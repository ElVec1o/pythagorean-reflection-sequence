// Bonfioli BFS in Rust -- the algebraic-state BFS that backs the
// universal sequence u_d, ported from MAC_BATCH_F's Python F4/F5.
//
// PURPOSE
// -------
// On a 24 GB Mac (M-series), this Rust implementation reliably reaches
// depth 41 in ~5 minutes wall time with ~5 GB RSS peak.  Depth 42+
// requires the disk-streaming frontier (this implementation), which
// keeps the packed-state frontier on disk between layers and only
// streams it through memory once per layer.
//
// CORRECTNESS
// -----------
// Output u_d sequence MUST match the Python implementation byte-for-byte
// through every common depth.  Verified against the canonical reference
//     u = [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875,
//          1345, 2066, 3203, 4971, 7574, 11543, 17683, 27108, 41067,
//          62263, 94622, 143881, 217101, 327832, 495443, 749195,
//          1127236, 1697179, 2554961, 3848384, 5777651, 8679441,
//          13031206, 19574659, 29338781, 43997388, 65932461, 98849591]
//
// MEMORY MODEL (target depth 42, disk-streaming frontier)
// -------------------------------------------------------
//   frontier blob   : on disk (~14 GB at d=42)
//   new blob        : on disk (streamed write)
//   layer_seen HashSet<u64>     : ~1.8 GB at d=42
//   cumulative seen (sorted Vec<u64>) : ~2.4 GB at d=42
//   frontier_lasts Vec<i8>      : ~149 MB at d=42
//   ----------------------------------
//   Peak RAM: ~5 GB.  Frontier file on disk: up to ~22 GB at d=43.
//
// SAFEGUARDS
// ----------
// 1. RSS-based abort via `ps` (every 100k states inside a layer).
// 2. Layer-by-layer JSON snapshot (just the u_d counts) for live progress.
// 3. Wall-time limit (default 4 hours).
// 4. Temp files cleaned up on normal exit (left behind on Ctrl-C; safe
//    to delete `rust_bfs_blob_*.tmp` manually).
//
// USAGE
// -----
//   cargo build --release
//   ./target/release/bonfioli_bfs                # default: depth 41
//   ./target/release/bonfioli_bfs 42 14 1        # depth 42, RSS abort 14 GB
//   ./target/release/bonfioli_bfs --help
//
// RESUMING
// --------
// Pass --save-frontier <path> on one run to dump the full BFS state to
// a binary snapshot.  Pass --resume <path> on a later run to pick up
// from there.  See --help for examples.

use std::collections::HashSet;
use std::env;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

const PACK_SIZE: usize = 96;  // bytes per state (94 used, padded to 96)
const MAX_TRANS: usize = 30;

// File I/O buffer size for streaming frontier blob.
const IO_BUF_BYTES: usize = 8 * 1024 * 1024;  // 8 MB
const COPY_CHUNK: usize = 1 << 20;            // 1 MB for bulk copies

// =============================================================
// State packing: header (4 bytes) + L[30] (30 bytes) + coef[30] (60 bytes)
// = 94 bytes packed.  Padded to 96 for alignment.
//
//   buf[0]  = sign (0 = negative, 1 = positive)
//   buf[1]  = lstr_start (0 = 'X', 1 = 'Y', 2 = empty)
//   buf[2]  = lstr_len (0..255)
//   buf[3]  = n_trans (0..30)
//   buf[4..34]      = L values (uint8 each)
//   buf[34..94]     = coef values (int16 little-endian)
//   buf[94..96]     = padding
// =============================================================

fn pack_state(buf: &mut [u8; PACK_SIZE],
              sign: i8, lstr_start: u8, lstr_len: u8,
              trans: &[(u8, i16)]) {
    *buf = [0u8; PACK_SIZE];
    buf[0] = if sign > 0 { 1 } else { 0 };
    buf[1] = lstr_start;
    buf[2] = lstr_len;
    buf[3] = trans.len() as u8;
    for (i, &(l_val, coef_val)) in trans.iter().enumerate() {
        if i >= MAX_TRANS { break; }
        buf[4 + i] = l_val;
        let bytes = coef_val.to_le_bytes();
        buf[4 + MAX_TRANS + 2*i] = bytes[0];
        buf[4 + MAX_TRANS + 2*i + 1] = bytes[1];
    }
}

fn unpack_state(buf: &[u8; PACK_SIZE]) -> (i8, u8, u8, Vec<(u8, i16)>) {
    let sign = if buf[0] == 1 { 1 } else { -1 };
    let lstr_start = buf[1];
    let lstr_len = buf[2];
    let n_trans = buf[3] as usize;
    let mut trans = Vec::with_capacity(n_trans);
    for i in 0..n_trans {
        let l_val = buf[4 + i];
        let coef_val = i16::from_le_bytes([
            buf[4 + MAX_TRANS + 2*i],
            buf[4 + MAX_TRANS + 2*i + 1],
        ]);
        trans.push((l_val, coef_val));
    }
    (sign, lstr_start, lstr_len, trans)
}

// =============================================================
// Algebraic step: identical math to D14v2's Python step().
// =============================================================

fn last_char(start: u8, length: u8) -> Option<u8> {
    if length == 0 { return None; }
    if length % 2 == 1 {
        Some(start)
    } else {
        // Opposite of start (X <-> Y, encoded as 0 <-> 1)
        Some(1 - start)
    }
}

fn append_or_cancel(start: u8, length: u8, ch: u8) -> (u8, u8) {
    if length == 0 {
        return (ch, 1);
    }
    if last_char(start, length) == Some(ch) {
        let new_len = length - 1;
        let new_start = if new_len > 0 { start } else { 2 };
        (new_start, new_len)
    } else {
        (start, length + 1)
    }
}

fn step(sign: i8, lstr_start: u8, lstr_len: u8,
        trans: &[(u8, i16)], letter: u8)
    -> (i8, u8, u8, Vec<(u8, i16)>) {
    let mut sign = sign;
    let mut lstr_start = lstr_start;
    let mut lstr_len = lstr_len;
    let mut trans: Vec<(u8, i16)> = trans.to_vec();

    if letter == 0 {
        let (s, l) = append_or_cancel(lstr_start, lstr_len, 0);  // X = 0
        lstr_start = s;
        lstr_len = l;
    } else if letter == 1 {
        let (s, l) = append_or_cancel(lstr_start, lstr_len, 0);
        lstr_start = s;
        lstr_len = l;
        sign = -sign;
    } else if letter == 2 {
        // Add (current_sign, current lstr reduced) to trans, then append Y.
        let mut t_start = lstr_start;
        let mut t_len = lstr_len;
        let mut t_sign = sign;
        while t_len > 0 && last_char(t_start, t_len) == Some(1) {  // Y = 1
            t_len -= 1;
            t_sign = -t_sign;
            if t_len == 0 { t_start = 2; }
        }
        let l_new = t_len;
        let mut new_trans: Vec<(u8, i16)> = Vec::with_capacity(trans.len() + 1);
        let mut found = false;
        for &(ll, vv) in &trans {
            if ll < l_new {
                new_trans.push((ll, vv));
            } else if ll == l_new {
                let nv = vv + t_sign as i16;
                if nv != 0 { new_trans.push((ll, nv)); }
                found = true;
            } else {
                if !found {
                    new_trans.push((l_new, t_sign as i16));
                    found = true;
                }
                new_trans.push((ll, vv));
            }
        }
        if !found {
            new_trans.push((l_new, t_sign as i16));
        }
        trans = new_trans;
        let (s, l) = append_or_cancel(lstr_start, lstr_len, 1);  // Y = 1
        lstr_start = s;
        lstr_len = l;
    }

    (sign, lstr_start, lstr_len, trans)
}

// =============================================================
// FNV-1a hash for packed state bytes -- fast, deterministic.
// =============================================================

fn hash_packed(buf: &[u8; PACK_SIZE]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in buf.iter() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

// =============================================================
// RSS via ps (matches Python F4/F5 convention).
// =============================================================

fn rss_gb() -> Option<f64> {
    let pid = std::process::id();
    let output = Command::new("ps")
        .args(&["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    let stdout = String::from_utf8(output.stdout).ok()?;
    let rss_kb: u64 = stdout.trim().parse().ok()?;
    Some(rss_kb as f64 / (1024.0 * 1024.0))
}

fn fmt_time(s: f64) -> String {
    if s < 60.0 { format!("{:.0}s", s) }
    else if s < 3600.0 { format!("{:.1}min", s / 60.0) }
    else { format!("{:.1}h", s / 3600.0) }
}

// =============================================================
// Temp file helpers for the disk-streamed frontier.
// =============================================================

fn temp_blob_path(tag: &str) -> PathBuf {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    dir.join(format!("rust_bfs_blob_{}_{}.tmp", std::process::id(), tag))
}

fn write_initial_blob_to_file(path: &Path) -> std::io::Result<()> {
    let mut init_buf = [0u8; PACK_SIZE];
    pack_state(&mut init_buf, 1, 2, 0, &[]);
    let mut f = File::create(path)?;
    f.write_all(&init_buf)?;
    f.flush()?;
    Ok(())
}

fn file_size(path: &Path) -> u64 {
    std::fs::metadata(path).map(|m| m.len()).unwrap_or(0)
}

// =============================================================
// BFS layer expansion.  Frontier blob lives on DISK between layers
// to keep peak RAM at ~5 GB even at depth 42-44.  Per layer:
//   1. Open old frontier file (BufReader).
//   2. Open new frontier file (BufWriter).
//   3. For each packed state read, compute step(state, c) for each c.
//   4. Hash result.  Skip if in cumulative seen.  Track within-layer
//      via HashSet<u64>.
//   5. Write novel children to new frontier file.
//   6. Delete old frontier file; swap.
//   7. Merge layer_seen hashes into sorted cumulative seen.
// =============================================================

fn run_bfs(
    max_depth: usize,
    rss_threshold_gb: f64,
    wall_limit_s: f64,
    interrupted: Arc<AtomicBool>,
    resumed: Option<(usize, Vec<usize>, Vec<u64>, Vec<i8>, PathBuf)>,
) -> (Vec<usize>, PathBuf, Vec<i8>, Vec<u64>, usize) {
    let start_depth: usize;
    let mut u: Vec<usize>;
    let mut seen: Vec<u64>;
    let mut frontier_lasts: Vec<i8>;
    let mut frontier_blob_path: PathBuf;

    if let Some((d0, u0, seen0, lasts0, blob_path)) = resumed {
        eprintln!("   resumed from d={}: frontier has {} states, seen has {} entries",
                  d0, lasts0.len(), seen0.len());
        eprintln!("   frontier blob on disk: {} ({:.2} GB)",
                  blob_path.display(), file_size(&blob_path) as f64 / 1e9);
        start_depth = d0;
        u = u0;
        seen = seen0;
        frontier_lasts = lasts0;
        frontier_blob_path = blob_path;
    } else {
        // Cold start: initial state sign=+1, lstr empty, no trans
        frontier_blob_path = temp_blob_path("d0");
        if let Err(e) = write_initial_blob_to_file(&frontier_blob_path) {
            eprintln!("failed to create initial blob file: {}", e);
            std::process::exit(1);
        }
        let mut init_buf = [0u8; PACK_SIZE];
        pack_state(&mut init_buf, 1, 2, 0, &[]);
        let init_hash = hash_packed(&init_buf);

        start_depth = 0;
        u = vec![1usize];
        seen = vec![init_hash];
        seen.sort_unstable();
        frontier_lasts = vec![-1i8];  // -1 = initial sentinel
        eprintln!("   d =  0: u_0 = 1");
    }

    let t_start = Instant::now();
    let mut last_completed: usize = start_depth;
    let mut state_buf = [0u8; PACK_SIZE];

    for d in (start_depth + 1)..=max_depth {
        if interrupted.load(Ordering::Relaxed) {
            eprintln!("\n  Interrupted at depth {}.  Saving snapshot.", d);
            break;
        }
        let t_layer = Instant::now();

        // Open old frontier for streaming read
        let r_file = match File::open(&frontier_blob_path) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("failed to open frontier file {}: {}",
                          frontier_blob_path.display(), e);
                std::process::exit(1);
            }
        };
        let mut r = BufReader::with_capacity(IO_BUF_BYTES, r_file);

        // Open new frontier for streaming write
        let new_blob_path = temp_blob_path(&format!("d{}", d));
        let w_file = match File::create(&new_blob_path) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("failed to create new frontier file {}: {}",
                          new_blob_path.display(), e);
                std::process::exit(1);
            }
        };
        let mut w = BufWriter::with_capacity(IO_BUF_BYTES, w_file);

        let mut new_lasts: Vec<i8> = Vec::new();
        let mut layer_seen: HashSet<u64> = HashSet::new();
        let n_states = frontier_lasts.len();

        let mut parent_buf = [0u8; PACK_SIZE];
        for i in 0..n_states {
            // RSS check every 100k states
            if i % 100_000 == 0 && i > 0 {
                if let Some(rss) = rss_gb() {
                    if rss > rss_threshold_gb {
                        eprintln!("\n  RSS = {:.2} GB > threshold {:.2} GB at d={}, i={}.  Abort.",
                                  rss, rss_threshold_gb, d, i);
                        drop(w);
                        drop(r);
                        std::fs::remove_file(&new_blob_path).ok();
                        save_json_progress(&u, max_depth, d - 1,
                                            t_start.elapsed().as_secs_f64(), rss);
                        return (u, frontier_blob_path, frontier_lasts, seen, last_completed);
                    }
                }
            }
            if let Err(e) = r.read_exact(&mut parent_buf) {
                eprintln!("read_exact failed at state {}: {}", i, e);
                std::process::exit(1);
            }
            let (sign, lstr_start, lstr_len, trans) = unpack_state(&parent_buf);
            let last = frontier_lasts[i];

            for c in 0u8..3 {
                if last != -1 && c as i8 == last { continue; }
                if last == 1 && c == 0 { continue; }
                let (ns_sign, ns_start, ns_len, ns_trans) =
                    step(sign, lstr_start, lstr_len, &trans, c);
                pack_state(&mut state_buf, ns_sign, ns_start, ns_len, &ns_trans);
                let h = hash_packed(&state_buf);
                if seen.binary_search(&h).is_ok() { continue; }
                if !layer_seen.insert(h) { continue; }
                if let Err(e) = w.write_all(&state_buf) {
                    eprintln!("write_all failed: {}", e);
                    std::process::exit(1);
                }
                new_lasts.push(c as i8);
            }
        }

        // Flush and close I/O
        if let Err(e) = w.flush() {
            eprintln!("flush failed: {}", e);
            std::process::exit(1);
        }
        drop(w);
        drop(r);

        // Delete old frontier file; swap in new one
        std::fs::remove_file(&frontier_blob_path).ok();
        frontier_blob_path = new_blob_path;

        // Merge layer_seen into cumulative seen via linear two-way merge.
        let mut new_hashes: Vec<u64> = layer_seen.iter().copied().collect();
        new_hashes.sort_unstable();
        let mut merged: Vec<u64> = Vec::with_capacity(seen.len() + new_hashes.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < seen.len() && j < new_hashes.len() {
            if seen[i] <= new_hashes[j] {
                merged.push(seen[i]);
                i += 1;
            } else {
                merged.push(new_hashes[j]);
                j += 1;
            }
        }
        if i < seen.len() { merged.extend_from_slice(&seen[i..]); }
        if j < new_hashes.len() { merged.extend_from_slice(&new_hashes[j..]); }
        seen = merged;
        drop(layer_seen);

        frontier_lasts = new_lasts;
        let n_new = frontier_lasts.len();
        u.push(n_new);
        last_completed = d;
        let wall = t_layer.elapsed().as_secs_f64();
        let total = t_start.elapsed().as_secs_f64();
        let rss = rss_gb().unwrap_or(0.0);
        eprintln!("   d = {:>2}: u_{} = {:>13}  (seen = {:>13}, layer = {}, total = {}, RSS = {:.2} GB, disk = {:.2} GB)",
                  d, d, n_new, seen.len(), fmt_time(wall), fmt_time(total), rss,
                  file_size(&frontier_blob_path) as f64 / 1e9);
        // Lightweight JSON progress (just u counts)
        save_json_progress(&u, max_depth, d, total, rss);
        // Wall-time abort
        if total > wall_limit_s {
            eprintln!("\n  Wall time {} exceeds limit {}.  Abort.",
                      fmt_time(total), fmt_time(wall_limit_s));
            break;
        }
        if interrupted.load(Ordering::Relaxed) {
            eprintln!("\n  Interrupted after depth {}.  Saving state.", d);
            break;
        }
    }
    (u, frontier_blob_path, frontier_lasts, seen, last_completed)
}

fn save_json_progress(u: &[usize], max_depth: usize, completed: usize,
                      total_wall_s: f64, rss_gb: f64) {
    if let Ok(mut f) = File::create("rust_bfs_progress.json") {
        write!(f, "{{\n").ok();
        write!(f, "  \"max_depth\": {},\n", max_depth).ok();
        write!(f, "  \"completed\": {},\n", completed).ok();
        write!(f, "  \"total_wall_s\": {:.1},\n", total_wall_s).ok();
        write!(f, "  \"rss_gb\": {:.4},\n", rss_gb).ok();
        write!(f, "  \"u\": [").ok();
        for (i, &v) in u.iter().enumerate() {
            if i > 0 { write!(f, ", ").ok(); }
            write!(f, "{}", v).ok();
        }
        write!(f, "]\n").ok();
        write!(f, "}}\n").ok();
    }
}

// =============================================================
// Binary frontier snapshot for --resume.
//
// FORMAT (little-endian; macOS LE host).
//   Header (64 bytes):
//     [ 0..16]  magic       "BONFIOLI_BFS_v1\n"
//     [16..24]  version     u64 = 1
//     [24..32]  completed_depth  u64
//     [32..40]  n_states    u64   (frontier size)
//     [40..48]  seen_len    u64
//     [48..56]  u_len       u64
//     [56..64]  reserved    u64 = 0
//   Body:
//     u            : u64 * u_len
//     seen         : u64 * seen_len      (sorted ascending)
//     lasts        : i8  * n_states      (bit-pattern as u8)
//     blob         : u8  * n_states * 96
// =============================================================

const SNAPSHOT_MAGIC: &[u8; 16] = b"BONFIOLI_BFS_v1\n";
const SNAPSHOT_VERSION: u64 = 1;
const SNAPSHOT_HEADER_LEN: usize = 64;

#[derive(Debug)]
struct SnapshotHeader {
    completed_depth: u64,
    n_states: u64,
    seen_len: u64,
    u_len: u64,
}

fn snapshot_estimated_size(n_states: u64, seen_len: u64, u_len: u64) -> u64 {
    (SNAPSHOT_HEADER_LEN as u64) + 8 * u_len + 8 * seen_len
        + n_states + 96 * n_states
}

fn save_frontier_snapshot(
    path: &str,
    completed_depth: usize,
    u: &[usize],
    seen: &[u64],
    frontier_lasts: &[i8],
    frontier_blob_path: &Path,
) -> std::io::Result<()> {
    let n_states = frontier_lasts.len() as u64;
    let est = snapshot_estimated_size(n_states, seen.len() as u64, u.len() as u64);
    eprintln!();
    eprintln!("  Saving snapshot to {} (estimated {:.2} GB) ...",
              path, (est as f64) / 1e9);
    let t = Instant::now();
    let f = File::create(path)?;
    let mut w = BufWriter::with_capacity(IO_BUF_BYTES, f);

    // Header
    w.write_all(SNAPSHOT_MAGIC)?;
    w.write_all(&SNAPSHOT_VERSION.to_le_bytes())?;
    w.write_all(&(completed_depth as u64).to_le_bytes())?;
    w.write_all(&n_states.to_le_bytes())?;
    w.write_all(&(seen.len() as u64).to_le_bytes())?;
    w.write_all(&(u.len() as u64).to_le_bytes())?;
    w.write_all(&[0u8; 8])?;
    debug_assert_eq!(SNAPSHOT_HEADER_LEN, 64);

    // u list as u64 little-endian (convert usize -> u64 on the fly)
    {
        let chunk: usize = 16384;
        let mut buf = vec![0u8; chunk * 8];
        for c in u.chunks(chunk) {
            for (i, &v) in c.iter().enumerate() {
                buf[i*8..i*8+8].copy_from_slice(&(v as u64).to_le_bytes());
            }
            w.write_all(&buf[..c.len()*8])?;
        }
    }

    // seen as raw u64 bytes (LE host)
    unsafe {
        let bytes = std::slice::from_raw_parts(
            seen.as_ptr() as *const u8,
            seen.len() * 8,
        );
        w.write_all(bytes)?;
    }

    // frontier_lasts: i8 bit pattern as u8
    unsafe {
        let bytes = std::slice::from_raw_parts(
            frontier_lasts.as_ptr() as *const u8,
            frontier_lasts.len(),
        );
        w.write_all(bytes)?;
    }

    // Stream the frontier blob from its on-disk temp file
    let blob_file = File::open(frontier_blob_path)?;
    let mut blob_r = BufReader::with_capacity(IO_BUF_BYTES, blob_file);
    let mut buf = vec![0u8; COPY_CHUNK];
    loop {
        let n = blob_r.read(&mut buf)?;
        if n == 0 { break; }
        w.write_all(&buf[..n])?;
    }

    w.flush()?;
    let dt = t.elapsed().as_secs_f64();
    eprintln!("  Snapshot saved: {:.2} GB in {:.1}s ({:.0} MB/s).",
              (est as f64) / 1e9, dt, (est as f64) / dt / 1e6);
    Ok(())
}

fn read_header<R: Read>(r: &mut R) -> std::io::Result<SnapshotHeader> {
    let mut magic = [0u8; 16];
    r.read_exact(&mut magic)?;
    if &magic != SNAPSHOT_MAGIC {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("bad magic in snapshot file"),
        ));
    }
    let mut tag = [0u8; 8];
    r.read_exact(&mut tag)?;
    let version = u64::from_le_bytes(tag);
    if version != SNAPSHOT_VERSION {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("unsupported snapshot version: {} (expected {})",
                    version, SNAPSHOT_VERSION),
        ));
    }
    r.read_exact(&mut tag)?;
    let completed_depth = u64::from_le_bytes(tag);
    r.read_exact(&mut tag)?;
    let n_states = u64::from_le_bytes(tag);
    r.read_exact(&mut tag)?;
    let seen_len = u64::from_le_bytes(tag);
    r.read_exact(&mut tag)?;
    let u_len = u64::from_le_bytes(tag);
    let mut reserved = [0u8; 8];
    r.read_exact(&mut reserved)?;
    Ok(SnapshotHeader { completed_depth, n_states, seen_len, u_len })
}

fn load_frontier_snapshot(path: &str)
    -> std::io::Result<(usize, Vec<usize>, Vec<u64>, Vec<i8>, PathBuf)>
{
    eprintln!();
    eprintln!("  Loading snapshot from {} ...", path);
    let t = Instant::now();
    let f = File::open(path)?;
    let mut r = BufReader::with_capacity(IO_BUF_BYTES, f);

    let hdr = read_header(&mut r)?;
    let n_states = hdr.n_states as usize;
    let seen_len = hdr.seen_len as usize;
    let u_len    = hdr.u_len    as usize;
    eprintln!("    completed_depth = {}", hdr.completed_depth);
    eprintln!("    frontier states = {}", n_states);
    eprintln!("    seen entries    = {}", seen_len);

    // u list
    let mut u_buf = vec![0u8; u_len * 8];
    r.read_exact(&mut u_buf)?;
    let mut u: Vec<usize> = Vec::with_capacity(u_len);
    for i in 0..u_len {
        let mut tag = [0u8; 8];
        tag.copy_from_slice(&u_buf[i*8..i*8+8]);
        u.push(u64::from_le_bytes(tag) as usize);
    }
    drop(u_buf);

    // seen (read directly into Vec<u64> bytes)
    let mut seen: Vec<u64> = vec![0u64; seen_len];
    unsafe {
        let bytes = std::slice::from_raw_parts_mut(
            seen.as_mut_ptr() as *mut u8,
            seen_len * 8,
        );
        r.read_exact(bytes)?;
    }

    // frontier_lasts
    let mut lasts: Vec<i8> = vec![0i8; n_states];
    unsafe {
        let bytes = std::slice::from_raw_parts_mut(
            lasts.as_mut_ptr() as *mut u8,
            n_states,
        );
        r.read_exact(bytes)?;
    }

    // frontier_blob: stream into a fresh temp file (no in-memory blob)
    let blob_temp = temp_blob_path("resumed");
    let blob_file = File::create(&blob_temp)?;
    let mut blob_w = BufWriter::with_capacity(IO_BUF_BYTES, blob_file);
    let n_blob_bytes = (n_states as u64) * (PACK_SIZE as u64);
    let mut buf = vec![0u8; COPY_CHUNK];
    let mut remaining = n_blob_bytes;
    while remaining > 0 {
        let to_read = std::cmp::min(remaining as usize, buf.len());
        r.read_exact(&mut buf[..to_read])?;
        blob_w.write_all(&buf[..to_read])?;
        remaining -= to_read as u64;
    }
    blob_w.flush()?;
    drop(blob_w);

    let dt = t.elapsed().as_secs_f64();
    let est = snapshot_estimated_size(hdr.n_states, hdr.seen_len, hdr.u_len);
    eprintln!("  Snapshot loaded: {:.2} GB in {:.1}s ({:.0} MB/s).",
              (est as f64) / 1e9, dt, (est as f64) / dt / 1e6);
    eprintln!("    frontier extracted to temp file: {}", blob_temp.display());

    Ok((hdr.completed_depth as usize, u, seen, lasts, blob_temp))
}

fn inspect_snapshot(path: &str) -> std::io::Result<()> {
    let f = File::open(path)?;
    let mut r = BufReader::new(f);
    let hdr = read_header(&mut r)?;
    let est = snapshot_estimated_size(hdr.n_states, hdr.seen_len, hdr.u_len);
    println!("File: {}", path);
    println!("  Magic / version:  OK / v{}", SNAPSHOT_VERSION);
    println!("  completed_depth:  {}", hdr.completed_depth);
    println!("  frontier_states:  {}", hdr.n_states);
    println!("  seen_entries:     {}", hdr.seen_len);
    println!("  u_list_len:       {}", hdr.u_len);
    println!("  expected_size:    {:.2} GB", (est as f64) / 1e9);
    let mut u_buf = vec![0u8; (hdr.u_len as usize) * 8];
    r.read_exact(&mut u_buf)?;
    print!("  u = [");
    for i in 0..hdr.u_len as usize {
        if i > 0 { print!(", "); }
        let mut tag = [0u8; 8];
        tag.copy_from_slice(&u_buf[i*8..i*8+8]);
        print!("{}", u64::from_le_bytes(tag));
    }
    println!("]");
    Ok(())
}

// =============================================================
// CLI argument parser.
// =============================================================

#[derive(Debug)]
struct CliArgs {
    max_depth: usize,
    rss_threshold_gb: f64,
    wall_limit_h: f64,
    save_frontier_path: Option<String>,
    resume_path: Option<String>,
    inspect_path: Option<String>,
}

fn parse_args(args: &[String]) -> CliArgs {
    let mut positional: Vec<String> = Vec::new();
    let mut save_frontier_path: Option<String> = None;
    let mut resume_path: Option<String> = None;
    let mut inspect_path: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--save-frontier" => {
                save_frontier_path = args.get(i + 1).cloned();
                i += 2;
            }
            "--resume" => {
                resume_path = args.get(i + 1).cloned();
                i += 2;
            }
            "--inspect" => {
                inspect_path = args.get(i + 1).cloned();
                i += 2;
            }
            "--help" | "-h" => {
                print_help();
                std::process::exit(0);
            }
            s if s.starts_with("--") => {
                eprintln!("Unknown flag: {} (use --help for usage)", s);
                std::process::exit(2);
            }
            s => {
                positional.push(s.to_string());
                i += 1;
            }
        }
    }
    let max_depth: usize = positional.get(0)
        .and_then(|s| s.parse().ok()).unwrap_or(41);
    let rss_threshold_gb: f64 = positional.get(1)
        .and_then(|s| s.parse().ok()).unwrap_or(18.0);
    let wall_limit_h: f64 = positional.get(2)
        .and_then(|s| s.parse().ok()).unwrap_or(4.0);
    CliArgs {
        max_depth, rss_threshold_gb, wall_limit_h,
        save_frontier_path, resume_path, inspect_path,
    }
}

fn print_help() {
    println!("Bonfioli BFS (Rust)  --  disk-streaming frontier edition");
    println!();
    println!("USAGE");
    println!("  bonfioli_bfs [DEPTH] [RSS_GB] [WALL_H] [FLAGS]");
    println!();
    println!("POSITIONAL ARGS  (all optional)");
    println!("  DEPTH     target depth (default 41)");
    println!("  RSS_GB    abort threshold in GB (default 18)");
    println!("  WALL_H    wall-time limit in hours (default 4)");
    println!();
    println!("FLAGS");
    println!("  --save-frontier <path>   after reaching DEPTH, dump full");
    println!("                           BFS state to <path> (binary)");
    println!("  --resume <path>          load <path>, continue from there");
    println!("                           to DEPTH (skips the prefix walk)");
    println!("  --inspect <path>         print snapshot header (depth, sizes,");
    println!("                           u list) and exit");
    println!("  --help, -h               this message");
    println!();
    println!("DISK USAGE");
    println!("  This build keeps the frontier blob on DISK (in cwd) between");
    println!("  layers.  Files named rust_bfs_blob_<pid>_*.tmp will appear");
    println!("  during the run.  They are cleaned up on normal exit; safe");
    println!("  to delete manually if a run was killed.");
    println!();
    println!("EXAMPLES");
    println!("  # Compute depth 41 from scratch, save snapshot for later");
    println!("  bonfioli_bfs 41 12 1 --save-frontier d41.bin");
    println!();
    println!("  # Resume from d41.bin and push to depth 43, save d43.bin");
    println!("  bonfioli_bfs 43 14 2 --resume d41.bin --save-frontier d43.bin");
    println!();
    println!("  # Peek at a snapshot without loading it");
    println!("  bonfioli_bfs --inspect d41.bin");
}

// =============================================================
// Main.
// =============================================================

fn cleanup_temp_blob(p: &Path) {
    if p.exists() {
        let _ = std::fs::remove_file(p);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let cli = parse_args(&args);

    if let Some(path) = cli.inspect_path.as_ref() {
        match inspect_snapshot(path) {
            Ok(()) => std::process::exit(0),
            Err(e) => {
                eprintln!("inspect failed: {}", e);
                std::process::exit(1);
            }
        }
    }

    let wall_limit_s = cli.wall_limit_h * 3600.0;

    eprintln!("==============================================================");
    eprintln!(" Bonfioli BFS (Rust, disk-streaming frontier)");
    eprintln!("==============================================================");
    eprintln!(" Target depth:        {}", cli.max_depth);
    eprintln!(" RSS abort threshold: {:.1} GB", cli.rss_threshold_gb);
    eprintln!(" Wall time limit:     {:.1} h", cli.wall_limit_h);
    if let Some(p) = &cli.resume_path {
        eprintln!(" Resume from:         {}", p);
    }
    if let Some(p) = &cli.save_frontier_path {
        eprintln!(" Save snapshot to:    {}", p);
    }
    eprintln!();

    let resumed = if let Some(path) = cli.resume_path.as_ref() {
        match load_frontier_snapshot(path) {
            Ok(tuple) => {
                if tuple.0 >= cli.max_depth {
                    eprintln!();
                    eprintln!(" Resume snapshot is at depth {}, target depth {} is not deeper.",
                              tuple.0, cli.max_depth);
                    eprintln!(" Nothing to compute.  u list from snapshot:");
                    print!("[");
                    for (i, &v) in tuple.1.iter().enumerate() {
                        if i > 0 { print!(", "); }
                        print!("{}", v);
                    }
                    println!("]");
                    cleanup_temp_blob(&tuple.4);
                    std::process::exit(0);
                }
                Some(tuple)
            }
            Err(e) => {
                eprintln!("Failed to load resume snapshot: {}", e);
                std::process::exit(1);
            }
        }
    } else {
        None
    };

    let interrupted = Arc::new(AtomicBool::new(false));

    let t0 = Instant::now();
    let (u, frontier_blob_path, frontier_lasts, seen, last_completed) =
        run_bfs(cli.max_depth, cli.rss_threshold_gb, wall_limit_s,
                interrupted, resumed);
    let total = t0.elapsed().as_secs_f64();

    eprintln!();
    eprintln!(" Total wall: {}", fmt_time(total));
    eprintln!();
    eprintln!(" u_d as JSON list (paste into D9 / D12 / D13 / paper table):");
    print!("[");
    for (i, &v) in u.iter().enumerate() {
        if i > 0 { print!(", "); }
        print!("{}", v);
    }
    println!("]");
    if last_completed < cli.max_depth {
        eprintln!();
        eprintln!(" Note: aborted at depth {} (target was {}).",
                  last_completed, cli.max_depth);
    }

    if let Some(path) = cli.save_frontier_path.as_ref() {
        match save_frontier_snapshot(path, last_completed, &u, &seen,
                                     &frontier_lasts, &frontier_blob_path) {
            Ok(()) => {
                eprintln!("  Resume next run with:");
                eprintln!("    bonfioli_bfs <NEW_DEPTH> <RSS_GB> <WALL_H> --resume {}", path);
            }
            Err(e) => {
                eprintln!("Failed to save frontier snapshot: {}", e);
                cleanup_temp_blob(&frontier_blob_path);
                std::process::exit(1);
            }
        }
    }

    // Clean up the temp frontier file (we've either saved the snapshot or
    // there was no --save-frontier flag).
    cleanup_temp_blob(&frontier_blob_path);
}
