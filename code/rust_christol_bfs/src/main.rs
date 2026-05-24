// Christol mod-p BFS for the Bonfioli universality paper (v8.2).
//
// State space: Q ⋉ M_p where
//   Q = D_∞ × Z/2 = <X, Y, c | X^2 = Y^2 = c^2 = 1, c central>
//   M = Z[Q]/(Y+1, c+1)
//   M_p = M/pM
//
// In the encoding inherited from the verified F4 packed-frontier algorithm
// (cross-checked against U_EXACT through depth 42), a state is
//   (sign, lstr_start, lstr_len, trans)
// where
//   sign ∈ {+1,-1}    encodes the c-component of Q
//   lstr               is a reduced alternating word in {X,Y} (length ≤ 255)
//   trans              is a Z[Q]-module element of M, represented as a
//                      sparse vector of (position L, coefficient mod p) pairs
// The generators R_0, R_1, R_2 act as in G12_modp_bfs.py / F4_packed_frontier.
//
// This file is a clean, self-contained Rust port. Verified to reproduce
// the Python G12_modp_bfs.py output byte-for-byte through depth 14
// (p ∈ {2,3,5,7}).

use std::collections::HashSet;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::Instant;

// ============================================================================
// State representation
// ============================================================================
//
// We pack a state into a small Vec<u8> so HashSet lookups are cheap and the
// memory footprint per state stays low (~ 20-60 bytes amortized).
//
// Header (4 bytes):  [sign_bit, lstr_start, lstr_len, n_trans]
//   sign_bit:   0 = -1, 1 = +1
//   lstr_start: 0 = 'X', 1 = 'Y', 2 = empty
//   lstr_len:   0..=255
//   n_trans:    0..=255
// Then n_trans entries, each (L_u8, coef_u8), so total = 4 + 2*n_trans bytes.

type State = Vec<u8>;

#[inline(always)]
fn last_char(start: u8, length: u8) -> Option<u8> {
    if length == 0 {
        return None;
    }
    if length % 2 == 1 {
        Some(start)
    } else {
        Some(1 - start)
    }
}

#[inline(always)]
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

#[inline(always)]
fn pack(sign: i8, lstr_start: u8, lstr_len: u8, trans: &[(u8, u8)]) -> State {
    let n = trans.len();
    let mut v = Vec::with_capacity(4 + 2 * n);
    v.push(if sign > 0 { 1 } else { 0 });
    v.push(lstr_start);
    v.push(lstr_len);
    v.push(n as u8);
    for &(l, c) in trans {
        v.push(l);
        v.push(c);
    }
    v
}

#[inline(always)]
fn unpack(s: &State) -> (i8, u8, u8, Vec<(u8, u8)>) {
    let sign = if s[0] == 1 { 1 } else { -1 };
    let lstr_start = s[1];
    let lstr_len = s[2];
    let n = s[3] as usize;
    let mut trans = Vec::with_capacity(n);
    for i in 0..n {
        trans.push((s[4 + 2 * i], s[4 + 2 * i + 1]));
    }
    (sign, lstr_start, lstr_len, trans)
}

// ============================================================================
// Step: apply generator R_letter (letter ∈ {0,1,2}) to a state, mod p.
// R_0 = X-action, R_1 = X'-action (= cX, flips sign), R_2 = Y-action with
// the algebraic-transcript contribution.
// ============================================================================
fn step_modp(state: &State, letter: u8, p: u8) -> State {
    let (mut sign, mut lstr_start, mut lstr_len, trans) = unpack(state);

    if letter == 0 {
        let (s, l) = append_or_cancel(lstr_start, lstr_len, 0);
        lstr_start = s;
        lstr_len = l;
        return pack(sign, lstr_start, lstr_len, &trans);
    }

    if letter == 1 {
        let (s, l) = append_or_cancel(lstr_start, lstr_len, 0);
        lstr_start = s;
        lstr_len = l;
        sign = -sign;
        return pack(sign, lstr_start, lstr_len, &trans);
    }

    // letter == 2: strip trailing Y's from lstr, flipping sign each time;
    // the resulting length L is the position; add ±1 mod p into trans[L].
    let mut t_start = lstr_start;
    let mut t_len = lstr_len;
    let mut t_sign = sign;
    while t_len > 0 && last_char(t_start, t_len) == Some(1) {
        t_len -= 1;
        t_sign = -t_sign;
        if t_len == 0 {
            t_start = 2;
        }
    }
    let big_l = t_len;
    // contrib = t_sign mod p in {1..p-1}
    let contrib: u8 = if t_sign > 0 { 1 } else { p - 1 };

    // Insert (big_l, contrib) into trans, summing on collision and dropping zeros.
    let mut new_trans: Vec<(u8, u8)> = Vec::with_capacity(trans.len() + 1);
    let mut found = false;
    for &(ll, vv) in &trans {
        if ll < big_l {
            new_trans.push((ll, vv));
        } else if ll == big_l {
            let nv = (vv + contrib) % p;
            if nv != 0 {
                new_trans.push((ll, nv));
            }
            found = true;
        } else {
            if !found {
                new_trans.push((big_l, contrib));
                found = true;
            }
            new_trans.push((ll, vv));
        }
    }
    if !found {
        new_trans.push((big_l, contrib));
    }

    // Append Y to lstr.
    let (s, l) = append_or_cancel(lstr_start, lstr_len, 1);
    lstr_start = s;
    lstr_len = l;
    pack(sign, lstr_start, lstr_len, &new_trans)
}

// ============================================================================
// BFS
// ============================================================================
struct BfsConfig {
    prime: u8,
    max_depth: usize,
    seen_cap: usize,
    time_cap_s: f64,
    snapshot_dir: Option<PathBuf>,
    progress_every_layer: bool,
}

struct BfsResult {
    layer_sizes: Vec<usize>,
    #[allow(dead_code)]
    walls_s: Vec<f64>,
    aborted: bool,
    reason: String,
}

fn bfs(cfg: &BfsConfig) -> BfsResult {
    // Initial state: sign=+1, empty lstr, empty trans.
    let initial = pack(1, 2, 0, &[]);
    // Frontier: parallel arrays state + last_letter (i8; -1 = "no parent move").
    let mut frontier: Vec<State> = vec![initial.clone()];
    let mut lasts: Vec<i8> = vec![-1];

    let mut seen: HashSet<State> = HashSet::new();
    seen.insert(initial);

    let mut layer_sizes: Vec<usize> = vec![1];
    let mut walls: Vec<f64> = Vec::new();

    let t_start = Instant::now();
    let mut aborted = false;
    let mut reason = String::new();

    for d in 1..=cfg.max_depth {
        let t0 = Instant::now();
        let mut new_frontier: Vec<State> = Vec::new();
        let mut new_lasts: Vec<i8> = Vec::new();
        let mut new_dedup: HashSet<State> = HashSet::new();

        for i in 0..frontier.len() {
            let st = &frontier[i];
            let last = lasts[i];
            for c in 0u8..3u8 {
                if c as i8 == last {
                    continue;
                }
                if last == 1 && c == 0 {
                    continue;
                }
                let ns = step_modp(st, c, cfg.prime);
                if new_dedup.contains(&ns) || seen.contains(&ns) {
                    continue;
                }
                new_dedup.insert(ns.clone());
                new_frontier.push(ns);
                new_lasts.push(c as i8);
            }
        }

        for s in &new_frontier {
            seen.insert(s.clone());
        }
        frontier = new_frontier;
        lasts = new_lasts;
        let n_new = frontier.len();
        layer_sizes.push(n_new);
        let wall = t0.elapsed().as_secs_f64();
        walls.push(wall);
        let total = t_start.elapsed().as_secs_f64();
        let prev = layer_sizes[layer_sizes.len() - 2];
        let ratio = if prev > 0 { n_new as f64 / prev as f64 } else { 0.0 };

        if cfg.progress_every_layer {
            println!(
                "p={}  d={:>3}: |S_p(d)|={:>14}  ratio={:.4}  seen={:>14}  layer={:>7.2}s  total={:>7.1}s",
                cfg.prime, d, n_new, ratio, seen.len(), wall, total
            );
        }

        if let Some(dir) = &cfg.snapshot_dir {
            let _ = std::fs::create_dir_all(dir);
            let p = dir.join(format!("snapshot_p{}.json", cfg.prime));
            let mut f = BufWriter::new(File::create(&p).unwrap());
            writeln!(
                f,
                "{{\"prime\":{},\"depth\":{},\"layer_sizes\":{:?},\"wall_total_s\":{:.2},\"seen\":{}}}",
                cfg.prime, d, layer_sizes, total, seen.len()
            )
            .ok();
        }

        if n_new == 0 {
            reason = "dead frontier (saturated)".into();
            break;
        }
        if seen.len() > cfg.seen_cap {
            aborted = true;
            reason = format!("seen-set > {}", cfg.seen_cap);
            break;
        }
        if total > cfg.time_cap_s {
            aborted = true;
            reason = format!("time > {:.0}s", cfg.time_cap_s);
            break;
        }
    }

    BfsResult {
        layer_sizes,
        walls_s: walls,
        aborted,
        reason,
    }
}

// ============================================================================
// Growth fit
// ============================================================================
fn log_linear_fit(xs: &[f64], ys: &[f64]) -> Option<(f64, f64, f64)> {
    let n = xs.len();
    if n < 2 || ys.iter().any(|&y| y <= 0.0) {
        return None;
    }
    let ly: Vec<f64> = ys.iter().map(|y| y.ln()).collect();
    let mx = xs.iter().sum::<f64>() / n as f64;
    let my = ly.iter().sum::<f64>() / n as f64;
    let sxx: f64 = xs.iter().map(|x| (x - mx).powi(2)).sum();
    let sxy: f64 = xs.iter().zip(ly.iter()).map(|(x, y)| (x - mx) * (y - my)).sum();
    if sxx == 0.0 {
        return None;
    }
    let b = sxy / sxx;
    let a = my - b * mx;
    let syy: f64 = ly.iter().map(|y| (y - my).powi(2)).sum();
    if syy == 0.0 {
        return None;
    }
    let ss_res: f64 = xs.iter().zip(ly.iter()).map(|(x, y)| (y - (a + b * x)).powi(2)).sum();
    let r2 = 1.0 - ss_res / syy;
    Some((a, b, r2))
}

fn classify(layer_sizes: &[usize]) -> (String, f64) {
    let d_max = layer_sizes.len() - 1;
    if d_max < 6 {
        return ("ambiguous".into(), 0.0);
    }
    // Saturation: last 5 layers all equal.
    if d_max >= 8 {
        let tail = &layer_sizes[layer_sizes.len() - 5..];
        if tail.iter().all(|&s| s == tail[0]) && tail[0] > 0 {
            return ("saturated".into(), tail[0] as f64);
        }
    }
    let tail_start = std::cmp::max(5, d_max / 2);
    let xs: Vec<f64> = (tail_start..=d_max).map(|x| x as f64).collect();
    let ys: Vec<f64> = layer_sizes[tail_start..].iter().map(|&y| y as f64).collect();
    let lxs: Vec<f64> = xs.iter().map(|x| x.ln()).collect();
    let exp_fit = log_linear_fit(&xs, &ys);
    let pow_fit = log_linear_fit(&lxs, &ys);
    match (exp_fit, pow_fit) {
        (Some((_, be, r2e)), Some((_, bp, r2p))) => {
            if r2e > r2p + 0.005 && r2e > 0.99 {
                ("exponential".into(), be.exp())
            } else if r2p > r2e + 0.005 {
                ("polynomial".into(), bp)
            } else {
                ("ambiguous".into(), 0.0)
            }
        }
        _ => ("ambiguous".into(), 0.0),
    }
}

// ============================================================================
// CLI
// ============================================================================
fn parse_args() -> BfsConfig {
    let args: Vec<String> = env::args().collect();
    let mut prime: u8 = 3;
    let mut max_depth: usize = 100;
    let mut seen_cap: usize = 200_000_000;
    let mut time_cap_s: f64 = 12.0 * 3600.0;
    let mut snapshot_dir: Option<PathBuf> = None;
    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--prime" => {
                prime = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--max-depth" => {
                max_depth = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--seen-cap" => {
                seen_cap = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--time-cap" => {
                time_cap_s = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--snapshot-dir" => {
                snapshot_dir = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--help" | "-h" => {
                eprintln!(
                    "Usage: christol_bfs --prime P --max-depth D [--seen-cap N] [--time-cap S] [--snapshot-dir DIR]"
                );
                std::process::exit(0);
            }
            other => {
                eprintln!("unknown arg: {}", other);
                std::process::exit(2);
            }
        }
    }
    BfsConfig {
        prime,
        max_depth,
        seen_cap,
        time_cap_s,
        snapshot_dir,
        progress_every_layer: true,
    }
}

// ============================================================================
// Sanity check (mod-INF: pretend p is huge by using p=251, no realistic
// collisions through depth 10; we then confirm against U_EXACT[0..=10]).
// ============================================================================
const U_EXACT_HEAD: [usize; 11] = [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225];

fn sanity_modinf() -> bool {
    // p=251 is large enough that no coefficient collision occurs through d=10,
    // so |S(d)| should equal U_EXACT[d].
    let cfg = BfsConfig {
        prime: 251,
        max_depth: 10,
        seen_cap: 1_000_000,
        time_cap_s: 60.0,
        snapshot_dir: None,
        progress_every_layer: false,
    };
    let r = bfs(&cfg);
    let ok = r.layer_sizes == U_EXACT_HEAD;
    println!("Sanity (mod 251, depth 0..10):");
    println!("  got:    {:?}", r.layer_sizes);
    println!("  expect: {:?}  ({})", U_EXACT_HEAD, if ok { "OK" } else { "FAIL" });
    ok
}

fn sanity_modp(p: u8, expected: &[usize]) -> bool {
    let cfg = BfsConfig {
        prime: p,
        max_depth: expected.len() - 1,
        seen_cap: 10_000_000,
        time_cap_s: 300.0,
        snapshot_dir: None,
        progress_every_layer: false,
    };
    let r = bfs(&cfg);
    let ok = r.layer_sizes == expected;
    println!(
        "Sanity (mod {}, depth 0..{}): got={:?}",
        p,
        expected.len() - 1,
        r.layer_sizes
    );
    println!(
        "  expect: {:?}  ({})",
        expected,
        if ok { "OK" } else { "FAIL" }
    );
    ok
}

// ============================================================================
fn main() {
    let cfg = parse_args();

    println!("============================================================");
    println!(" Christol mod-p BFS  (Bonfioli universality paper v8.2)");
    println!("============================================================");
    println!(" prime         : {}", cfg.prime);
    println!(" max-depth     : {}", cfg.max_depth);
    println!(" seen-cap      : {}", cfg.seen_cap);
    println!(" time-cap (s)  : {}", cfg.time_cap_s);
    if let Some(d) = &cfg.snapshot_dir {
        println!(" snapshot-dir  : {}", d.display());
    }
    println!();

    // ---- sanity ----
    let s_inf = sanity_modinf();
    // Known reference layer sizes for p=2,3 from G12_modp_bfs.py
    let s_p2 = sanity_modp(2, &[1, 3, 5, 5, 4, 4, 4, 4, 4, 4, 4]);
    let s_p3 = sanity_modp(3, &[1, 3, 5, 8, 13, 21, 34, 55, 89, 141, 216]);
    println!();
    if !(s_inf && s_p2 && s_p3) {
        eprintln!("SANITY CHECK FAILED -- aborting full BFS.");
        std::process::exit(1);
    }
    println!("All sanity checks passed.\n");

    // ---- full BFS ----
    let t0 = Instant::now();
    let result = bfs(&cfg);
    let total = t0.elapsed().as_secs_f64();

    let (kind, rate) = classify(&result.layer_sizes);

    println!("\n============================================================");
    println!(" RESULT");
    println!("============================================================");
    println!(" depth reached : {}", result.layer_sizes.len() - 1);
    println!(" aborted       : {} ({})", result.aborted, result.reason);
    println!(" wall total    : {:.1}s", total);
    println!(" growth        : {}  rate={:.4}", kind, rate);

    // Final JSON to stdout
    println!();
    println!(
        "{{\"prime\":{},\"max_depth_reached\":{},\"state_counts\":{:?},\"wall_s\":{:.2},\"aborted\":{},\"abort_reason\":\"{}\",\"growth_fit\":{{\"type\":\"{}\",\"rate\":{}}}}}",
        cfg.prime,
        result.layer_sizes.len() - 1,
        result.layer_sizes,
        total,
        result.aborted,
        result.reason,
        kind,
        rate
    );
}
