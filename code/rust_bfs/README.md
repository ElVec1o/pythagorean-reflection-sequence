# Bonfioli BFS — Rust port (disk-streaming frontier)

Push the universal sequence `u_d` past depth 41 on the 24 GB Mac mini.

## Why this build

The original in-memory Rust port reached d=41 in ~5 min but spiked to ~20 GB
of true memory use during layer expansion (old frontier + new frontier +
HashSet all live in RAM simultaneously). That worked because the Mac mini
has 24 GB physical, but d=42 would have needed ~28 GB → guaranteed crash.

This build keeps the frontier on **disk** between layers. Per-layer we
stream the old frontier in via `BufReader` and stream the new frontier out
via `BufWriter`. Only the cumulative `seen` Vec, the `frontier_lasts`
vector, and the layer-local `HashSet<u64>` remain in RAM.

| metric           | original     | disk-stream  |
|------------------|--------------|--------------|
| RAM at d=32      | ~0.57 GB     | ~0.11 GB     |
| RAM at d=41      | ~5 GB        | ~4 GB        |
| **RAM at d=42**  | **~28 GB (won't fit)** | **~5 GB** |
| RAM at d=43      | n/a          | ~7 GB        |
| RAM at d=44      | n/a          | ~10 GB       |

## Targets (Mac mini, 24 GB unified memory)

| depth | est. wall | RAM peak | disk peak | risk |
|-------|-----------|----------|-----------|------|
| 41 | ~5 min | ~4 GB | ~10 GB | trivial |
| 42 | ~7 min | ~5 GB | ~14 GB | safe |
| 43 | ~10 min | ~7 GB | ~22 GB | safe |
| 44 | ~15 min | ~10 GB | ~33 GB | check disk |
| 45 | ~25 min | ~15 GB | ~50 GB | tight |

Disk peak includes both the live temp frontier file AND the saved snapshot
if you pass `--save-frontier`. Make sure you have that much free space
on the volume containing the working directory.

## Install Rust (one-time)

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME/.cargo/env"
rustc --version    # should be 1.70+
```

## Build

```bash
cd path/to/this/repo/code/rust_bfs
cargo build --release
```

## Run

```bash
# Default: depth 41, RSS guard 18 GB, wall limit 4 h
./target/release/bonfioli_bfs

# Sanity check (must match F5 / D14v2 through d=40)
./target/release/bonfioli_bfs 32 4 1
```

The output now includes a per-layer `disk = X GB` column showing the
current frontier file size on disk.

## Resume (incremental depth pushes)

Save a snapshot once, then jump to higher depths without recomputing.

```bash
# Compute d=41 from scratch, save snapshot (~12 GB binary file)
./target/release/bonfioli_bfs 41 12 1 --save-frontier d41.bin

# Resume from d41 → d42 (save d42 too, ~18 GB)
./target/release/bonfioli_bfs 42 14 1 --resume d41.bin --save-frontier d42.bin

# d42 → d43 (~28 GB snapshot file)
./target/release/bonfioli_bfs 43 18 1 --resume d42.bin --save-frontier d43.bin

# d43 → d44
./target/release/bonfioli_bfs 44 22 1 --resume d43.bin --save-frontier d44.bin

# Peek at a snapshot
./target/release/bonfioli_bfs --inspect d41.bin

# Full help
./target/release/bonfioli_bfs --help
```

**Snapshot file sizes:**

| depth | snapshot size |
|-------|---------------|
| 40 | ~8 GB |
| 41 | ~12 GB |
| 42 | ~18 GB |
| 43 | ~28 GB |
| 44 | ~42 GB |

**Disk space recommendation:** at d=44, you need free space for the
saved snapshot (~42 GB) AND the live temp frontier file (~33 GB) AND
the resumed temp file (~28 GB) all at once. That's ~100 GB free during
the d=44 run. The temp files are deleted at the end, but during the
run all three coexist.

If disk is tight, skip `--save-frontier` on the intermediate runs and
only save at the depths you actually want to keep.

## Temp files

This build creates files named `rust_bfs_blob_<pid>_*.tmp` in the
working directory while running. They are deleted on normal exit.
If a run is killed (Ctrl-C, kill -9, system crash), these files may
be left behind — they are safe to delete manually:

```bash
rm rust_bfs_blob_*.tmp
```

## Correctness

The first 41 entries MUST match this canonical reference:

```
[1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875,
 1345, 2066, 3203, 4971, 7574, 11543, 17683, 27108, 41067,
 62263, 94622, 143881, 217101, 327832, 495443, 749195,
 1127236, 1697179, 2554961, 3848384, 5777651, 8679441,
 13031206, 19574659, 29338781, 43997388, 65932461, 98849591]
```

The disk-streaming version produces the SAME u_d sequence — verified
through d=32 in the sandbox. If your output diverges, stop and report.

## Architecture sketch

```
state = 96 bytes packed (see source comment for layout)

frontier_blob_path : PathBuf      (frontier file on disk)
frontier_lasts     : Vec<i8>      (parallel last-letter array, in RAM)
seen               : Vec<u64>     (sorted; binary_search for membership)
layer_seen         : HashSet<u64> (rebuilt each layer, then dropped)
```

**Layer expansion**:

1. Open `frontier_blob_path` with `BufReader` (8 MB buffer).
2. Open new temp file with `BufWriter` (8 MB buffer).
3. For each parent state streamed in, generate 3 children via `step()`,
   hash the packed result, skip if in cumulative `seen` or already in
   `layer_seen`, else write to the new file.
4. Flush, close both files.
5. Delete the old frontier file; rename pointer to the new one.
6. Linear two-way merge of `layer_seen` hashes into `seen`.

**Snapshot save**: write header + `u` + `seen` + `lasts` to the snapshot
file, then stream the frontier blob file into it. No in-memory copy of
the blob.

**Snapshot load**: read header + `u` + `seen` + `lasts`, then stream the
frontier blob portion to a fresh temp file. No in-memory copy of the
blob.

## What to do if d=42 still crashes

It shouldn't — but if it does:

1. Read `rust_bfs_progress.json`. The `completed` field tells you the
   deepest finished layer.
2. Read the on-disk temp file `rust_bfs_blob_<pid>_d<N>.tmp` to confirm
   the frontier is intact (if it exists).
3. Re-run with a tighter RSS guard to pin down the leak.
4. Report numbers — there may be an issue with the `seen` Vec resort or
   the HashSet sizing that needs a smaller `layer_seen` (sorted Vec
   instead of HashSet would save ~3-4 GB at d=42).

## Future optimizations (if we want d=45+)

The remaining in-RAM costs at d=45 are:
- `seen` Vec: ~12 GB
- `layer_seen` HashSet: ~9 GB
- `frontier_lasts`: ~2 GB

The seen Vec dominates. Options:
- Replace with a memory-mapped sorted file (zero RAM cost, slower lookup).
- Switch to a streaming external-merge dedup at end of layer.

Not in scope for the current push; this build targets d=42-44 reliably.
