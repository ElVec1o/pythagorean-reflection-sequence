#!/usr/bin/env python3
"""
u_growth_disk.py  --  EXTERNAL-MEMORY (disk-backed) geodesic growth u_n for OEIS A396406.

GUARANTEED OOM-SAFE: RAM is bounded by ONE sort buffer (you choose CHUNK_MB; default 800).
The spheres of radius n-1, n, n+1 live on DISK as SORTED fixed-length binary files; all
set operations (dedup, set-difference) are streaming sorted merges. RAM never holds a whole
sphere, so it does not OOM no matter how deep you go -- the limit is DISK and TIME, not the
24 GB. (The naive in-RAM BFS OOMs at depth 42 because it holds the whole ball; a frontier-only
in-RAM BFS does not help, since for growth ratio 1.49 the ball ~ 3.04*u_n ~ one sphere anyway.)

  ***  RAM rule of thumb: peak RAM ~= 2.3 * CHUNK_MB  (Python bytes-object overhead).  ***
  ***  So on 24 GB, CHUNK_MB up to ~6000 is safe; the default 800 uses ~2 GB. Bigger     ***
  ***  CHUNK = fewer chunk files = faster, but more RAM. Pick CHUNK_MB <= free_RAM/2.5.   ***

Same validated generators as lamp_lib.bfs  =>  identical u_n (auto-checked vs OEIS to n=42).

DISK NEED at depth n ~ 3 * u_n * KEYLEN bytes (KEYLEN=38). e.g. n=46: u_46~7e8 -> ~80 GB of
scratch; n=44: ~36 GB; n=43: ~24 GB. Point WORKDIR at a disk with room. Keys are deleted as
spheres age out, so steady-state scratch ~ 3 spheres.

USAGE:
  python3 u_growth_disk.py MAXDEPTH [WORKDIR] [CHUNK_MB]
  e.g.  python3 u_growth_disk.py 46 /Volumes/scratch/ubfs 1500
Resumable: it writes u_values.txt after every depth; if restarted it resumes from the last
sphere files present in WORKDIR.

ELEMENT (e,dl,k,L): e in {+1,-1}, dl in {0,1}, k int, L dict site->nonzero int (|val|<128 ok
to depth ~380, |k|,|span| < 32767). Generators (cost 1): (e,1-dl,k,L); (-e,1-dl,k,L);
dl==0 -> (e,1,k-1, L[k-1]+=e); dl==1 -> (e,0,k+1, L[k]-=e).
"""
import sys, os, struct, heapq, glob, tempfile

KNOWN = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
   17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,
   2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]

import os as _os
MAXVALS = int(_os.environ.get('UBFS_MAXVALS', '32'))  # support span cap -> max depth ~ 2*MAXVALS+1
KEYLEN  = 1 + 2 + 2 + 1 + MAXVALS  # hdr, k(int16), lo(int16), n(uint8), vals(int8 each)

def encode(e, dl, k, L):
    hdr = ((0 if e == 1 else 1) << 1) | (dl & 1)
    if L:
        lo = min(L); hi = max(L); n = hi - lo + 1
        vals = bytes((L.get(lo + i, 0) & 0xff) for i in range(n))
    else:
        lo = 0; n = 0; vals = b''
    assert n <= MAXVALS, f"span {n} exceeds MAXVALS={MAXVALS}; raise MAXVALS"
    return struct.pack('<BhhB', hdr, k, lo, n) + vals + b'\x00' * (MAXVALS - n)

def decode(key):
    hdr, k, lo, n = struct.unpack_from('<BhhB', key, 0)
    e = 1 if (hdr >> 1) == 0 else -1
    dl = hdr & 1
    L = {}
    for i in range(n):
        v = key[6 + i]
        if v:
            L[lo + i] = v - 256 if v >= 128 else v   # signed int8
    return e, dl, k, L

def neighbors(e, dl, k, L):
    yield encode(e, 1 - dl, k, L)
    yield encode(-e, 1 - dl, k, L)
    if dl == 0:
        D = dict(L); nv = D.get(k - 1, 0) + e
        if nv == 0: D.pop(k - 1, None)
        else: D[k - 1] = nv
        yield encode(e, 1, k - 1, D)
    else:
        D = dict(L); nv = D.get(k, 0) - e
        if nv == 0: D.pop(k, None)
        else: D[k] = nv
        yield encode(e, 0, k + 1, D)

# ---- sorted-file utilities (fixed-length KEYLEN records) ----
def read_keys(path):
    with open(path, 'rb') as f:
        while True:
            b = f.read(KEYLEN)
            if len(b) < KEYLEN: break
            yield b

def expand_to_sorted_chunks(sphere_path, workdir, chunk_keys):
    """stream sphere -> generate neighbors -> sorted chunk files. returns chunk paths."""
    chunks = []; buf = []
    def flush():
        if not buf: return
        buf.sort()
        # dedup WITHIN the chunk (the 4 neighbors-per-element overlap heavily) -> less disk
        p = os.path.join(workdir, f"_chunk_{len(chunks):06d}.bin")
        with open(p, 'wb') as f:
            last = None; out = []
            for kk in buf:
                if kk != last:
                    out.append(kk); last = kk
            f.write(b''.join(out))
        chunks.append(p); buf.clear()
    for key in read_keys(sphere_path):
        e, dl, k, L = decode(key)
        for nk in neighbors(e, dl, k, L):
            buf.append(nk)
            if len(buf) >= chunk_keys: flush()
    flush()
    return chunks

def merge_dedup_minus(chunk_paths, minus_paths, out_path):
    """out = (dedup of merged chunks) \\ (union of minus_paths). all inputs sorted. streaming."""
    streams = [read_keys(p) for p in chunk_paths]
    merged = heapq.merge(*streams)
    minus_streams = [read_keys(p) for p in minus_paths]
    mm = heapq.merge(*minus_streams) if minus_streams else iter(())
    cnt = 0
    cur_minus = next(mm, None)
    last = None
    tmp = out_path + '.tmp'                    # write to tmp, atomic-rename: a kill never
    with open(tmp, 'wb') as out:              # leaves a TRUNCATED sphere that resume trusts
        wbuf = []
        for key in merged:
            if key == last: continue          # dedup
            last = key
            while cur_minus is not None and cur_minus < key:
                cur_minus = next(mm, None)
            if cur_minus is not None and cur_minus == key:
                continue                        # in prev/cur sphere -> skip
            wbuf.append(key); cnt += 1
            if len(wbuf) >= 1 << 16:
                out.write(b''.join(wbuf)); wbuf.clear()
        if wbuf: out.write(b''.join(wbuf))
    os.replace(tmp, out_path)                  # atomic on POSIX
    return cnt

def rss_gb():
    try:
        import resource
        m = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return m / (1024**3 if sys.platform == 'darwin' else 1024**2)
    except Exception:
        return -1.0

def run(maxdepth, workdir, chunk_keys):
    os.makedirs(workdir, exist_ok=True)
    sph = lambda n: os.path.join(workdir, f"sphere_{n:03d}.bin")
    # resume?  Source of truth = u_values.txt (written AFTER its sphere). Trust its length,
    # require spheres {start, start-1} present, and DELETE any higher/partial spheres left by
    # a kill (this is what made the old resume go off-by-one on a corrupt sphere).
    uv = os.path.join(workdir, "u_values.txt")
    have = sorted(int(os.path.basename(p)[7:10]) for p in glob.glob(os.path.join(workdir, "sphere_*.bin")))
    if have and have[-1] >= 1 and os.path.exists(uv):
        with open(uv) as f:
            u = [int(x) for x in f.read().split()]
        start = len(u) - 1                         # u has u_0..u_start  <=>  sphere_start is final
        for j in have:
            if j > start:                          # partial sphere from the kill -> discard
                os.remove(sph(j))
        if not (os.path.exists(sph(start)) and (start < 1 or os.path.exists(sph(start - 1)))):
            raise SystemExit(f"resume: spheres for depth {start},{start-1} missing; rerun from scratch")
        print(f"# resuming from depth {start} (u has {len(u)} entries; verified consistent)")
    else:
        with open(sph(0), 'wb') as f: f.write(encode(1, 0, 0, {}))
        u = [1]; start = 0
        with open(os.path.join(workdir, "u_values.txt"), 'w') as f: f.write("1\n")
        print(f"{'n':>3} {'u_n':>14} {'check':>7} {'RAM(GB)':>8}")
        print(f"{0:>3} {1:>14} {'OK':>7} {rss_gb():>8.2f}")
    for n in range(start + 1, maxdepth + 1):
        chunks = expand_to_sorted_chunks(sph(n - 1), workdir, chunk_keys)
        minus = [sph(n - 1)] + ([sph(n - 2)] if n >= 2 else [])
        un = merge_dedup_minus(chunks, minus, sph(n))
        for c in chunks: os.remove(c)
        u.append(un)
        with open(os.path.join(workdir, "u_values.txt"), 'w') as f:
            f.write(" ".join(map(str, u)) + "\n")
        ok = (n < len(KNOWN) and un == KNOWN[n])
        flag = 'OK' if ok else ('X!!' if n < len(KNOWN) else '(new)')
        print(f"{n:>3} {un:>14} {flag:>7} {rss_gb():>8.2f}", flush=True)
        if n < len(KNOWN) and not ok:
            print(f"  !! MISMATCH n={n}: {un} != {KNOWN[n]} -- bug, aborting"); return u
        if n >= 2:
            old = sph(n - 2)
            if os.path.exists(old): os.remove(old)   # age out (keep n-1, n)
    print("\nu:", u)
    return u

if __name__ == "__main__":
    md = int(sys.argv[1]) if len(sys.argv) > 1 else 44
    wd = sys.argv[2] if len(sys.argv) > 2 else os.path.join(tempfile.gettempdir(), "ubfs_work")
    chunk_mb = int(sys.argv[3]) if len(sys.argv) > 3 else 800
    chunk_keys = max(100000, (chunk_mb * 1024 * 1024) // KEYLEN)
    print(f"# workdir={wd}  chunk={chunk_mb}MB ({chunk_keys} keys)  KEYLEN={KEYLEN}")
    run(md, wd, chunk_keys)
