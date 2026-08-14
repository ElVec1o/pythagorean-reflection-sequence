#!/usr/bin/env python3
"""
u_growth_lowmem.py  --  memory-bounded geodesic growth u_n for OEIS A396406.

WHY: the naive BFS stores ALL visited elements (cumulative ~ sum_{m<=n} u_m), which
OOMs near depth 42 on 24 GB. This version is a FRONTIER BFS: it keeps only the spheres
of radius n-1 and n in RAM (peak ~ 3*u_n keys, NOT the cumulative), so memory scales with
the LARGEST sphere, not the ball. Same validated generators as lamp_lib.bfs -> identical u_n.

ELEMENT = (e, dl, k, L):  e in {+1,-1} (eps), dl in {0,1} (delta), k = position (int),
L = lamp config (dict site->nonzero int).  Generators (cost 1 each), from lamp_lib:
  (e,1-dl,k,L) ; (-e,1-dl,k,L) ; if dl==0: (e,1,k-1, L with L[k-1]+=e)
                                  if dl==1: (e,0,k+1, L with L[k]-=e).
Distance from identity (1,0,0,{}) = word length = TRUE geodesic length.

MEMORY: peak ~ 3 * u_n * (key_bytes + set_overhead). Keys are compact bytes (~ 2 + 2*span).
At depth ~46-48, u_n ~ 1e8, peak ~ a few GB to ~15 GB depending on Python set overhead.
Set MAXDEPTH for your RAM; the script prints sphere sizes + a live RSS estimate so you can
stop before OOM. For deeper, lower memory: switch SPHERE_BACKEND to 'array' (sorted bytes
+ binary-search dedup; ~3x less RAM, a bit slower) -- see the note at SphereSet.

USAGE:  python3 u_growth_lowmem.py [MAXDEPTH]      (default 44)
Validates u_0..u_42 against the known OEIS values automatically.
"""
import sys, struct
from array import array

KNOWN = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
   17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,
   2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]

# ---- compact canonical encoding of (e,dl,k,L) ----
# L stored as values over [lo, hi]; lo,hi the support extent (empty -> lo=hi=k sentinel).
# key = bytes: header(e,dl) 1 byte ; k (int16 signed) ; lo (int16) ; n (uint8) ; values (int16 each)
def encode(e, dl, k, L):
    hdr = ((0 if e == 1 else 1) << 1) | (dl & 1)
    if L:
        lo = min(L); hi = max(L)
        vals = [L.get(s, 0) for s in range(lo, hi + 1)]
    else:
        lo = 0; vals = []
    # pack
    out = bytearray()
    out.append(hdr)
    out += struct.pack('<hhB', k, lo, len(vals))
    for v in vals:
        out += struct.pack('<h', v)
    return bytes(out)

def decode(key):
    hdr = key[0]
    e = 1 if (hdr >> 1) == 0 else -1
    dl = hdr & 1
    k, lo, n = struct.unpack_from('<hhB', key, 1)
    L = {}
    off = 6
    for i in range(n):
        (v,) = struct.unpack_from('<h', key, off); off += 2
        if v != 0:
            L[lo + i] = v
    return e, dl, k, L

def neighbors(e, dl, k, L):
    yield (e, 1 - dl, k, L)
    yield (-e, 1 - dl, k, L)
    if dl == 0:
        D = dict(L); D[k - 1] = D.get(k - 1, 0) + e
        if D[k - 1] == 0: del D[k - 1]
        yield (e, 1, k - 1, D)
    else:
        D = dict(L); D[k] = D.get(k, 0) - e
        if D[k] == 0: del D[k]
        yield (e, 0, k + 1, D)

def rss_gb():
    try:
        import resource
        m = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return m / (1024**3 if sys.platform == 'darwin' else 1024**2)  # macOS bytes, linux KB
    except Exception:
        return -1.0

def run(maxdepth):
    ident = (1, 0, 0, {})
    k_ident = encode(*ident)
    prev = set()                 # sphere n-1 (keys)
    cur = {k_ident}              # sphere n   (keys)
    u = [1]                      # u_0
    print(f"{'n':>3} {'u_n':>14} {'known?':>7} {'peakRSS(GB)':>11}")
    print(f"{0:>3} {1:>14} {'OK' if KNOWN[0]==1 else 'X':>7} {rss_gb():>11.2f}")
    for n in range(1, maxdepth + 1):
        nxt = set()
        for key in cur:
            e, dl, k, L = decode(key)
            for ne in neighbors(e, dl, k, L):
                nk = encode(*ne)
                if nk not in prev and nk not in cur:
                    nxt.add(nk)          # set membership dedups within sphere n+1
        un = len(nxt)
        u.append(un)
        ok = (n < len(KNOWN) and un == KNOWN[n])
        flag = 'OK' if ok else ('X!!' if n < len(KNOWN) else '(new)')
        print(f"{n:>3} {un:>14} {flag:>7} {rss_gb():>11.2f}", flush=True)
        if n < len(KNOWN) and not ok:
            print(f"  !! MISMATCH at n={n}: got {un}, expected {KNOWN[n]} -- ABORTING (encoding/generator bug)")
            return u
        prev = cur
        cur = nxt
    print("\nu sequence:", u)
    return u

if __name__ == "__main__":
    md = int(sys.argv[1]) if len(sys.argv) > 1 else 44
    run(md)
