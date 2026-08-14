#!/usr/bin/env python3
"""
Optimized integer-encoded BFS for the TRUE word-length distribution u_n.

State = (eps in {+1,-1}, delta in {0,1}, k, deposit-vector a).
Generators (from lamp_lib.bfs, the validated true-metric Cayley graph):
   (e,1-dl,k,L), (-e,1-dl,k,L), and a catalytic deposit move that shifts k.
The BFS distance in THIS graph IS the true word length (validated: u_n).

Speed/RAM: we pack each state into a single Python int and keep a flat set of
ints, far lighter than tuples of tuples. Deposit values are bounded; we encode
the sparse vector as (offset, signed base-B digits). Counts per layer are
accumulated; only the seen-set persists.

We VALIDATE the int-encoding round-trips and that u_n matches the reference
through the depth where full BFS is known.
"""
import sys, time, resource

# ---- bounds discovered empirically (deposit magnitudes stay small) ----
# encode deposit vector: list of (site, val). sites range over a window; vals are
# small ints. We map val v -> (v + VOFF) in [0, VBASE). Sites -> (site + SOFF).
VOFF = 32          # deposit values in [-31, 31]
VBASE = 64
SOFF = 96          # site indices in [-95, 95]; plenty for depth<=60
SBASE = 192

def encode(e, dl, k, items):
    # items: sorted tuple of (site, val) with val!=0
    # pack: header (e,dl,k) then each (site,val) as two base-digit groups.
    # Use a big-int accumulator.
    x = (1 if e == 1 else 0)
    x = x * 2 + dl
    x = x * SBASE + (k + SOFF)
    for (s, v) in items:
        x = x * SBASE + (s + SOFF)
        x = x * VBASE + (v + VOFF)
    # terminator so different-length vectors never collide via trailing zeros
    x = x * 2 + 1
    return x

def bfs_u(maxd, ref=None, verbose=True):
    # initial identity: (e=1, dl=0, k=0, no deposits)
    ident_items = ()
    seen = set()
    seen.add(encode(1, 0, 0, ident_items))
    # frontier as list of decoded tuples (e,dl,k, dict-as-sorted-tuple)
    frontier = [(1, 0, 0, ())]
    counts = [0] * (maxd + 1)
    counts[0] = 1
    t0 = time.time()
    for d in range(maxd):
        nxt = []
        ap = nxt.append
        sadd = seen.add
        scon = seen.__contains__
        for (e, dl, k, L) in frontier:
            # generator 1,2: flip delta, keep deposits
            for ne in ((e, 1 - dl, k, L), (-e, 1 - dl, k, L)):
                code = encode(ne[0], ne[1], ne[2], ne[3])
                if not scon(code):
                    sadd(code); ap(ne)
            # generator 3: catalytic deposit move shifting k
            Ld = dict(L)
            if dl == 0:
                site = k - 1
                v = Ld.get(site, 0) + e
                if v == 0:
                    Ld.pop(site, None)
                else:
                    Ld[site] = v
                nk = k - 1; ndl = 1
            else:
                site = k
                v = Ld.get(site, 0) - e
                if v == 0:
                    Ld.pop(site, None)
                else:
                    Ld[site] = v
                nk = k + 1; ndl = 0
            items = tuple(sorted(Ld.items()))
            code = encode(e, ndl, nk, items)
            if not scon(code):
                sadd(code); ap((e, ndl, nk, items))
        counts[d + 1] = len(nxt)
        frontier = nxt
        if verbose:
            rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
            print(f"  depth {d+1}: layer {len(nxt):>12d}  total_seen {len(seen):>13d}  "
                  f"{time.time()-t0:7.1f}s  RSS {rss:6.0f}MB", flush=True)
        if ref is not None and d + 1 < len(ref) and counts[d + 1] != ref[d + 1]:
            print(f"  !! MISMATCH at depth {d+1}: got {counts[d+1]} ref {ref[d+1]}", flush=True)
            return counts, False
    return counts, True

if __name__ == "__main__":
    md = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    U = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
         17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,
         1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,
         65932461,98849591,147969934]
    counts, ok = bfs_u(md, ref=U)
    print("=" * 60)
    print(f"validated against reference: {ok}")
    print("u_n:")
    for n in range(md + 1):
        ref = U[n] if n < len(U) else "?"
        tag = "" if (n < len(U) and counts[n] == U[n]) else "  <-- NEW" if n >= len(U) else "  MISMATCH"
        print(f"  u_{n} = {counts[n]}   (ref {ref}){tag}")
