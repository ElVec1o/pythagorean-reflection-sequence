#!/usr/bin/env python3
# Structural probe of (u_n mod p): is there a PROVABLE non-automaticity mechanism,
# or only the (strong) kernel evidence?  Tests the prime suspects:
#   A. full-tree kernel quantification (deficit from maximal p^k growth)
#   B. square-gap structure (squares are the classic non-automatic set; U=W(x,x^2)
#      maps the j^2 block-gaps to even-square positions)
#   C. zero-set base-p structure + subword complexity (Cobham: automatic => p(L)=O(L))
#
# Usage: python3 structure_probe.py u_mod3_N180.txt 3 [u_mod5_N130.txt 5 ...]
import sys

def load(path):
    return [int(x) for x in open(path).read().split()]

def kernel_levels(seq, p, kmax, minov=4):
    N = len(seq) - 1
    elems = []; per = []
    for k in range(kmax + 1):
        pk = p**k; new = 0; reliable = True; lens = []
        for r in range(pk):
            sub = tuple(seq[pk*n + r] for n in range((N - r)//pk + 1) if pk*n + r <= N)
            if len(sub) < minov:
                reliable = False; continue
            lens.append(len(sub))
            if not any(len(e) >= minov and len(sub) >= minov and
                       e[:min(len(e),len(sub))] == sub[:min(len(e),len(sub))] for e in elems):
                elems.append(sub); new += 1
        full = p**k
        per.append((k, new, full, len(elems), reliable, min(lens) if lens else 0))
    return per

def full_tree_cum(p, k):  # cumulative size of full p-ary tree to level k
    return (p**(k+1) - 1)//(p - 1)

def runs_of_zeros(seq, p):
    """gaps between consecutive zeros of (u_n mod p): do they grow like squares (~2*sqrt) ?"""
    zeros = [n for n,v in enumerate(seq) if v % p == 0]
    gaps = [zeros[i+1]-zeros[i] for i in range(len(zeros)-1)]
    return zeros, gaps

def subword_complexity(seq, p, Lmax):
    out = []
    for L in range(1, Lmax+1):
        facs = set(tuple(seq[i:i+L]) for i in range(len(seq)-L+1))
        windows = len(seq)-L+1
        out.append((L, len(facs), windows))
    return out

def square_probe(seq, p):
    """values of u_n at structured positions: n=j^2, 2j^2, triangular, oblong."""
    N = len(seq)-1
    def at(f):
        vals=[]; j=0
        while True:
            n=f(j)
            if n>N: break
            vals.append(seq[n]); j+=1
        return vals
    return {
        'n=j^2':      at(lambda j: j*j),
        'n=2j^2':     at(lambda j: 2*j*j),
        'n=j^2+j':    at(lambda j: j*j+j),          # oblong
        'n=j(j+1)/2': at(lambda j: j*(j+1)//2),     # triangular
        'n=j^2-1':    at(lambda j: j*j-1) if True else None,
    }

for ai in range(1, len(sys.argv), 2):
    path = sys.argv[ai]; p = int(sys.argv[ai+1])
    seq = load(path); N = len(seq)-1
    print("="*70)
    print(f"  {path}   p={p}   u_0..u_{N}  ({N+1} terms)")
    print("="*70)

    # ---- A. full-tree kernel quantification ----
    print("\n[A] p-KERNEL vs FULL p-ARY TREE  (deficit = how far below maximal)")
    kmax = 6
    per = kernel_levels(seq, p, kmax)
    print(f"  {'k':>2} {'new':>5} {'max(p^k)':>9} {'cumul':>6} {'fulltree':>9} {'deficit':>8} {'minlen':>7} reliable")
    for (k,new,full,cum,rel,ml) in per:
        ft = full_tree_cum(p,k)
        print(f"  {k:>2} {new:>5} {full:>9} {cum:>6} {ft:>9} {ft-cum:>8} {ml:>7}  {'yes' if rel else 'NO (short)'}")
    print("  => 'deficit' staying O(1) while cumul ~ p-ary-tree = MAXIMAL non-automaticity.")

    # ---- B. square-gap structure ----
    print("\n[B] SQUARE-GAP STRUCTURE  (squares = classic non-automatic set)")
    zeros, gaps = runs_of_zeros(seq, p)
    print(f"  #zeros={len(zeros)} / {N+1}   density~{len(zeros)/(N+1):.3f}")
    print(f"  zero positions (first 30): {zeros[:30]}")
    print(f"  consecutive zero-gaps   : {gaps[:30]}")
    sqs = [j*j for j in range(int(N**0.5)+1)]
    print(f"  zeros that are squares  : {[z for z in zeros if z in set(sqs)]}")
    print(f"  squares' u-values u_{{j^2}}: {square_probe(seq,p)['n=j^2']}")
    print(f"  u_{{2 j^2}}               : {square_probe(seq,p)['n=2j^2']}")
    print(f"  u_{{triangular}}          : {square_probe(seq,p)['n=j(j+1)/2']}")
    print(f"  u_{{oblong j^2+j}}        : {square_probe(seq,p)['n=j^2+j']}")

    # ---- C. subword complexity (Cobham: automatic => p(L)=O(L)) ----
    print("\n[C] SUBWORD COMPLEXITY p(L)  (Cobham: p-automatic => p(L)=O(L))")
    sc = subword_complexity(seq, p, 10)
    print(f"  {'L':>2} {'p(L)':>6} {'p(L)/L':>8} {'#windows':>9}  (saturated when p(L)~#windows)")
    for (L,c,w) in sc:
        sat = ' <-- saturated' if c >= w-1 else ''
        print(f"  {L:>2} {c:>6} {c/L:>8.1f} {w:>9}{sat}")
print()
print("# done. structural read: any clean square-encoding => provable; else kernel = strong evidence.")
