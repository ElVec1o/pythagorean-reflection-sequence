#!/usr/bin/env python3
"""
SEAM #3 -- corrected bulk kernel, fast closed-form (no BFS).

A one-sided bulk run anchored at marker site 0 (eps=1,dl=0,k=0): deposits at increasing
edges with gap-runs between. Using the VALIDATED relaxed length formula:
  relaxed_len = sum_edges m_j + sum_interior_sites max(|a_{j-1}|,|a_j|)
  m_j = |a_j| for active, 2 for gap (reachability).
And the VALIDATED true correction: true_len = relaxed_len + 2*c, where (bulk_cycle_rule.py)
  c = number of gap edges lying BEFORE a later deposit
    = sum over maximal interior gap-runs of (their length)   [each gap edge before the
      next deposit is one isolated 2-cycle].
  (trailing gaps after the last deposit are not part of the run; the anchor at edge0 means
   no leading gap.)

We build, for a run = [s_0, g_1, s_1, g_2, s_2, ..., g_d, s_d]  (s_i>=1 deposit half-sizes,
g_i>=0 gap-run lengths before deposit i), the EXACT generating contribution:
   relaxed length L_rel/... in q (q=x^2, so q-power = length/2):
     edges: sum_i s_i (active, length 2s_i -> q^{s_i})  +  sum_i g_i * 1 (gap length 2 -> q^1)
     sites: between deposit i-1 and i:
         if g_i=0 (adjacent): max(s_{i-1},s_i)            -> q^{max}
         if g_i>=1: left join q^{s_{i-1}} + interior gap-gap sites (g_i-1 of them, each
                    max(0,0)=0 -> q^0) + right join q^{s_i}.  Total q^{s_{i-1}+s_i}.
   plus the LEFT BOUNDARY at site 0 (anchor): the marker site cost. For a clean BULK
   DENOMINATOR study we strip the boundary (it is a bounded prefactor, holomorphic & nonzero)
   and study the INTERIOR transfer kernel between deposits, exactly as the relaxed S_1 does.

   true correction: c = sum_i g_i  (every gap edge is before deposit i) -> extra factor q^{g_i}
   per gap-run of length g_i, i.e. y^{g_i} with y the cycle marker (true y=q).

So the interior transfer kernel between consecutive deposit half-sizes a=s_{i-1}, b=s_i is
   K(a,b; y) = q^{max(a,b)}                                  [g=0, adjacent]
             + sum_{g>=1} q^{a} (q*y)^{g} q^{b}              [g>=1 gaps, each gap q*y^... ]
   wait: each gap edge contributes q (length) and y (cycle); relaxed y=1 => q per gap.
       = q^{max(a,b)} + q^{a+b} * (q y)/(1 - q y).
At y=1: K_rel(a,b)= q^{max(a,b)} + q^{a+b} q/(1-q).

The block GF over deposit chains (catalytic) is built from this kernel.  We VERIFY the
y=1 block reproduces the validated relaxed bulk series, then extract the y-dependent
denominator and test for cosine oscillation -> infinitely many zeros -> U bulk poles.
"""
import mpmath as mp
mp.mp.dps=40

# ----- relaxed bulk series ground truth (validated recursion) -----
def relaxed_bulk_series(Nq, Smax=60):
    def Fblock(q):
        sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
        M=mp.matrix(n,n); b=mp.matrix(n,1)
        for s in sizes:
            b[idx[s],0]=2*q**s
            for sp in sizes:
                if sp>=s: M[idx[s],idx[sp]]+=2*q**(s)*q**(sp)
                else:     M[idx[s],idx[sp]]+=2*q**(2*s)
        F=mp.lu_solve(mp.eye(n)-M,b)
        return sum(F[i,0] for i in range(n))
    return [int(mp.nint(c)) for c in mp.taylor(Fblock,0,Nq)]

# ----- candidate corrected block via explicit-deposit kernel K(a,b;y) -----
# Block over chains of deposits a_1..a_d (d>=1), weight:
#   2 per deposit (signs)? NO -- the relaxed recursion seed is 2q^s with the factor 2.
#   We mirror it: P_b = e(b) * ( 1 + sum_a P_a K(a,b;y) ), e(b)=2 q^b? Let's CALIBRATE the
#   seed/edge factor by requiring y=1 to reproduce the relaxed series.
def kernel_block(q,y,edgefac, Smax=60):
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    g=(q*y)/(1-q*y)
    def K(a,b): return q**max(a,b)+q**(a+b)*g
    E=mp.matrix(n,1)
    for b in sizes: E[idx[b],0]=edgefac(b,q)
    M=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            M[idx[b],idx[a]]=edgefac(b,q)*K(a,b)
    P=mp.lu_solve(mp.eye(n)-M,E)
    return sum(P[i,0] for i in range(n))

if __name__=="__main__":
    Nq=14
    rel=relaxed_bulk_series(Nq)
    print("relaxed bulk (validated):", rel)
    # try edgefac = 2q^b
    for label,ef in [("2q^b", lambda b,q:2*q**b)]:
        ser=[int(mp.nint(c)) for c in mp.taylor(lambda q: kernel_block(q,mp.mpf(1),ef),0,Nq)]
        print(f"kernel block y=1 [{label}]:", ser)
        print("  match relaxed:", ser==rel)
