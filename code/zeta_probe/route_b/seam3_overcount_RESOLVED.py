#!/usr/bin/env python3
"""
SEAM #3 gap-bridge kernel OVERCOUNTING -- EXACT SOURCE IDENTIFIED (2026-06-16).

The seam3 kernel K(a,b;y) = q^{max(a,b)} + q^{a+b} * (qy)/(1-qy) overcounts the
relaxed bulk block already at y=1: 22 vs 18 at q^5 (header claim reproduced).

ROOT CAUSE (proven numerically below):
  The CORRECT relaxed interior kernel is simply K_rel(a,b) = q^{max(a,b)}.
  This follows from the VALIDATED catalytic recursion
     F_s = 2q^s + 2q^s sum_{s'>=s} F_{s'} q^{s'} + 2q^{2s} sum_{s'<s} F_{s'}
        = 2q^s ( 1 + sum_{s'} F_{s'} q^{max(s',s)} ),
  because s'>=s gives q^{s'}=q^{max} and s'<s gives the q^{2s}=q^{s}*q^{s} site+edge
  i.e. q^{max(s,s')} with max=s.  So the per-pair kernel is q^{max(a,b)} with NO
  additive gap term, and it reproduces [0,2,2,6,2,18,6,42,18,118,50,282,190,...] EXACTLY.

  The seam3 additive term q^{a+b}*(qy)/(1-qy) is SPURIOUS.  It models "a gap-run of
  length g>=1 between deposits a and b" as an INDEPENDENT channel.  But in the catalytic
  recursion the ONLY state is the last deposit size (the catalytic variable); gap edges
  (reachability, forced m=2) and their q^1 lengths / q^0 interior-gap sites are ALREADY
  summed implicitly inside the magnitude ladder 2q^{k+1}/(1-q^{k+1}) of the telescoped
  alpha_k.  Re-adding an explicit geometric gap channel double-counts those configs.
  Hence the overcount.

MARKER-SHIELDING:  bulk_cycle_rule.py shows the true cycle count is NOT "sum of all gap
lengths": a gap adjacent to a marker site is SHIELDED (free).  Right-run deposit at edge e
(e gaps) -> c=e; left-run -> c=e-1 (first gap shielded); two right deposits 0,2 (one gap
between) -> c=0 (shielded), 0,3 (two gaps) -> c=1.  The seam3 (qy)/(1-qy) summed ALL gap
lengths with full y-weight, ignoring shielding -- a SECOND, independent error on top of
the spurious-channel error.  A marker-shielding correction alone does NOT fix the y=1
overcount, because that overcount exists even with NO cycles (y=1): the additive channel
itself must be removed.  The correct route is K_rel = q^{max} (no additive term), with the
cycle marker introduced through the connectivity-aware interface transfer
(seam3_bulk_transfer.py), NOT through a closed-form additive gap series.
"""
import mpmath as mp
mp.mp.dps = 50

def block(Kfun, Smax=40, N=14):
    sizes = list(range(1, Smax + 1)); n = len(sizes); idx = {s: i for i, s in enumerate(sizes)}
    def F(q):
        E = mp.matrix(n, 1); M = mp.matrix(n, n)
        for b in sizes:
            E[idx[b], 0] = 2 * q**b
            for a in sizes:
                M[idx[b], idx[a]] = 2 * q**b * Kfun(a, b, q)
        P = mp.lu_solve(mp.eye(n) - M, E)
        return sum(P[i, 0] for i in range(n))
    return [int(mp.nint(c)) for c in mp.taylor(F, 0, N)]

def relaxed_recursion(Smax=80, N=14):
    sizes = list(range(1, Smax + 1)); n = len(sizes); idx = {s: i for i, s in enumerate(sizes)}
    def Fr(q):
        M = mp.matrix(n, n); b = mp.matrix(n, 1)
        for s in sizes:
            b[idx[s], 0] = 2 * q**s
            for sp in sizes:
                if sp >= s: M[idx[s], idx[sp]] += 2 * q**s * q**sp
                else:       M[idx[s], idx[sp]] += 2 * q**(2 * s)
        F = mp.lu_solve(mp.eye(n) - M, b)
        return sum(F[i, 0] for i in range(n))
    return [int(mp.nint(c)) for c in mp.taylor(Fr, 0, N)]

if __name__ == "__main__":
    Kmax  = lambda a, b, q: q**max(a, b)
    Kseam = lambda a, b, q: q**max(a, b) + q**(a + b) * (q / (1 - q))   # y=1
    val   = relaxed_recursion()
    vm    = block(Kmax)
    vs    = block(Kseam)
    print("validated catalytic recursion      :", val)
    print("CORRECT kernel  K=q^max            :", vm, "  match:", vm == val)
    print("SEAM3   kernel  K=q^max + gap-term :", vs)
    print("OVERCOUNT (seam3 - correct)        :", [vs[i] - vm[i] for i in range(len(vm))])
    print()
    print(f"First overcount: q^5  seam3={vs[5]} vs correct={vm[5]}  (the '22 vs 18' header bug)")
    print("CONCLUSION: the additive gap channel q^{a+b}(qy)/(1-qy) is spurious; remove it.")
    print("            The correct relaxed interior kernel is K=q^{max(a,b)}.")
