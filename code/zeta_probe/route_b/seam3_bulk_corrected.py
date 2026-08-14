#!/usr/bin/env python3
"""
=============================================================================
SEAM #3 RESULT (2026-06-14): the corrected bulk denominator is y-FREE.
The seam's hoped-for mechanism (U gets its OWN new bulk pole family from a
cycle-corrected denominator) is KILLED. Precise reason below; the seam instead
REDUCES to the SAME numerator obstruction as the travel route, on the bulk
family {1-S_1=0} instead of the travel family {1-Sigma_1=0}.

ESTABLISHED RIGOROUSLY (validated):
 (1) The relaxed bulk block G_0=S_0/(1-S_1) has alpha_k=2q^{k+1}/(1-q^{k+1})
     = 2 sum_{s>=1} q^{(k+1)s}.  The Lambert factor 1/(1-q^{k+1}) is the
     geometric sum over DEPOSIT HALF-SIZES s (magnitudes), via the catalytic
     telescoping (travel_singularity.py derivation).  This magnitude ladder is
     what generates the cosine pole family {1-S_1=0} -> 1 (the SAME mechanism as
     1-Sigma_1; lem:cos covers both).
 (2) The cycle count c is MAGNITUDE-INDEPENDENT (here: c=2 for a=2,4,6,8 at a
     fixed 2-gap pattern) and depends only on the GAP structure between deposits
     and the anchor (bulk_cycle_rule.py: single deposit at edge e with e gaps
     -> c=e; smaller-append ADJACENT deposits -> c=0).
 (3) Therefore the cycle marker y attaches to gap-count, which is DECOUPLED from
     deposit magnitude.  y CANNOT rescale the magnitude-Lambert factors
     1/(1-q^{k+1}); it does NOT turn them into 1/(1-q^{k+1} y).  Hence the
     corrected bulk denominator equals 1-S_1 VERBATIM (y-free).
 => B_U = N_U(q,y)/(1-S_1):  SAME pole family as B_V, modulo the numerator N_U.

FALSIFIED MARKINGS (do NOT retry):
 * Explicit free-gap cells (weight q*y): OVERCOUNTS (block 3,3,11,7 vs 2,2,6,2).
 * gap-bridge kernel K=q^max+q^{a+b} qy/(1-qy): OVERCOUNTS (22 vs 18 at q^5).
 * 'ysingle' (mark the smaller-append 3rd term 2q^{2s} by y): WRONG -- it moves
   the dominant bulk pole 0.6096->0.6277, but FAILS per-element validation:
   smaller-adjacent-append deposits have c=0 (a={0:4,1:2}: relaxed=true=16), so
   the 3rd term carries NO cycle. The pole shift was an artifact of over-marking
   the magnitude ladder.

NET: the cosine bulk family lives in the magnitude ladder, which the (magnitude-
independent) cycle correction provably cannot touch.  No new denominator; the
seam collapses onto the numerator condition N_U(q_m^bulk) != 0, sign-refractory
exactly like lem:numerator.  Conditional on lem:cos AND that numerator condition,
U has poles at the bulk family -> transcendental; this is the SAME conditional
structure as the travel route, not an independent escape.
=============================================================================

SEAM #3: cycle-corrected BULK transfer and its OWN denominator.

GOAL: derive the true-metric bulk block B_U from the validated relaxed bulk catalytic
recursion by inserting the cycle marker y in the CORRECT analytic channel, then ask
whether the corrected denominator (the 1-S_1 analog) ALSO has infinitely many zeros
accumulating at q=1 (cosine oscillation) -> U transcendental DIRECTLY via its own bulk
poles, independent of the travel-numerator question.

VALIDATED RELAXED BULK RECURSION (catalytic, q=x^2; reproduces 0,2,2,6,2,18,6,42,18,118,..):
   F_s = 2q^s + 2q^s sum_{s'>=s} F_{s'} q^{s'} + 2q^{2s} sum_{s'<s} F_{s'},   s>=1.
Telescoped:  G_k = alpha_k (1+G_1) + gamma_k G_{k+2},
   alpha_k = 2q^{k+1}/(1-q^{k+1}),  gamma_k = 2q^{k+2}/(1-q^{k+2}) - 2q^{k+1}/(1-q^{k+1}).
Singularity at S_1(q)=1 (zeros 0.6096,0.9202,0.9690,... -> 1).

CYCLE STRUCTURE (validated bulk_cycle_rule.py / catalytic_funceq.relaxed_len_local):
 - A bulk run is a left-to-right sequence of even deposits a=2s (s>=1) on edges, with
   FORCED gap edges (m=2 -> length q) wherever there is a reachability gap.
 - In the TRUE metric each forced gap edge that lies before a later deposit is an isolated
   2-cycle: +2 length, i.e. an extra factor q (mark y; true = y=q).
 - The gaps live in the SMALLER-OR-FURTHER append: the extra q^{2s} (vs q^s site) in the
   third term encodes the reachability slack.  But the gaps are LENGTH-counted in the
   relaxed recursion already (via 1/(1-q^{m}) Lambert sums that sum geometric gap runs).

We do NOT guess.  We CALIBRATE: build a 1-parameter family of markings and check which
reproduces the TRUE bulk series u_bulk (computed by validated DP), then read its denominator.
"""
import sys, os, importlib.util
from collections import defaultdict
import mpmath as mp
mp.mp.dps=40

HERE=os.path.dirname(os.path.abspath(__file__))
import lamp_lib as LL
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
relaxed_len=cf.relaxed_len_local

# ---------------------------------------------------------------------------
# 1.  TRUE bulk block by validated DP: one-sided run anchored at marker 0 (eps=1,dl=0,k=0).
#     Use a transfer DP over (position, last-deposit-half-size, run-of-gaps) to avoid the
#     exponential product().  State carries TRUE length increment per appended cell.
#     We enumerate deposit SEQUENCES (active s>=1) with explicit gap counts between them.
#     length(relaxed) and c(cycles) are both closed form here so we don't call BFS.
#
#     A right run anchored at site 0:  edge0 deposit (s0>=1), then for each subsequent
#     deposit: g>=0 gap edges (each length 2 relaxed) then a deposit s_i>=1.
#     relaxed_len of such a run (validated formula relaxed_len_local):
#        sum over edges of m_j  +  sum over interior sites of max(|a_{j-1}|,|a_j|).
#     We just CALL relaxed_len_local and LL.solve to be safe (small runs).
# ---------------------------------------------------------------------------
def true_bulk_series(Nmax_len=22, Smax=4, maxgap=6, maxdep=6):
    """Right run anchored at site0. deposits list with gaps. Build V_bulk, U_bulk q-series
    (index = length/2). Enumerate by #deposits d and gap-vector; bounded by length."""
    V=defaultdict(int); U=defaultdict(int)
    # recursive builder over deposits; prune by relaxed length
    sizes=[2*m for m in range(1,Smax+1)]  # |a| even, positive magnitude; sign factor 2 each
    def rec(a, lastedge, ndep):
        # a: dict edge->deposit (magnitude, we add sign multiplicity at the end = 2^ndep)
        if ndep>=1:
            rl=relaxed_len(1,0,0,a); tl=LL.solve(1,0,0,a)
            if rl is not None and tl is not None and rl<=Nmax_len:
                mult=2**ndep  # each deposit has +/- sign
                if rl%2==0: V[rl//2]+=mult
                if tl%2==0: U[tl//2]+=mult
        if ndep>=maxdep: return
        # append next deposit after g gaps
        for g in range(0, maxgap+1):
            nextedge=lastedge+1+g
            for s in sizes:
                a2=dict(a); a2[nextedge]=s
                rl=relaxed_len(1,0,0,a2)
                if rl is None or rl>Nmax_len: continue
                rec(a2, nextedge, ndep+1)
    # first deposit at edge0
    for s in sizes:
        rec({0:s}, 0, 1)
    return V,U

if __name__=="__main__":
    print("Computing TRUE vs RELAXED one-sided bulk block (validated DP, anchored at 0)...")
    V,U=true_bulk_series(Nmax_len=20, Smax=4, maxgap=8, maxdep=7)
    NN=16
    vb=[V.get(n,0) for n in range(NN)]
    ub=[U.get(n,0) for n in range(NN)]
    print("V_bulk (relaxed, q-series):", vb)
    print("U_bulk (true,    q-series):", ub)
    print("d_bulk = V-U             :", [vb[n]-ub[n] for n in range(NN)])
