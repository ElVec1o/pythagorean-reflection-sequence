#!/usr/bin/env python3
"""
Derive the cycle-weighted bulk-block telescoping with EXPLICIT gap edges, and analytically
continue it (so it is valid at travel poles q_n -> 1, beyond the bulk series radius).

Model (bulk run, catalytic mark t for the last edge's half-size; q=x^2):
 Edges left-to-right, each ACTIVE half-size s>=1 (weight 2 q^s, two signs) or GAP s=0
 (weight q*y).  Site coupling between consecutive half-sizes w,w': q^{max(w,w')}.

Catalytic GF F(t) = sum over runs of weight * t^{w_last}.  We want G_k=F(q^k) telescoped.
Let P_w = sum over runs ENDING in half-size w of weight (so F(t)=sum_w P_w t^w).
Section identity (append edge w' to any run, or start fresh):
   P_{w'} = e(w') * ( 1 + sum_w P_w q^{max(w,w')} ),   e(w')=2q^{w'} (w'>=1), q*y (w'=0).
Split sum at w=w':  sum_w P_w q^{max(w,w')} = q^{w'} sum_{w<=w'} P_w + sum_{w>w'} P_w q^{w}.
Define cumulative  Below(w')=sum_{w<=w'} P_w,  Above(w')=sum_{w>w'} P_w q^{w}.
This is the same structure as the seed but with the extra w'=0 (gap) term carrying weight
q*y.  We unfold via G_k = F(q^k) = sum_w P_w q^{k w}.  Multiply section id by q^{k w'} and sum:

  G_k = sum_{w'} e(w') q^{k w'} ( 1 + q^{w'} sum_{w<=w'}P_w + sum_{w>w'}P_w q^w )

This couples through the cumulative sums; the seed handles the s>=1 part. The gap term
(w'=0) adds  e(0) q^{0} (1 + sum_{w<=0}P_w + sum_{w>0}P_w q^w) = q*y*(1 + P_0 + sum_{w>=1}P_w q^w).
Let me just solve the LINEAR system for P_w on a truncated range but using a HIGH Smax with
ANALYTIC CONTINUATION via the telescoped seed for the active part, and treat the gap as a
rank-1 coupling.  Cleanest: compute the seed (gapless, y irrelevant) block exactly via S_k,
then add gaps perturbatively?  No -- gaps are essential (defect starts at the first gap).

ALTERNATIVE CLEAN ROUTE: gaps only ever sit BETWEEN active deposits or between an active
deposit and a marker.  A maximal gap-block of length L between two active half-sizes wL,wR
(or a marker) contributes a factor: each gap edge pays q (crossing) * y (cycle) and the site
couplings q^{max(...)} = q^{wL} on its left-join, q over the gap interior (max(0,0)=0 ->q^0=1!),
q^{wR} on its right-join.  Wait: site coupling between two GAP edges (both half-size 0) is
q^{max(0,0)}=q^0=1.  So an interior gap-block of length L costs (q*y)^L * (interior sites
q^0=1 each).  Joins: q^{wL} (site between left active and first gap) and q^{wR} (site between
last gap and right active).  These joins are ALREADY counted as q^{max(wL,0)}=q^{wL} etc.

So a gap-block of length L>=1 between active sizes wL,wR contributes the SCALAR factor
   Phi_L(q,y) = (q y)^L            [edge weights]  * 1^{L-1}  [interior sites, q^0]
and the joining site costs q^{wL}, q^{wR} are part of the normal transfer.  Crucially the
gap-block transfer is DIAGONAL in nothing -- it just inserts a scalar (qy)^L and connects
wL to wR with site costs q^{wL} (left) and q^{wR}(right).  Summing over L>=0:
   gap-bridge(wL,wR) = q^{wL} * [ sum_{L>=1} (qy)^L ] * q^{wR} ... for L>=1 gaps, PLUS the
   L=0 (no gap, direct adjacency) which is the normal site q^{max(wL,wR)}.
Hmm, the site between adjacent ACTIVE edges is q^{max(wL,wR)}, NOT q^{wL+wR}.  Only when a
gap separates them do the joins factor as q^{wL}*q^{wR}.  So:
   transfer(wL -> wR) = q^{max(wL,wR)}              [adjacent, no gap]
                      + q^{wL} ( sum_{L>=1}(qy)^L ) q^{wR}   [L>=1 gaps between]
                      = q^{max(wL,wR)} + q^{wL+wR} * (qy)/(1-qy).
This is the EXACT cycle-weighted transfer kernel!  At y=1: q^{max}+q^{wL+wR} q/(1-q).
Let me VERIFY this reproduces the relaxed bulk series at y=1, then continue to travel poles.
"""
import mpmath as mp
mp.mp.dps=40

def block_via_kernel(q,y,Smax=80):
    # sizes w>=1 (active). Start/end attach to marker (treat marker as size 0 with its own joins).
    # P_w = e(w)*(seed_w + sum_{w'} P_{w'} K(w',w)), e(w)=2q^w,
    #   seed_w = attachment from the marker (left boundary): marker acts like a size-0 anchor;
    #   the first active edge w pays its edge weight and a left-join to the marker.
    # For a clean BLOCK (run not necessarily touching marker on left), seed_w=1 (run can start
    # at w). Block = sum_w P_w (+ contributions of pure-gap runs, negligible/boundary).
    # Kernel between active sizes:
    #   K(a,b) = q^{max(a,b)} + q^{a+b} * (q*y)/(1-q*y)
    sizes=list(range(1,Smax+1))
    n=len(sizes); idx={w:i for i,w in enumerate(sizes)}
    g=(q*y)/(1-q*y)
    E=mp.matrix(n,1)
    for w in sizes: E[idx[w],0]=2*q**w
    M=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            K=q**max(a,b)+q**(a+b)*g
            M[idx[b],idx[a]]=2*q**b*K   # P_b gets e(b)*K(a,b)*P_a
    P=mp.lu_solve(mp.eye(n)-M,E)
    return sum(P[i,0] for i in range(n))

# relaxed seed block S0/(1-S1) for comparison
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=800):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>25: break
    return tot

if __name__=="__main__":
    for q in [mp.mpf('0.2'),mp.mpf('0.3'),mp.mpf('0.4'),mp.mpf('0.5')]:
        bk=block_via_kernel(q,mp.mpf(1))
        seed=Sb(0,q)/(1-Sb(1,q))
        print(f"q={q}: kernel-block(y=1)={mp.nstr(bk,12)}  seed S0/(1-S1)={mp.nstr(seed,12)}  match={abs(bk-seed)<mp.mpf(10)**(-8)}")
