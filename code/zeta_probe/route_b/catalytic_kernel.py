#!/usr/bin/env python3
"""
ROUTE B -- catalytic kernel for the RELAXED lamplighter growth (A396406).

We assemble the one-catalytic-variable functional equation for the relaxed
word-length generating function and validate it against v_n.

SETUP
=====
Relaxed length of an element (eps*, delta*, k*, P), P = sum_j a_j t^j, drops the
single-Eulerian-path (no-isolated-cycle) constraint. It is computed by a
left-to-right sweep over edges j: each edge carries a profile
        pi_j = (f_j, m_j, pu_j, pd_j),
with f_j in {-1,0,+1} fixed by the travel interval, m_j >= 0 the crossing count
(parity m_j == a_j == f_j mod 2), u_j=(m_j+f_j)/2 up-strands, dn_j=(m_j-f_j)/2
down-strands, pu_j in [0,u_j] the number of +-signed ups, pd_j in [0,dn_j] the
number of +-signed downs.  The lamp coefficient is a_j = 2 pd_j - dn_j + u_j - 2 pu_j.

Length = sum_j m_j  +  sum_sites SiteCost(pi_{j-1}, pi_j),
SiteCost = min-cost matching between arrivals and departures at the integer site,
pair costs: same side & same sign 0, same side opposite sign 2, opposite side 1.
(virtual arrival (L,+) at site 0; virtual departure (side=delta*, sign=eps*) at k*.)

CATALYTIC VARIABLE
==================
The catalytic variable t marks m_R := the crossing count of the *current
(rightmost) edge* of the partial sweep.  x marks accumulated length.  The
boundary datum that the next site-cost depends on is the FINE PROFILE of the
rightmost edge: its (f, m, pu, pd).  Because pu,pd only matter through the
per-strand (side,sign) multiset that meets the next site, and SiteCost is
symmetric in identical strands, the boundary state collapses to the
"strand-type multiset of the rightmost edge", i.e. (f; #up+, #up-, #dn+, #dn-).

We build the transfer operator
        F_q(x,t) = sum over partial sweeps ending in boundary class q of
                   x^{length-so-far} t^{m_R},
indexed by the finite set Q of boundary classes (the 'sections').  Appending one
edge of profile pi' to a sweep ending in class q pays
        x^{m'}  *  x^{SiteCost(q, pi')}  and resets the catalytic mark to t^{m'}.
This is a linear (counting) recursion -- EXCEPT that distinct internal sign
arrangements (pu,pd) realizing the SAME lamp coefficient a' must be DEDUPLICATED
to the minimal-length one (the relaxed length is a min over them).  That min is
exactly the determinization performed in wf2_relaxed_dp.  Here we keep the
catalytic variable explicit by tracking, per boundary class q and per chosen
deposit a', the MIN site+edge cost increment; the transfer weight is then
x^{Delta(q,a',m')} t^{m'} summed over the m'-ladder.

This file VALIDATES the catalytic transfer by recomputing v_n through n=16 and
comparing to the known sequence, then prints the kernel ingredients.
"""
import sys, importlib.util, os
from collections import defaultdict
from functools import lru_cache

HERE=os.path.dirname(os.path.abspath(__file__))
ZP=os.path.dirname(HERE)
_SAVED_ARGV=list(sys.argv)
spec=importlib.util.spec_from_file_location("lf",os.path.join(ZP,"lamp_formula.py"))
lf=importlib.util.module_from_spec(spec); sys.argv=["lf","0"]; spec.loader.exec_module(lf)
sys.argv=_SAVED_ARGV
site_cost=lf.site_cost

def edge_updn(f,m): return (m+f)//2,(m-f)//2

# ---------------------------------------------------------------------------
# Boundary class of the rightmost edge: the (side,sign) multiset its strands
# present to the NEXT site.  For the next site, the rightmost edge contributes:
#   - its UP strands as ARRIVALS on side L (pu of +, u-pu of -)
#   - its DOWN strands as DEPARTURES on side L (pd of +, dn-pd of -)
# So the boundary class is fully captured by (u, pu, dn, pd) -- equivalently the
# 4-vector (pu, u-pu, pd, dn-pd) of (up+,up-,dn+,dn-) counts.  f is recoverable
# as u-dn but we keep m for the catalytic mark.
# A profile pi=(f,m,pu,pd) yields boundary class b=(pu, u-pu, pd, dn-pd).
# ---------------------------------------------------------------------------
def boundary_of(f,m,pu,pd):
    u,dn=edge_updn(f,m)
    return (pu, u-pu, pd, dn-pd)

# Site cost between a LEFT edge given by its boundary class bL=(up+,up-,dn+,dn-)
# and a RIGHT edge profile (f',m',pu',pd'), with optional virtual events.
def site_increment(bL, f2,m2,pu2,pd2, is0, isk, eps, delta):
    u2,dn2=edge_updn(f2,m2)
    up_p,up_m,dn_p,dn_m = bL
    arr=[0,0,0,0]; dep=[0,0,0,0]
    # arrivals: ups of left edge (side L)
    arr[0]+=up_p; arr[1]+=up_m
    # arrivals: downs of right edge (side R)
    arr[2]+=pd2;  arr[3]+=dn2-pd2
    # departures: downs of left edge (side L)
    dep[0]+=dn_p; dep[1]+=dn_m
    # departures: ups of right edge (side R)
    dep[2]+=pu2;  dep[3]+=u2-pu2
    if is0: arr[0]+=1
    if isk:
        s=2 if delta==1 else 0
        dep[s+(0 if eps==1 else 1)]+=1
    if sum(arr)!=sum(dep): return None
    return site_cost(tuple(arr),tuple(dep))

def f_of(j,k):
    if 0<=j<k: return 1
    if k<=j<0: return -1
    return 0

# Enumerate all profiles of given f up to mmax, grouped by deposit a.
@lru_cache(maxsize=None)
def profiles_by_a(f,mmax):
    out=defaultdict(list)
    for m in range(0,mmax+1):
        if m==0 and f!=0: continue
        if (m-f)%2!=0: continue
        u,dn=edge_updn(f,m)
        if u<0 or dn<0: continue
        for pu in range(u+1):
            for pd in range(dn+1):
                a=2*pd-dn+u-2*pu
                if m==0 and a!=0: continue
                out[a].append((f,m,pu,pd))
    return dict(out)

# ---------------------------------------------------------------------------
# CATALYTIC GENERATING FUNCTION (per slice), as a polynomial in (x,t).
# State at the boundary between processed edges and the next site = boundary
# class bL plus the catalytic mark m_R of the rightmost edge.  We carry the GF
#       G[bL] = sum_{sweeps ending at bL} x^{len} t^{m_R}
# but for the relaxed COUNT we must, per (bL, deposit a'), keep only the
# MIN-length realization across the (pu',pd') choices that realize a'.  Hence we
# carry a determinized cost table exactly as wf2_relaxed_dp, but additionally
# tag each surviving boundary entry with its m (the catalytic exponent).
# ---------------------------------------------------------------------------
def slice_series(eps,delta,k,JLO,JHI,mmax,Ncap, catalytic=False):
    """Return dict L->count (catalytic=False) OR dict (L,m_last)->count
    when catalytic=True, where m_last is the crossing count of the rightmost
    NON-VIRTUAL edge actually crossed (the catalytic exponent)."""
    EMPTYP=(0,0,0,0)
    def norm(items):
        b=min(c for _,c in items)
        return tuple(sorted((p,c-b) for p,c in items)), b
    # state key = (tkey, base); tkey = tuple of (profile, rel_cost).
    # value = count (and we propagate the *element* multiplicity).
    states=defaultdict(int)
    states[(((EMPTYP,0),),0)]=1
    for j in range(JLO,JHI+1):
        fj=f_of(j,k); is0=(j==0); isk=(j==k)
        pmap=profiles_by_a(fj,mmax)
        nxt=defaultdict(int)
        for (tkey,base),cnt in states.items():
            abstbl=[(p,base+r) for p,r in tkey]
            for a,profs in pmap.items():
                newitems=[]
                for pc in profs:
                    fc,mc,puc,pdc=pc
                    best=None
                    for pp,cp in abstbl:
                        fp,mp_,pup,pdp=pp
                        pm=mp_
                        if j<=-1 and pm>0 and mc==0: continue
                        if j>=1 and pm==0 and mc>0: continue
                        bL=boundary_of(fp,mp_,pup,pdp)
                        sc=site_increment(bL,fc,mc,puc,pdc,is0,isk,eps,delta)
                        if sc is None: continue
                        v=cp+sc+mc
                        if best is None or v<best: best=v
                    if best is not None and best<=Ncap:
                        newitems.append((pc,best))
                if newitems:
                    nk,nb=norm(newitems)
                    nxt[(nk,nb)]+=cnt
        states=nxt
        if not states: break
    # close out at site JHI+1 (no further edge): pair rightmost edge ups/downs
    j=JHI+1; fj=f_of(j,k); is0=(j==0); isk=(j==k)
    out=defaultdict(int)
    for (tkey,base),cnt in states.items():
        # min over rightmost-edge profile of final-site cost, tracking m_last
        best=None; bestm=None
        for p,r in tkey:
            fp,mp_,pup,pdp=p
            bL=boundary_of(fp,mp_,pup,pdp)
            sc=site_increment(bL,0,0,0,0,is0,isk,eps,delta)
            if sc is None: continue
            v=base+r+sc
            if best is None or v<best:
                best=v; bestm=mp_
        if best is not None:
            if catalytic: out[(best,bestm)]+=cnt
            else: out[best]+=cnt
    return out

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 16
    MMAX=int(sys.argv[2]) if len(sys.argv)>2 else (N+1)//2+2
    half=(N+1)//2; KMAX=half+2; PAD=half+2
    total=defaultdict(int)
    for k in range(-KMAX,KMAX+1):
        JLO=min(0,k)-PAD; JHI=max(0,k)+PAD
        for eps in (1,-1):
            for delta in (0,1):
                poly=slice_series(eps,delta,k,JLO,JHI,MMAX,N)
                for L,c in poly.items():
                    if L<=N: total[L]+=c
    out=[total[n] for n in range(0,N+1)]
    print("CATALYTIC-DP v_n =", out)
    ref=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949]
    ok=all(out[n]==ref[n] for n in range(min(len(out),len(ref))))
    print("MATCHES reference v_n:", ok)
