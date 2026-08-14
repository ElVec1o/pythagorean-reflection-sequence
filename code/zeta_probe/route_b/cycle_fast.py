#!/usr/bin/env python3
"""
FAST cycle locator via deposit-vector enumeration (no BFS, no per-element
permutation DP over the whole element).  We use the validated solvers from
conn_kernel.solve(eps,dl,k,a,splice): splice=0 -> relaxed_len v, splice=2 ->
true_len u, exactly.  c(g) = (u-v)/2.

We enumerate canonical group elements directly by their encoding (eps,delta,k;a)
with a length cap, instead of BFS.  An element of relaxed length <= N has
  sum_j |a_j| + |k| + (site/boundary costs) <= N,
so |k| <= N and sum |a_j| <= N.  We enumerate deposit vectors a on a bounded
window of sites with sum|a_j| <= N-|k|.  Each (eps,delta,k;a) is ONE element;
we compute v=solve(...,0), u=solve(...,2); if u>v we record location.

This is the SAME element set as BFS (canonical normal form), just enumerated by
encoding -- far fewer expensive calls because we cap aggressively.
"""
import sys, itertools
sys.path.insert(0,'/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b')
from conn_kernel import solve
from collections import Counter, defaultdict

U=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683]
V=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949]

def gen_deposits(window, budget):
    """yield dicts a: site->nonzero int, with sum|a|<=budget, over sites in window."""
    # represent as list over window positions; each can be 0 or +-1,+-2,...
    sites=list(window)
    n=len(sites)
    def rec(i, remaining, cur):
        yield dict(cur)
        if i>=n: return
        for v in range(1, remaining+1):
            for s in (v,-v):
                cur[sites[i]]=s
                yield from rec(i+1, remaining-v, cur)
            cur.pop(sites[i],None)
        # also skip site i with 0 (already covered by yielding then recursing on i+1 with 0)
        yield from rec(i+1, remaining, cur)
    # dedupe via set of frozenset items
    seen=set()
    for d in rec(0,budget,{}):
        key=tuple(sorted(d.items()))
        if key in seen: continue
        seen.add(key)
        yield d

def main(N):
    cyc=[]
    vN=defaultdict(int); uN=defaultdict(int)
    seen=set()
    for k in range(-N, N+1):
        K0,K1=min(0,k),max(0,k)
        budget=N-abs(k)
        if budget<0: continue
        # window of sites where lamp deposits can be nonzero: within [K0-pad,K1+pad]
        pad=budget//1+1
        window=range(K0-pad, K1+pad+1)
        for a in gen_deposits(window, budget):
            for eps in (1,-1):
                for delta in (0,1):
                    key=(eps,delta,k,tuple(sorted(a.items())))
                    if key in seen: continue
                    seen.add(key)
                    v=solve(eps,delta,k,a,0)
                    if v is None or v>N: continue
                    u=solve(eps,delta,k,a,2)
                    vN[v]+=1; uN[u]+=1
                    if u is not None and u>v:
                        c=(u-v)//2
                        supp=sorted(j for j in a if a[j]!=0)
                        cyc.append((v,u,c,eps,delta,k,supp,K0,K1,dict(a)))
    Uc=[uN.get(n,0) for n in range(N+1)]
    Vc=[vN.get(n,0) for n in range(N+1)]
    print("u_n:",Uc,"  match:",Uc==U[:N+1])
    print("v_n:",Vc,"  match:",Vc==V[:N+1])
    print("d_n:",[Vc[n]-Uc[n] for n in range(N+1)])
    print(f"\n# cycle-bearing elements: {len(cyc)}")
    by_travel=Counter(); overlap=Counter()
    for v,u,c,eps,delta,k,supp,K0,K1,a in cyc:
        by_travel['k=0(no travel)' if k==0 else 'k!=0(travel)']+=1
        if not supp: overlap['lamp-empty']+=1
        else:
            inside=[j for j in supp if K0<=j<K1]; outside=[j for j in supp if j<K0 or j>=K1]
            if inside and outside: overlap['straddle']+=1
            elif inside: overlap['lamp-inside-travel']+=1
            else: overlap['lamp-outside-travel(pure-bulk)']+=1
    print("by travel:",dict(by_travel))
    print("lamp vs travel:",dict(overlap))
    cyc.sort()
    print("\nsmallest cycle elements:")
    for v,u,c,eps,delta,k,supp,K0,K1,a in cyc[:25]:
        print(f"  v={v} u={u} c={c} | eps={eps} dl={delta} k={k} travel=[{K0},{K1}) a={a}")

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 11
    main(N)
