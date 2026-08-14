#!/usr/bin/env python3
"""Enumerate group elements by deposit config (bounded), compute TRUE and RELAXED
length via the validated solvers, and find genuine defects (true>relaxed).
Then characterize them: do they ever involve a TRAVEL interval, or are they all
pure-BULK (k=0 or bulk-only)?  This tells us whether the defect touches the
travel block (the pole generator)."""
import sys, os, importlib.util
import defect_locate as dl
from itertools import product
from collections import defaultdict

# Enumerate canonical group elements (eps,delta,k; a) with bounded support/mag,
# dedupe by the element identity (eps,delta,k, frozenset of nonzero deposits).
def enum_elements(krange, sites, mags):
    seen=set()
    for k in krange:
        for eps in (1,-1):
            for delta in (0,1):
                # element identity depends on (eps,delta,k,a); but eps,delta only
                # matter when k has certain parity. We enumerate all and dedupe.
                for vals in product(mags, repeat=len(sites)):
                    a={sites[i]:vals[i] for i in range(len(sites)) if vals[i]!=0}
                    key=(eps,delta,k,tuple(sorted(a.items())))
                    if key in seen: continue
                    seen.add(key)
                    yield eps,delta,k,a

if __name__=="__main__":
    NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 12
    sites=list(range(-2,5))
    mags=[-2,-1,0,1,2]
    krange=range(-3,5)
    defects=defaultdict(int)        # true_len -> count of defect elements
    travel_defects=0; bulk_defects=0
    examples=[]
    cnt=0
    for eps,delta,k,a in enum_elements(krange,sites,mags):
        t=dl.true_len(eps,delta,k,a)
        if t is None or t>NMAX: continue
        r=dl.relaxed_len(eps,delta,k,a)
        if r is None: continue
        cnt+=1
        if t>r:
            defects[t]+=1
            has_travel=(k!=0)
            if has_travel: travel_defects+=1
            else: bulk_defects+=1
            if len(examples)<15:
                examples.append((eps,delta,k,dict(a),r,t))
    print(f"enumerated {cnt} elements with true_len<={NMAX}")
    print(f"defect elements: travel(k!=0)={travel_defects}  bulk(k=0)={bulk_defects}")
    print("defect count by TRUE length:", dict(sorted(defects.items())))
    print("examples (eps,delta,k,a,relaxed,true):")
    for x in examples: print("  ",x)
