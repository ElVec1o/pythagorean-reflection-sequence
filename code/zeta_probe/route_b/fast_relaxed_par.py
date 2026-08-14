#!/usr/bin/env python3
"""Parallel driver for fast_relaxed.slice_gf, distributing k-slices over procs."""
import sys, os, time, importlib.util
import multiprocessing as mpx
from collections import defaultdict

HERE=os.path.dirname(os.path.abspath(__file__))
_S=list(sys.argv)
spec=importlib.util.spec_from_file_location("fr",os.path.join(HERE,"fast_relaxed.py"))
fr=importlib.util.module_from_spec(spec); sys.argv=["fr","0"]; spec.loader.exec_module(fr)
sys.argv=_S

N=int(sys.argv[1]) if len(sys.argv)>1 else 40
# Safe deposit cap: an isolated deposit |a|=m costs >=3m (cross m + two sites m),
# so |a|<=N//3 for any element of length<=N.  +2 margin.  Verified identical to
# cap=N at N=24.
CAP=int(sys.argv[2]) if len(sys.argv)>2 else (N//3+2)
NPROC=int(sys.argv[3]) if len(sys.argv)>3 else 10
KMAX=N+1

def work(k):
    loc=defaultdict(int)
    for eps in (1,-1):
        for delta in (0,1):
            gf=fr.slice_gf(eps,delta,k,N,CAP)
            for d,c in gf.items():
                if d<=N: loc[d]+=c
    return dict(loc)

if __name__=="__main__":
    t0=time.time()
    ks=list(range(-KMAX,KMAX+1))
    total=defaultdict(int)
    ctx=mpx.get_context("fork")
    with ctx.Pool(NPROC) as pool:
        for res in pool.imap_unordered(work,ks):
            for d,c in res.items(): total[d]+=c
    seq=[total[n] for n in range(0,N+1)]
    el=time.time()-t0
    print(f"N={N} CAP={CAP} NPROC={NPROC} elapsed {el:.1f}s")
    print("v_n =", seq)
    ref=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,
         12959,19949,30640,46905,71699,109490,166969,254047,386192,586349,
         889599,1347444,2039911,3084135]
    L=min(len(seq),len(ref))
    ok=all(seq[n]==ref[n] for n in range(L))
    print(f"MATCHES reference (first {L}):", ok)
