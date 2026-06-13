#!/usr/bin/env python3
# Parallel relaxed v_n: distribute (k) slices across processes.
import sys, time, os
import multiprocessing as mpx
_ARGV=list(sys.argv)
_HERE=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(_HERE,"wf2_relaxed_dp.py")).read().split('if __name__')[0])
from collections import defaultdict

N=int(_ARGV[1]) if len(_ARGV)>1 else 24
MMAX=int(_ARGV[2]) if len(_ARGV)>2 else (N+1)//2+2
NPROC=int(_ARGV[3]) if len(_ARGV)>3 else 8
half=(N+1)//2
KMAX=half+2; PAD=half+2

def work(k):
    loc=defaultdict(int)
    JLO=min(0,k)-PAD; JHI=max(0,k)+PAD
    for eps in (1,-1):
        for delta in (0,1):
            poly=slice_poly(eps,delta,k,JLO,JHI,MMAX,N)
            for L,c in poly.items():
                if L<=N: loc[L]+=c
    return dict(loc)

if __name__=="__main__":
    t0=time.time()
    ks=list(range(-KMAX,KMAX+1))
    total=defaultdict(int)
    ctx=mpx.get_context("fork")
    with ctx.Pool(NPROC) as pool:
        for res in pool.imap_unordered(work, ks):
            for L,c in res.items(): total[L]+=c
    out=[total[n] for n in range(0,N+1)]
    print(f"N={N} MMAX={MMAX} elapsed {time.time()-t0:.1f}s")
    print("RELAXED v_n =", out)
