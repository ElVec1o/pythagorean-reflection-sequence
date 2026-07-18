"""Parallel mod-p + CRT reconstruction of A_1..A_order."""
import subprocess, sys, json, time, os
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Fr
def isprime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def primes_below(start,k):
    out=[];n=start
    while len(out)<k:
        if isprime(n): out.append(n)
        n-=2
    return out
def work(args):
    p,order=args
    out=subprocess.run(['python3','engine_modp.py',str(p),str(order)],capture_output=True,text=True)
    if out.returncode: return (p,None)
    return (p,[int(x) for x in out.stdout.split()])
def crt(rs,ms):
    R,M=rs[0],ms[0]
    for r,m in zip(rs[1:],ms[1:]):
        t=((r-R)%m)*pow(M%m,m-2,m)%m
        R+=M*t; M*=m
    return R%M,M
def ratrec(a,M):
    import math
    bound=math.isqrt(M//2)
    r0,r1=M,a%M; s0,s1=0,1
    while r1>bound:
        q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    if s1==0 or abs(s1)>bound: return None
    return Fr(r1 if s1>0 else -r1, abs(s1))
if __name__=="__main__":
    order=int(sys.argv[1]); k=int(sys.argv[2]); W=int(sys.argv[3])
    ps=primes_below((1<<62)-1,k)
    t0=time.time()
    vals={}
    with ProcessPoolExecutor(max_workers=W) as ex:
        for p,v in ex.map(work,[(p,order) for p in ps]):
            if v is None: print("FAILED at",p,flush=True); continue
            vals[p]=v
            print(f"  {len(vals)}/{k} primes ({time.time()-t0:.0f}s)",flush=True)
    ok=sorted(vals)
    for use in range(4,len(ok)+1):
        got=[]
        for n in range(order):
            R,M=crt([vals[q][n] for q in ok[:use]],ok[:use])
            fr=ratrec(R,M)
            if fr is None: got=None; break
            got.append(fr)
        if got is None: continue
        prev=[]
        for n in range(order):
            R,M=crt([vals[q][n] for q in ok[:use-1]],ok[:use-1])
            prev.append(ratrec(R,M))
        if got==prev:
            print(f"STABLE with {use} primes")
            json.dump({"order":order,"num":[str(x.numerator) for x in got],"den":[str(x.denominator) for x in got]},open(f"A_exact_order{order}.json","w"))
            print("saved"); break
    else: print("NOT stable -- need more primes")
    print("total %.0fs"%(time.time()-t0))
