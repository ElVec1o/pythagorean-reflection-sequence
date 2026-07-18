"""Run the validated mod-p engine over several primes, CRT, and rationally reconstruct A_n."""
import subprocess, sys, json, time
from fractions import Fraction as Fr
def isprime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
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
def crt(rs,ms):
    R,M=rs[0],ms[0]
    for r,m in zip(rs[1:],ms[1:]):
        g=pow(M%m,m-2,m)
        t=((r-R)%m)*g%m
        R+=M*t; M*=m
    return R%M,M
def ratrec(a,M):
    """rational reconstruction: find p/q = a mod M with |p|,q <= sqrt(M/2)"""
    import math
    bound=math.isqrt(M//2)
    r0,r1=M,a%M; s0,s1=0,1
    while r1>bound:
        q=r0//r1
        r0,r1=r1,r0-q*r1
        s0,s1=s1,s0-q*s1
    if s1==0 or abs(s1)>bound: return None
    return Fr(r1 if s1>0 else -r1, abs(s1))
order=int(sys.argv[1]); kmax=int(sys.argv[2])
ps=primes_below((1<<62)-1,kmax)
vals={}
t0=time.time()
for i,p in enumerate(ps):
    out=subprocess.run(['python3','engine_modp.py',str(p),str(order)],capture_output=True,text=True)
    if out.returncode: print("engine failed at p=",p,out.stderr[-300:]); break
    vals[p]=[int(x) for x in out.stdout.split()]
    print(f"  prime {i+1}/{kmax} done ({time.time()-t0:.0f}s elapsed)",flush=True)
    # attempt reconstruction with the primes so far
    if i>=3:
        got=[];okall=True
        for n in range(order):
            rs=[vals[q][n] for q in ps[:i+1]]; ms=ps[:i+1]
            R,M=crt(rs,ms); fr=ratrec(R,M)
            if fr is None: okall=False; break
            got.append(fr)
        if okall:
            # stability check: same reconstruction with one fewer prime
            got2=[]
            for n in range(order):
                rs=[vals[q][n] for q in ps[:i]]; ms=ps[:i]
                R,M=crt(rs,ms); fr=ratrec(R,M)
                got2.append(fr)
            if got==got2:
                print(f"  RECONSTRUCTION STABLE with {i+1} primes")
                json.dump({"order":order,"num":[str(x.numerator) for x in got],"den":[str(x.denominator) for x in got]},open(f"A_exact_order{order}.json","w"))
                print("  saved A_exact_order%d.json"%order)
                break
print("total %.0fs"%(time.time()-t0))
