#!/usr/bin/env python3
"""
gap-A, MEMORY-LIGHT. Only small-q evaluations (Smax hard-capped) -> safe.
Compares the bulk-dressing pole at y=q under the BROKEN vs CORRECTED gap kernel:
   broken    g = (qy)/(1-qy)      (every gap edge = +1 cycle)
   corrected g = q/(1-qy)         (first edge of each interior run FREE -> validated c)
and evaluates B_U at the dominant travel pole q0. Bulk poles sit at q<0.65 so Smax<=140.
"""
import sys
import mpmath as mp
mp.mp.dps=30
CAP=140

def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(q,J=6000,k=1):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-40) and j>40: break
    return tot
q0=mp.findroot(lambda q: Sig_t(q)-1, mp.mpf('0.45'))

def gap_broken(q,y):  return (q*y)/(1-q*y)
def gap_correct(q,y): return q/(1-q*y)

def bulk_block(q,y,gfn):
    Smax=min(CAP, max(50, int(mp.ceil(40/(1-q)))))
    g=gfn(q,y); n=Smax
    E=mp.matrix(n,1); M=mp.matrix(n,n)
    for w in range(1,n+1): E[w-1,0]=2*q**w
    for a in range(1,n+1):
        for b in range(1,n+1):
            M[b-1,a-1]=2*q**b*(q**max(a,b)+q**(a+b)*g)
    P=mp.lu_solve(mp.eye(n)-M,E)
    return sum(P[i,0] for i in range(n))

def bulk_pole(gfn):
    qprev=None; vprev=None; q=mp.mpf('0.30'); step=mp.mpf('0.01')
    while q<mp.mpf('0.66'):
        try: v=1/bulk_block(q,q,gfn)
        except Exception: v=mp.mpf('nan')
        if vprev is not None and not mp.isnan(v) and not mp.isnan(vprev) and vprev*v<0:
            return mp.findroot(lambda z: 1/bulk_block(z,z,gfn),(qprev+q)/2)
        vprev=v; qprev=q; q+=step
    return None

if __name__=="__main__":
    print(f"dominant travel pole  q0 = {mp.nstr(q0,12)}   (beta2 = 1/sqrt(q0) = {mp.nstr(1/mp.sqrt(q0),10)})")
    print("relaxed bulk pole (y=1, S1_bulk=1) q_b ~ 0.6096 (reference)")
    pb=bulk_pole(gap_broken); pc=bulk_pole(gap_correct)
    print(f"BULK pole at y=q (U):  broken-c -> q={mp.nstr(pb,10) if pb else None}    corrected-c -> q={mp.nstr(pc,10) if pc else None}")
    print()
    for name,g in [('broken',gap_broken),('corrected',gap_correct)]:
        B=bulk_block(q0,q0,g)
        print(f"B_U(q0) [{name:9s}] = {mp.nstr(B,10)}   finite&nonzero={abs(B)>mp.mpf(10)**-10 and abs(B)<mp.mpf(10)**10}")
    print()
    print("Reading: q0 < both bulk poles => dominant pole of U is below the bulk pole => B_U(q0)")
    print("finite (dominant residue OK). Whether the CORRECTED bulk pole sits among the secondary")
    print("travel poles q_m (m>=1, all >0.9) is the gap-A asymptotic question (needs telescoped form).")
