#!/usr/bin/env python3
"""
gap-A via numpy float64 (memory-light: a 1000x1000 double matrix is 8MB; no mpmath blowup).
Tests whether the CORRECTED bulk dressing B_U(q_m) is FINITE & NONZERO at the travel poles q_m
(roots of Sigma_1=1), which is exactly gap-A. Corrected gap kernel g = q/(1-qy); broken (qy)/(1-qy).
For U we set y=q. If B_U finite & nonzero at every q_m, the secondary poles of U are genuine
(=> pole accumulation => natural boundary => transcendence), with the CORRECT connectivity.
"""
import sys, math
import numpy as np

def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(q,J=20000,k=1):
    tot=0.0; prod=1.0
    for j in range(J):
        kk=k+2*j
        tot+=Aq(kk,q)*prod; prod*=Cq(kk,q)
        if abs(prod)<1e-18 and j>40: break
    return tot
def travel_poles(n):
    poles=[]; wv=3.0; prev=None; qprev=None; step=0.01
    while len(poles)<n and wv<400:
        tau=2/(wv*wv); q=math.exp(-tau); val=Sig_t(q)-1
        if prev is not None and prev*val<0:
            lo,hi=qprev,q
            for _ in range(80):
                mid=(lo+hi)/2
                if (Sig_t(lo)-1)*(Sig_t(mid)-1)<=0: hi=mid
                else: lo=mid
            r=(lo+hi)/2
            if 0<r<1 and all(abs(r-p)>1e-12 for p in poles): poles.append(r)
        prev=val; qprev=q; wv+=step
    return sorted(poles)

def bulk_block(q,y,corrected,cap=2000):
    Smax=min(cap, max(60, int(math.ceil(40/(1-q)))))
    g = q/(1-q*y) if corrected else (q*y)/(1-q*y)
    n=Smax
    w=np.arange(1,n+1, dtype=np.float64)
    qa=q**w                       # q^a
    # M[b-1,a-1] = 2 q^b (q^max(a,b) + q^{a+b} g)
    A=w[None,:]; B=w[:,None]
    QmaxAB=q**np.maximum(A,B)
    Qab=q**(A+B)
    M=2*(q**B)*(QmaxAB+Qab*g)
    E=2*qa
    try:
        P=np.linalg.solve(np.eye(n)-M, E)
    except np.linalg.LinAlgError:
        return float('inf')
    return float(P.sum())

def bulk_poles(corrected, qhi=0.97, nmax=6):
    out=[]; qprev=None; vprev=None; q=0.30; step=0.005
    while q<qhi and len(out)<nmax:
        b=bulk_block(q,q,corrected)
        v=1.0/b if (b==b and abs(b)>1e-300) else float('nan')
        if vprev is not None and v==v and vprev==vprev and vprev*v<0:
            lo,hi=qprev,q
            for _ in range(60):
                mid=(lo+hi)/2
                bm=bulk_block(mid,mid,corrected); vm=1.0/bm if abs(bm)>1e-300 else float('nan')
                blo=bulk_block(lo,lo,corrected); vlo=1.0/blo if abs(blo)>1e-300 else float('nan')
                if vlo*vm<=0: hi=mid
                else: lo=mid
            out.append((lo+hi)/2)
        vprev=v; qprev=q; q+=step
    return out

if __name__=="__main__":
    NP=int(sys.argv[1]) if len(sys.argv)>1 else 6
    tp=travel_poles(NP)
    print("travel poles q_m (Sigma_1=1):")
    for i,p in enumerate(tp): print(f"   q_{i}= {p:.10f}")
    bpc=bulk_poles(True); bpb=bulk_poles(False)
    print("bulk poles at y=q (B_U diverges):")
    print("   corrected-c:", [f"{x:.6f}" for x in bpc])
    print("   broken-c   :", [f"{x:.6f}" for x in bpb])
    print()
    print("B_U(q_m) at each travel pole (corrected c, y=q_m). gap-A holds iff all FINITE & NONZERO:")
    print(f"{'m':>2} {'q_m':>13} {'B_U_corrected':>16} {'|1-S1bulk gap|=dist to nearest bulk pole':>20}")
    ok=True
    for i,qm in enumerate(tp):
        B=bulk_block(qm,qm,True)
        dist=min([abs(qm-bp) for bp in bpc], default=float('nan'))
        finite = (B==B) and abs(B)<1e8
        nonzero= abs(B)>1e-8
        if not(finite and nonzero): ok=False
        print(f"{i:>2} {qm:>13.9f} {B:>16.6g}   nearest bulk pole dist={dist:.5f}  {'OK' if finite and nonzero else 'PROBLEM'}")
    print()
    print("RESULT:", "gap-A HOLDS with corrected c (B_U finite & nonzero at all computed travel poles)" if ok
          else "gap-A FAILS at some pole -- bulk/travel pole coincidence")
