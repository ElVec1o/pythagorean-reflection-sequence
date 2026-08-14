#!/usr/bin/env python3
"""
gap-A with the CORRECTED connectivity penalty.
The bulk-dressing transfer kernel is K(a,b)=q^{max(a,b)} + q^{a+b}*g(q,y), where an interior
gap-run of length L contributes its q-edges and y-cycles:
   BROKEN  c: every gap edge = +1 cycle  -> run weight (qy)^L -> g = (qy)/(1-qy)
   CORRECT c: first edge of each run FREE -> run weight q^L y^{L-1} -> g = q/(1-qy)
For the TRUE series U=W(x,x^2) we evaluate the bulk at y = q (=x^2). The transcendence
argument (pole accumulation) needs B_U(q_m) FINITE and NONZERO at every travel pole q_m
(roots of Sigma_1=1). We test that for BOTH g, and locate each bulk's own pole.
Low memory: a single truncated linear solve per evaluation (Smax ~ adaptive).
"""
import sys
import mpmath as mp
mp.mp.dps=30

# travel block Sigma_1 and its poles q_m
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(q,J=6000,k=1):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-40) and j>40: break
    return tot
def travel_poles(n):
    poles=[]; wv=mp.mpf('3.0'); prev=None; qprev=None; step=mp.mpf('0.02')
    while len(poles)<n and wv<300:
        tau=2/(wv*wv); q=mp.e**(-tau); val=Sig_t(q)-1
        if prev is not None and prev*val<0:
            try:
                r=mp.findroot(lambda qq: Sig_t(qq)-1,(qprev+q)/2)
                if 0<r<1 and all(abs(r-p)>mp.mpf(10)**(-18) for p in poles): poles.append(r)
            except Exception: pass
        prev=val; qprev=q; wv+=step
    return sorted(poles)

def gap_broken(q,y):    return (q*y)/(1-q*y)
def gap_correct(q,y):   return q/(1-q*y)

def bulk_block(q,y,gfn,Smax=None):
    if Smax is None:
        Smax=max(60, int(mp.ceil(45/(1-q))))   # q^Smax ~ e^-45, negligible
    g=gfn(q,y); n=Smax
    E=mp.matrix(n,1); M=mp.matrix(n,n)
    for w in range(1,n+1): E[w-1,0]=2*q**w
    for a in range(1,n+1):
        qa=q**a
        for b in range(1,n+1):
            K=q**max(a,b)+q**(a+b)*g
            M[b-1,a-1]=2*q**b*K
    P=mp.lu_solve(mp.eye(n)-M,E)
    return sum(P[i,0] for i in range(n))

def bulk_pole_at_yeqq(gfn):
    # scan q, find where bulk_block(q,q) first diverges (1-eigenvalue crosses 0)
    qprev=None; vprev=None; q=mp.mpf('0.20'); step=mp.mpf('0.02')
    while q<mp.mpf('0.72'):
        try:
            v=1/bulk_block(q,q,gfn)   # ->0 at the pole
        except Exception:
            v=mp.mpf(0)
        if vprev is not None and vprev*v<0:
            return mp.findroot(lambda z: 1/bulk_block(z,z,gfn),(qprev+q)/2)
        vprev=v; qprev=q; q+=step
    return None

if __name__=="__main__":
    NP=int(sys.argv[1]) if len(sys.argv)>1 else 5
    poles=travel_poles(NP)
    print("travel poles q_m (Sigma_1=1):", [mp.nstr(p,10) for p in poles])
    pb=bulk_pole_at_yeqq(gap_broken); pc=bulk_pole_at_yeqq(gap_correct)
    print(f"BULK pole at y=q (block diverges):  broken g -> {mp.nstr(pb,10) if pb else None}   corrected g -> {mp.nstr(pc,10) if pc else None}")
    print()
    print("B_U(q_m) = bulk dressing at each travel pole (y=q_m). FINITE & NONZERO => gap-A holds.")
    print(f"{'m':>2} {'q_m':>12} {'B_broken':>16} {'B_corrected':>16}  notes")
    for i,qm in enumerate(poles):
        try: Bb=bulk_block(qm,qm,gap_broken)
        except Exception: Bb=None
        try: Bc=bulk_block(qm,qm,gap_correct)
        except Exception: Bc=None
        note=""
        if Bc is not None:
            note = "finite,nonzero" if abs(Bc)>mp.mpf(10)**(-12) and abs(Bc)<mp.mpf(10)**12 else "DEGENERATE"
        print(f"{i:>2} {mp.nstr(qm,10):>12} {mp.nstr(Bb,8) if Bb is not None else 'div':>16} {mp.nstr(Bc,8) if Bc is not None else 'div':>16}  {note}")
