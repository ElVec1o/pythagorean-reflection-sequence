"""
Final adversarial probes:
(A) R_S = Se - E_S = O(tau)? (the lem:cos / lem:Bbounded T2-class bound). Print R_S/tau,
    and T2-link: memory says R_S = -T2 with T2/(sqrt(tau) sinw)->sqrt2/36. Check R_S/(sqrt(tau)sinw).
    NB sqrt2/36=0.039284. If R_S~sqrt(tau) NOT tau, the 'O(tau)' bound claim is WRONG.
(B) off-pole: is P12 == (tau/4)*So a false identity? Evaluate at a generic non-pole q.
    Also t1 == P12/Se off-pole (should still hold -- it's exact).
(C) Circularity audit: does any quantity used to DERIVE t1~tau/4 itself assume t1~tau/4?
    E,E_S,W,w are built only from tau (elementary), P12,Se from raw cocycle. No t1 input. OK by construction.
(D) The DECISIVE question for 'V footing': the leading const of t1 needs
    E/E_S=(1/2)(w-W)^2 -> tau/4  AND  R/E->0, R_S/E_S->0. The latter are BOUNDS.
    But does the RATIO t1/tau->1/4 actually need R_S/E_S = o(1) to be a *bound* only,
    or does the sqrt(tau) saddle term in R_S shift the limit? Check:
    t1/tau vs (E/E_S)/tau-equivalent and the correction from R_S.
"""
import mpmath as mp

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y

def Se_So(q,J=None):
    if J is None: J=int(8*mp.sqrt(2/(-mp.log(q))))+200
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0); poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("=== (A) R_S rate: O(tau) [bound] or O(sqrt tau)? ; T2-link sqrt2/36 ===")
print(f"{'m':>3} {'tau':>9} {'R_S/tau':>10} {'R_S/(sqrt(t)sinw)':>17} {'R/E':>11} {'R_S/E_S':>11}")
for m in [2,4,8,16,24,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(2.8*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q))
    P12,Se=cocycle(q,N)
    W=w*mp.e**(-tau/2); sinw=mp.sin(w)
    E_S=mp.sin(w)*mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*E_S
    R_S=Se-E_S; R=P12-E
    print(f"{m:>3} {float(tau):>9.2e} {float(R_S/tau):>10.5f} {float(R_S/(mp.sqrt(tau)*sinw)):>17.8f} {float(R/E):>11.3e} {float(R_S/E_S):>11.3e}")
    mp.mp.dps=50

print()
print("=== (B) off-pole: t1==P12/Se exact? ; P12==(tau/4)So false? ===")
for q0 in ['0.70','0.85','0.93']:
    mp.mp.dps=60
    q=mp.mpf(q0); tau=-mp.log(q); N=int(70/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N); _,So=Se_So(q)
    print(f"q={q0}: |t1-P12/Se|={float(abs(t1-P12/Se)):.2e}   P12={float(P12):.6f}  (tau/4)So={float((tau/4)*So):.6f}  ratio={float(P12/((tau/4)*So)):.5f}")
