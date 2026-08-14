"""
SYNTHESIS VERDICT for R2 (prove t1 ~ tau/4 along travel poles).
Self-contained. Establishes ground truth and adjudicates the two competing claims:
  CLAIM-A (elementary ratio):  P12 leading = (1/2)(w-W)^2 sin w sin(w-W) is ELEMENTARY,
           remainder bounded by lem:cos => R2 closes ON V's FOOTING.
  CLAIM-B (saddle):  P12 leading IS a saddle with constant 1/(4 sqrt2), NOT a proven block
           => R2 reduced to a NAMED FACT one notch beyond lem:cos.
Every number printed and compared to raw().
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
    return l0,l1,u0[0],u1[0]   # b0,b1,t0,t1

def cocycle(q,N):
    # convA columns. Returns P12=Y, P22=Se=y, P11=X, P21=x
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

def Sbulk(start,q,J=None):
    # bulk lem:cos block: S_b(start,q) = sum_j alpha(start+2j) prod_{i<j} gamma(start+2i)
    if J is None: J=int(8*mp.sqrt(2/(-mp.log(q))))+200
    def alpha(k): return 2*q**(k+1)/(1-q**(k+1))
    def gamma(k): return 2*q**(k+2)/(1-q**(k+2))-2*q**(k+1)/(1-q**(k+1))
    S=mp.mpf(0); pr=mp.mpf(1)
    for j in range(J):
        S+=alpha(start+2*j)*pr
        pr*=gamma(start+2*j)
    return S

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*108)
print("PART 1  --  EXACT IDENTITIES (generic q, NOT poles).  These must hold to ~1e-30 or the whole edifice is wrong.")
print("="*108)
mxt1=mp.mpf(0); mxP21=mp.mpf(0); mxdet=mp.mpf(0); mxuni=mp.mpf(0); mxSe=mp.mpf(0); mxSo=mp.mpf(0)
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(70/p)
    b0,b1,t0,t1=raw(q,N)
    P12,Se,P11,P21=cocycle(q,N)
    S0b=Sbulk(0,q); S1b=Sbulk(1,q)
    # (D1) Se = 1 - S1b ; (D4) b0 = S0b/(1-S1b) ; (D2) b1=t0=S1b/(1-S1b)
    mxSe=max(mxSe, abs(Se-(1-S1b)))
    mxSo=max(mxSo, abs(b0-S0b/(1-S1b)))
    # t1 = P12/Se
    mxt1=max(mxt1, abs(t1-P12/Se))
    # (E1) P21 = -S0b
    mxP21=max(mxP21, abs(P21-(-S0b)))
    # det = 1 (unimodular): P11*Se - P12*P21 = 1
    mxdet=max(mxdet, abs(P11*Se-P12*P21-1))
    # (E2) unimodular consequence: P11*Se + P12*S0b = 1
    mxuni=max(mxuni, abs(P11*Se+P12*S0b-1))
print(f"  (D1) Se = 1 - S1b                         max err = {float(mxSe):.2e}")
print(f"  (D4) b0 = S0b/(1-S1b)                     max err = {float(mxSo):.2e}")
print(f"  (DICT) t1 = P12/Se                        max err = {float(mxt1):.2e}")
print(f"  (E1) P21 = -S0b                           max err = {float(mxP21):.2e}")
print(f"  (det) P11*Se - P12*P21 = 1 (unimodular)   max err = {float(mxdet):.2e}")
print(f"  (E2) P11*Se + P12*S0b = 1                 max err = {float(mxuni):.2e}")
print("  => EXACT:  t1 = P12/Se = (P12*S0b)/(S0b*Se) = D/(S0b*Se),  D := P12*S0b = 1 - P11*Se  (the 'deficit').")

print()
print("="*108)
print("PART 2  --  AT TRAVEL POLES: which pieces are PROVEN BLOCKS vs which need a NEW estimate?")
print("="*108)
print(f"{'m':>3} {'tau':>10} {'t1/tau':>9} | {'S0b*Se':>9} {'->1?':>5} | {'D=P12*S0b':>11} {'D/(tau/4)':>10} | {'P12/Se/(tau/4)':>13}")
print("  [S0b*Se: S0b~w sinw PROVEN, Se~sqrt(tau/2)sinw lem:cos => product ~ w*sqrt(tau/2)*sin^2 w = sin^2 w =1 at poles]")
for m in [2,4,8,16,24,32,40]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se,P11,P21=cocycle(q,N); S0b=Sbulk(0,q)
    D=P12*S0b
    print(f"{m:>3} {float(tau):>10.3e} {float(t1/tau):>9.6f} | {float(S0b*Se):>9.6f} {'':>5} | {float(D):>11.3e} {float(D/(tau/4)):>10.7f} | {float((P12/Se)/(tau/4)):>13.9f}")
    mp.mp.dps=60
print("  KEY: if S0b*Se->1 (PROVEN blocks) then  R2 <=> D = P12*S0b -> tau/4.")

print()
print("="*108)
print("PART 3  --  THE DECISIVE TEST: is P12's LEADING ORDER elementary (CLAIM-A) or a genuine saddle (CLAIM-B)?")
print("="*108)
print("Decompose P12 = E + R with E := (1/2)(w-W)^2 * sinw * sin(w-W)  [ELEMENTARY, W=w e^{-tau/2}].")
print("Also Se = E_S + R_S, E_S := sinw sin(w-W) [elementary phase shift].  CLAIM-A: R/E->0 AND R_S/E_S->0.")
print(f"{'m':>3} {'tau':>9} | {'P12':>12} {'E_elem':>12} {'P12/E':>9} {'R/E':>10} | {'Se':>11} {'E_S':>11} {'R_S/E_S':>9} | {'E/E_S':>11} {'(tau/4)':>9}")
for m in [2,4,8,16,24,32,40]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    W=w*mp.e**(-tau/2)
    _,_,_,t1=raw(q,N); P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW; ES=sw*swW
    R=P12-E; RS=Se-ES
    print(f"{m:>3} {float(tau):>9.4f} | {float(P12):>12.5e} {float(E):>12.5e} {float(P12/E):>9.6f} {float(R/E):>10.2e} | {float(Se):>11.4e} {float(ES):>11.4e} {float(RS/ES):>9.2e} | {float(E/ES):>11.7f} {float(tau/4):>9.6f}")
    mp.mp.dps=60
print("  E/E_S = (1/2)(w-W)^2 EXACTLY (elementary) = (1/2)w^2(1-e^{-tau/2})^2 -> (1/2)(2/tau)(tau/2)^2 = tau/4.")
print("  WATCH the R/E and R_S/E_S columns: do they -> 0 (CLAIM-A holds) or stay O(1) (CLAIM-B, E is not the true leading)?")
