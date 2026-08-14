"""
INDEPENDENT A6 verification, lean.  Tests the LOAD-BEARING links:
 (P)  pole condition  P11 + P21 = 0  at travel pole  -- is it EXACT?
 (D)  det P = 1                                       -- exact (algebraic)
 (C3) P12 = 1/P11 - Se                                -- follows from (P)+(D)
 (C1) P11 = S0_bulk,  (C2) Se = 1 - S1_bulk
 (G)  |P12|/tau^{3/2} < 1/sqrt2  at every pole; asymptote 1/(4sqrt2).
 (B)  the GATE-AS-BOUND: does |d11|,|dSe| <= K tau with K~0.13 hold, and does the
      crude bound 2 sqrt2 K < 1/sqrt2 actually close it?  Re-derive 2sqrt2 K.
 (S)  cross-check inline cocycle == matrix product on ONE pole.
"""
import mpmath as mp

def cocycle_inline(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    # prompt convention: return P12,Se,P11,P21 = Y,y,X,x
    return Y,y,X,x

def cocycle_matrix(q,N):
    P=mp.matrix([[1,0],[0,1]])
    for n in range(N,0,-1):
        qn=q**n;q2n=qn*qn;q3n=q2n*qn
        P=P*mp.matrix([[1+2*q2n,-2*qn],[2*q3n,1-2*q2n]])
    return P

def Sbulk(k,q,J=200000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        a=2*q**(k+2*j+1)/(1-q**(k+2*j+1))
        tot+=a*prod
        g=2*q**(k+2*j+2)/(1-q**(k+2*j+2)) - 2*q**(k+2*j+1)/(1-q**(k+2*j+1))
        prod*=g
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-6) and j>80: break
    return tot

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(260/(1-q))+80
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-12): break
    return S

def refine_pole(q0, iters=14):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
c0=mp.sqrt(2)/36; gate=1/mp.sqrt(2)

# (S) one-time inline-vs-matrix cross check at m=4
mp.mp.dps=80
q=poles[3]; N=int(50/(1-q))
P12i,Sei,P11i,P21i=cocycle_inline(q,N)
M=cocycle_matrix(q,N)
print("CROSS-CHECK inline vs matrix at m=4:")
print("  matrix P=",[ [float(M[0,0]),float(M[0,1])],[float(M[1,0]),float(M[1,1])] ])
print("  inline (P12,Se,P11,P21)=",float(P12i),float(Sei),float(P11i),float(P21i))
# map: which matrix entries equal inline P11,Se,P12,P21?
print("  P11i vs M[0,0]:",float(abs(P11i-M[0,0])),"  Sei vs M[1,1]:",float(abs(Sei-M[1,1])))
print("  P12i vs M[1,0]:",float(abs(P12i-M[1,0])),"  P12i vs M[0,1]:",float(abs(P12i-M[0,1])))
print("  P21i vs M[0,1]:",float(abs(P21i-M[0,1])),"  P21i vs M[1,0]:",float(abs(P21i-M[1,0])))
print()

print("="*108)
print(("{:>3} {:>11} {:>12} {:>12} {:>12} {:>11} {:>11} {:>10} {:>10}").format(
   "m","tau","P11+P21","detP-1","P12-(1/P11-Se)","P11/S0b","Se/(1-S1b)","|P12|/t1.5","2sqrt2*K"))

sup_gate=mp.mpf(0); supK=mp.mpf(0)
for m in [2,4,8,16,24,32,48,64,79]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=55+int(2.0*float(w0))
    q=refine_pole(poles[m-1])
    tau=-mp.log(q); w=mp.sqrt(2/tau); sw=mp.sin(w); cw=mp.cos(w)
    N=int(75/(1-q))
    P12,Se,P11,P21=cocycle_inline(q,N)
    poleC=P11+P21
    detm1=P11*Se-P12*P21-1
    id3=P12-(1/P11-Se)
    S0b=Sbulk(0,q); S1b=Sbulk(1,q)
    id1=P11/S0b; id2=Se/(1-S1b)
    t15=tau**mp.mpf('1.5'); rg=abs(P12)/t15
    # defects per SECRET_SAUCE: Se=(sin w/w)(1+dSe), P11=(w sin w)(1+d11)
    d11=P11/(w*sw)-1; dSe=Se*w/sw-1
    K=max(abs(d11),abs(dSe))/tau   # so |d|<=K tau
    sup_gate=max(sup_gate,rg); supK=max(supK,K)
    print(("{:>3} {:>11.4e} {:>12.2e} {:>12.2e} {:>12.2e} {:>11.7f} {:>11.7f} {:>10.6f} {:>10.5f}").format(
        m,float(tau),float(poleC),float(detm1),float(id3),float(id1),float(id2),
        float(rg),float(2*mp.sqrt(2)*K)),flush=True)
    mp.mp.dps=50

print("-"*108)
print("sup |P12|/tau^1.5 = %.7f  < 1/sqrt2 = %.6f   (margin %.2fx)" % (float(sup_gate),float(gate),float(gate/sup_gate)))
print("sup K (so |d11|,|dSe| <= K tau) = %.5f ;  crude gate bound 2sqrt2*K = %.5f  (claim: <1/sqrt2=%.5f)" %
      (float(supK),float(2*mp.sqrt(2)*supK),float(gate)))
print("1/(4 sqrt2) = %.7f  (claimed asymptote)" % float(1/(4*mp.sqrt(2))))
