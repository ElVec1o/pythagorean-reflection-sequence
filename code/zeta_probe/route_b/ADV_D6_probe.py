"""
Adversarial probes of the SUPPORTING claims in D6:
  (P1) R11 = P11/(w sin w) -> 1 ;  (R11-1)/tau -> -0.12423 ;  c^2/tau -> 1/648=(sqrt2/36)^2
  (P2) [S2] is FALSE off-pole (ratio blows up) -- i.e. intrinsically pole-phase.
  (P3) route (a) DEAD: pref*Y3 and (2/3)Se both O(sqrt tau), difference O(tau^{3/2}).
  (P4) decomposition 1/(4 sqrt2) = A_lead + B_lead with the 1/P11 - Se split.
  (P5) the A_lead/B_lead numbers (0.3246, -0.1478): check via 1/P11 and Se leading coeffs.
"""
import mpmath as mp

def cocycle_full(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return X,Y,x,y

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

def refine_pole(q0, iters=8):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
half=mp.mpf('0.5'); s32=mp.mpf('1.5')

print("="*100)
print("(P1) R11=P11/(w sin w)->1 ; (R11-1)/tau ; c=cos w / sin w over sqrt(tau)... c^2/tau=1/648?")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'R11':>12} {'(R11-1)/tau':>14} {'cosw/sinw':>13} {'(cosw/sinw)^2/tau':>18}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    R11=P11/(w*mp.sin(w))
    c=mp.cos(w)/mp.sin(w)
    print(f"{m:>3} {float(tau):>11.4e} {float(R11):>12.7f} {float((R11-1)/tau):>14.7f} {float(c):>13.3e} {float(c*c/tau):>18.9f}")
    mp.mp.dps=50
print(f"  1/648 = {float(mp.mpf(1)/648):.9f}   (sqrt2/36)^2 = {float((mp.sqrt(2)/36)**2):.9f}")

print("\n"+"="*100)
print("(P2) [S2] off-pole: at q NOT a pole, (cos w - T2_Se)/tau^{3/2} should blow up")
print("="*100)
mp.mp.dps=80
# take a pole, perturb q by a small fraction of the inter-pole gap
m=16; q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
qp=refine_pole(q0); taup=-mp.log(qp)
print(f"  base refined pole m={m}: tau={float(taup):.4e}, Sig_t-1={mp.nstr(Sig_t(qp)-1,3)}")
for frac in ['0','1e-6','1e-4','1e-3','1e-2']:
    dq=mp.mpf(frac)*(1-qp)
    q=qp+dq; tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    T2Se=mp.cos(W)-P22
    s2=(mp.cos(w)-T2Se)/tau**s32
    print(f"  dq/(1-q)={frac:>6}: Sig_t-1={mp.nstr(Sig_t(q)-1,3):>10}  (cosw-T2Se)/t^1.5 = {float(s2):>14.5f}")

print("\n"+"="*100)
print("(P3) route (a): pref*Y3(1/q) and (2/3)Se -- both O(sqrt tau), difference O(tau^{3/2})?")
print("  fact 4: P12 = (2 q^3/(3(1-q^3))) Y3(1/q) - (2/3) Se ; Y3(1/q)=3 Y3(1) - (1-q^{-3}) Se, Y3(1)=(1-q^3)P12/(2 q^3)")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'pref*Y3(1/q)':>14} {'(2/3)Se':>12} {'diff':>13} {'diff/t^1.5':>12} {'/sqrt t':>10}")
for m in [4,8,16,32,60]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    Y3_1=(1-q**3)*P12/(2*q**3)
    Y3_1q=3*Y3_1-(1-q**(-3))*Se
    pref=2*q**3/(3*(1-q**3))
    A=pref*Y3_1q; B=(mp.mpf(2)/3)*Se
    diff=A-B
    print(f"{m:>3} {float(tau):>11.4e} {float(A):>14.7f} {float(B):>12.7f} {float(diff):>13.3e} {float(diff/tau**s32):>12.6f} {float(A/mp.sqrt(tau)):>10.4f}")
    # check the fact-4 identity itself
    rec = pref*Y3_1q - B - P12
    if abs(rec)>mp.mpf(10)**(-mp.mp.dps+30): print("   *** fact-4 identity residual:", mp.nstr(rec,3))
    mp.mp.dps=50

print("\n"+"="*100)
print("(P5) decomposition: P12 = 1/P11 - Se. 1/P11 -> A_lead t^1.5, Se -> ... ; A_lead, -B_lead?")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'(1/P11)/t^1.5':>15} {'Se/t^1.5':>12} {'P12/t^1.5':>12}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    a=(1/P11)/tau**s32; b=Se/tau**s32; p=P12/tau**s32
    print(f"{m:>3} {float(tau):>11.4e} {float(a):>15.7f} {float(b):>12.7f} {float(p):>12.7f}  [1/P11 - Se - P12 = {mp.nstr(1/P11-Se-P12,2)}]")
    mp.mp.dps=50
