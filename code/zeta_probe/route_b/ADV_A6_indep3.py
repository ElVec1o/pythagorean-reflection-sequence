"""
Decisive adversarial probes:
 (Q1) Is the SECRET_SAUCE crude triangle bound valid?
      |BR| <= cos^2 w + |d11|/(1-|d11|) + |dSe|   (BR = cos^2w - d11/(1+d11) - sin^2 w dSe)
      Check the inequality numerically AND that it actually yields |P12|/t1.5 <= 2sqrt2 K.
 (Q2) Does d11/tau, dSe/tau CONVERGE to a finite limit (so K bounded), and to what?
      Richardson-extrapolate d11/tau, dSe/tau in tau. If they -> -c1 = -0.12423, K bounded ~0.124.
 (Q3) Is the crude gate REALLY < 1/sqrt2 using the *limit* K, or does the finite-tau K exceed 1/4
      at small m (the worst case)?  Need K<1/4=0.25 for 2sqrt2 K<1/sqrt2.
 (Q4) sup over a DENSE sweep of poles m=1..29 of |P12|/t1.5 and of K -- catch any non-monotone spike.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x  # P12,Se,P11,P21
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
gate=1/mp.sqrt(2)

print("Q1+Q3+Q4: dense sweep m=1..29.  crude-bound validity, K, gate.")
print(f"{'m':>3} {'tau':>10} {'|P12|/t1.5':>11} {'d11/tau':>9} {'dSe/tau':>9} {'K=max|d|/t':>10} {'2sqrt2 K':>9} {'crudeOK':>7} {'crudeBnd':>9}")
supgate=mp.mpf(0); supK=mp.mpf(0); crude_viol=0
for m in range(1,30):
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=45+int(1.4*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(62/(1-q))
    P12,Se,P11,P21=cocycle(q,N); sw=mp.sin(w); cw=mp.cos(w)
    d11=P11/(w*sw)-1; dSe=Se*w/sw-1
    BR=1/(1+d11)-sw**2*(1+dSe)
    # exact P12 check: P12 should = BR/(w sw)
    t15=tau**mp.mpf('1.5'); g=abs(P12)/t15
    # crude bound on |BR|
    crudeBR=cw**2 + abs(d11)/(1-abs(d11)) + abs(dSe)
    crude_ok = abs(BR) <= crudeBR + mp.mpf(10)**(-20)
    if not crude_ok: crude_viol+=1
    K=max(abs(d11),abs(dSe))/tau
    # the SECRET_SAUCE final gate bound: |P12|/t1.5 <= crudeBR/(sqrt2 tau |sw|)
    crude_gate = crudeBR/(mp.sqrt(2)*tau*abs(sw))
    supgate=max(supgate,g); supK=max(supK,K)
    if m in [1,2,3,4,6,10,16,22,29]:
        print(f"{m:>3} {float(tau):>10.3e} {float(g):>11.7f} {float(d11/tau):>9.5f} {float(dSe/tau):>9.5f} {float(K):>10.5f} {float(2*mp.sqrt(2)*K):>9.5f} {str(crude_ok):>7} {float(crude_gate):>9.5f}",flush=True)
    mp.mp.dps=40
print("-"*100)
print(f"sup |P12|/t1.5 (m=1..29) = {float(supgate):.7f}  < 1/sqrt2={float(gate):.5f} ? {supgate<gate}")
print(f"sup K (m=1..29)          = {float(supK):.7f}  ; need K<1/4=0.25 for crude 2sqrt2 K<1/sqrt2 ? {supK<mp.mpf('0.25')}")
print(f"crude triangle |BR|<=bound violations: {crude_viol}")
print()
# Q2: convergence of d11/tau, dSe/tau
print("Q2: Richardson convergence of d11/tau and dSe/tau (do they -> finite -c1?)")
vals=[]
for m in [4,8,16,32,64]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=55+int(1.8*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(75/(1-q))
    P12,Se,P11,P21=cocycle(q,N); sw=mp.sin(w)
    d11=P11/(w*sw)-1; dSe=Se*w/sw-1
    vals.append((m,float(tau),float(d11/tau),float(dSe/tau)))
    print(f"  m={m:>2} tau={float(tau):.3e}  d11/tau={float(d11/tau):.7f}  dSe/tau={float(dSe/tau):.7f}  diff={float((d11-dSe)/tau**2):.4f}(/tau^2)")
    mp.mp.dps=40
print("  (if both -> ~ -0.1242 = -c1, K is bounded ~0.124, crude gate ~0.35 < 0.707 holds asymptotically)")
