"""
#6 attack. Establish what CLOSES elementarily and isolate the genuine residual.
EXACT reformulation (at pole, det=1, P21=-P11):  t1=Pi/(1-Pi), Pi=P12 P11=1-P11 Se.
  => gate s<1  <=>  Pi < 1-q  <=>  P11 Se > q.   (verify)
ELEMENTARY leading bound:  |E| <= (1/2)|w-W|^3 <= (1/2)(w tau/2)^3 = tau^{3/2}/(4 sqrt2)=0.1768 tau^{3/2},
  STRICT, no saddle. Gate threshold (1/sqrt2)tau^{3/2}=0.707 tau^{3/2}. So elementary E uses only 25%;
  residual budget for |R|=|P12-E| is 0.53 tau^{3/2}. (verify |E| bound + |E| coeff)
RESIDUAL R=P12-E: true rate? (O(tau^{5/2})=o(tau^{3/2}), huge room) -- but rigorous bound via
  variation-of-parameters is only O(tau) (Green's function through the zero). So R's DECAY is the
  open q-Bessel confluence estimate. (verify R rate, and |R|/tau^{3/2}->0)
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12,Se,P11,P21
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print(f"{'m':>3}{'tau':>10}{'Pi=P12P11':>12}{'1-q':>11}{'Pi<1-q':>7}{'P11Se>q':>8}{'|E|/t1.5':>9}{'<0.1768':>8}{'|R|/t1.5':>10}{'|R|/t2.5':>10}")
for m in range(1,17):
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(1.3*float(w)); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    W=w*mp.e**(-tau/2); E=mp.mpf('0.5')*(w-W)**2*mp.sin(w)*mp.sin(w-W); R=P12-E
    Pi=P12*P11; oneq=1-q; t15=tau**mp.mpf('1.5'); t25=tau**mp.mpf('2.5')
    # elementary upper bound on |E|
    Eel=mp.mpf('0.5')*abs(w-W)**3
    print(f"{m:>3}{float(tau):>10.6f}{float(Pi):>12.7f}{float(oneq):>11.7f}{str(Pi<oneq):>7}{str(P11*Se>q):>8}"
          f"{float(abs(E)/t15):>9.5f}{str(abs(E)/t15<mp.mpf('0.17678')+mp.mpf('1e-6')):>8}{float(abs(R)/t15):>10.6f}{float(abs(R)/t25):>10.5f}")
    mp.mp.dps=30
print("\nPi=P12P11<1-q (gate, EXACT reform) and P11Se>q at all poles; |E|/tau^1.5 < 0.1768 (ELEMENTARY,")
print("uses 25% of gate budget 0.707); |R|/tau^1.5 -> 0 (residual has room), |R|/tau^2.5 bounded (R=O(tau^2.5)).")
print("=> elementary part CLOSED; lone residual = decay of R (q-Bessel confluence), rigorous v.o.p. bound O(tau) NOT enough.")
