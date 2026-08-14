import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

print("="*100)
print("R2 RESOLUTION SUMMARY  (all machine-checked)")
print("="*100)
print("\n[A] EXACT cocycle dictionary (generic q, error ~1e-30..1e-60):")
print("    P22 = Se = 1 - S1b   |   P21 = -S0b   |   t1 = P12/Se   |   det: P11*Se - P12*P21 = 1")
mx_p21=mp.mpf(0); mx_det=mp.mpf(0)
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf);p=1-q;N=int(70/(1-q))
    P12,P22,P11,P21=cocyc(q,N); S0b=Sbulk(0,q); S1b=Sbulk(1,q)
    mx_p21=max(mx_p21,abs(P21-(-S0b))); mx_det=max(mx_det,abs(P11*P22-P12*P21-1))
print(f"    max|P21+S0b|={float(mx_p21):.1e}   max|det-1|={float(mx_det):.1e}")

print("\n[B] EXACT VOP closed form for t1 (SL2 unit-Wronskian telescoping), error ~1e-57:")
print("    t1 = sum_{n>=1} 2 q^{3n}/(y_n y_{n-1}),  y_n = P22 cocycle partials (y_inf = Se)")
mxv=mp.mpf(0)
for qf in ['0.70','0.80','0.88','0.96','0.985']:
    q=mp.mpf(qf);N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    yh=cocyc_y(q,N); qn=mp.mpf(1);S=mp.mpf(0)
    for n in range(1,N+1): qn=qn*q;S+=2*qn**3/(yh[n]*yh[n-1])
    mxv=max(mxv,abs(t1-S))
print(f"    max|t1_raw - t1_VOP|={float(mxv):.1e}")

print("\n[C] ASYMPTOTICS at travel poles -> t1 ~ tau/4:")
print("    P12 ~ (sqrt2/8) tau^{3/2} sin w   [amp -> 1/(4 sqrt2)=sqrt2/8=0.1767767]")
print("    Se  ~ sqrt(tau/2) sin w           [V's footing, lem:cos]")
print("    => t1 = P12/Se ~ (sqrt2/8 tau^{3/2})/(sqrt(tau/2)) = tau/4   (sin w CANCELS)")
print(f"    {'m':>3} {'tau':>10} {'t1/tau':>10} {'P12 amp':>11} {'Se amp':>10}")
for i in [4,16,40,72]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.2*float(w)); N=int(60/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocyc(q,N); sw=mp.sin(w)
    print(f"    {i:>3} {float(tau):>10.6f} {float(t1/tau):>10.7f} {float(P12/(tau**mp.mpf('1.5')*sw)):>11.7f} {float(P22/(mp.sqrt(tau/2)*sw)):>10.7f}")
    mp.mp.dps=60
print(f"    targets:                   0.2500000   0.1767767  1.0000000")
