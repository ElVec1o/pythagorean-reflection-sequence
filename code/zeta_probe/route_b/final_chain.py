import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

print("FULL CHAIN at travel poles. t1 from raw, from VOP, from P12/Se; and the asymptotic decomposition.")
print(f"{'m':>3} {'tau':>9} {'t1_raw':>12} {'t1_VOP':>12} {'P12/Se':>12} {'t1/tau':>9} | {'P12/(tau^1.5 sinw)':>18} {'Se/(sqrt(tau/2)sinw)':>20}")
for i in [1,2,4,8,16,32,56,72]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.2*float(w)); N=int(60/(1-q))
    b0,b1,t0,t1raw,L,qp=raw(q,N)
    yh=cocyc_y(q,N); qn=mp.mpf(1);S=mp.mpf(0)
    for n in range(1,N+1):
        qn=qn*q;S+=2*qn**3/(yh[n]*yh[n-1])
    P12,P22,P11,P21=cocyc(q,N); Se=P22
    sw=mp.sin(w)
    P12amp=P12/(tau**mp.mpf('1.5')*sw)         # -> 1/(4 sqrt2)=0.176777
    Seamp=Se/(mp.sqrt(tau/2)*sw)               # -> 1 (sin w sin(w-W) leading)
    print(f"{i:>3} {float(tau):>9.6f} {float(t1raw):>12.6f} {float(S):>12.6f} {float(P12/Se):>12.6f} {float(t1raw/tau):>9.6f} | {float(P12amp):>18.7f} {float(Seamp):>20.7f}")
    mp.mp.dps=50
print()
print(f"target P12amp=1/(4 sqrt2)={float(1/(4*mp.sqrt(2))):.7f}; Se amp target=1; t1/tau target=0.25")
