import mpmath as mp
mp.mp.dps=70
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  # P12,P22,P11,P21

print("="*100)
print("EXACT DICTIONARY gapless-bulk <-> lem:cos bulk {S0b,S1b} (Sblk(0),Sblk(1))  [verified ~60+ digits]")
print("="*100)
ids = {
 "Se = 1 - S1b"              : lambda d: d['Se'] - (1-d['S1b']),
 "P22 = Se"                  : lambda d: d['P22'] - d['Se'],
 "So = (1-q)/(2q) * S0b"     : lambda d: d['So'] - (d['p']/(2*d['q']))*d['S0b'],
 "P21 = -S0b"                : lambda d: d['P21'] + d['S0b'],
 "b0 = S0b/(1-S1b) [G0bulk]" : lambda d: d['b0'] - d['S0b']/(1-d['S1b']),
 "b1 = S1b/(1-S1b)"          : lambda d: d['b1'] - d['S1b']/(1-d['S1b']),
 "t0 = b1"                   : lambda d: d['t0'] - d['b1'],
 "det P = 1 (SL2)"           : lambda d: d['P11']*d['P22']-d['P12']*d['P21'] - 1,
 "P11*Se + P12*S0b = 1"      : lambda d: d['P11']*d['Se']+d['P12']*d['S0b'] - 1,
 "t1 = P12/Se"               : lambda d: d['t1'] - d['P12']/d['Se'],
}
for qf in ['0.7','0.8','0.9','0.95']:
    q=mp.mpf(qf); N=int(60/(1-q)); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle_full(q,N)
    d=dict(q=q,p=p,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se_clf(q),So=So_clf(q),
           S0b=Sblk(0,q),S1b=Sblk(1,q),P11=P11,P12=P12,P21=P21,P22=P22)
    print(f"\n q={qf}:")
    for name,f in ids.items():
        r=abs(f(d))
        print(f"   {'OK ' if r<mp.mpf(10)**(-25) else 'XX '}{name:<28} residual={float(r):.1e}")

print("\n"+"="*100)
print("R1 (b0*tau->2): b0=S0b/(1-S1b)=G0bulk;  b0*tau=sqrt2*[sin w*(S0b/w)]/[Se/sqrt tau]->sqrt2*1/(1/sqrt2)=2")
print("  (R1a) S0b/(w sin w)->1 [PROVEN bulk numerator-asymptotic]; (R1b) Se*w=(1-S1b)*w->1 [lem:cos extreme-phase]")
print("R2 (t1/tau->1/4): t1=P12/Se; t1/tau=(P12*w/tau)/(Se*w)->(1/4)/1=1/4")
print("  (R1b) Se*w->1 [same]; (R2) P12*w/tau->1/4 [lem:cos extreme-phase amplitude of cocycle P12]")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'b0*tau':>12} {'S0b/(w sinw)':>13} {'Se*w':>10} {'P12*w/tau':>11} {'t1/tau':>10} {'s':>10}")
for m in [1,2,4,8,16,32,40]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle_full(q,N)
    S0b=Sblk(0,q)
    print(f"{m:>3} {float(tau):>10.6f} {float(b0*tau):>12.8f} {float(S0b/(w*mp.sin(w))):>13.8f} {float(P22*w):>10.6f} {float(P12*w/tau):>11.7f} {float(t1/tau):>10.7f} {float((q/p)*t1):>10.7f}")
