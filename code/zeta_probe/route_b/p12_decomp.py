import mpmath as mp
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

# t1=P12/Se. We have Se=P22~sqrt(tau/2) sin w (cosW-T2). 
# Now characterize P12=Y at travel poles. Test P12 ~ ? * tau^{3/2} sin w (the prompt claim P12~sin w tau^{3/2}/(4 sqrt2)).
print("P12 asymptotic at travel poles. claim P12 ~ sin w * tau^{3/2}/(4 sqrt2)")
print(f"{'m':>3} {'tau':>10} {'w':>9} {'P12':>13} {'P12/tau^1.5':>13} {'sinw/(4 sqrt2)':>14} {'ratio':>9}")
for i in [2,4,8,16,24,32,40,56]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.0*float(w)); N=int(60/(1-q))
    P12,P22,P11,P21=cocyc(q,N)
    sw=mp.sin(w)
    pred=sw*tau**mp.mpf('1.5')/(4*mp.sqrt(2))
    print(f"{i:>3} {float(tau):>10.6f} {float(w):>9.3f} {float(P12):>13.3e} {float(P12/tau**mp.mpf('1.5')):>13.6f} {float(sw/(4*mp.sqrt(2))):>14.6f} {float(P12/pred):>9.5f}")
    mp.mp.dps=50
