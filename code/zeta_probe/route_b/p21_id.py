import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
print("EXACT: P21 = -S0b ?  and P11 = ? (Wronskian P11 Se - P12 P21=1)")
print(f"{'q':>7} {'P21':>13} {'-S0b':>13} {'diff':>11} | {'P11':>13} {'(1+P12 P21)/Se':>15} {'diff':>11}")
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf);p=1-q;N=int(70/(1-q))
    P12,P22,P11,P21=cocyc(q,N); S0b=Sbulk(0,q); Se=1-Sbulk(1,q)
    d1=P21-(-S0b)
    d2=P11-(1+P12*P21)/Se
    print(f"{qf:>7} {float(P21):>13.7f} {float(-S0b):>13.7f} {float(d1):>11.2e} | {float(P11):>13.7f} {float((1+P12*P21)/Se):>15.7f} {float(d2):>11.2e}")
