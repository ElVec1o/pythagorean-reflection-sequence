import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Try P12 = combination of Se,So and their q-derivatives (EXACT at generic q).
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
# P21=x is the OTHER off-diagonal (start (0,1)). Wronskian Xy-Yx=1 => P11 P22 - P12 P21=1.
# P11=X start(1,0). So we have 4 cocycle entries; Se=P22, and P21=x, P12=Y, P11=X.
# t1=P12/P22. There may be a second resolvent value s' = P21/P22 = x/y. Let's see what P21/P22 is.
print("Other cocycle ratios at generic q (is P21/Se a known block? is P11 So-related?):")
print(f"{'q':>7} {'P12/Se':>11} {'P21/Se':>11} {'P11/Se':>11} {'So':>10} {'2q/p So/Se=b0':>13}")
for qf in ['0.70','0.80','0.88','0.96']:
    q=mp.mpf(qf);p=1-q;N=int(70/(1-q))
    P12,P22,P11,P21=cocyc(q,N); Se,So=Se_So(q)
    print(f"{qf:>7} {float(P12/P22):>11.6f} {float(P21/P22):>11.6f} {float(P11/P22):>11.6f} {float(So):>10.6f} {float((2*q/p)*So/Se):>13.6f}")
print()
# P21=x is the (0,1)-start x-component. Recall b0=(2q/p)So/Se. Is So tied to P21?
# Test So vs P21 combos:
print("So vs P21 (the (0,1)-start x-comp):")
print(f"{'q':>7} {'P21':>12} {'So':>11} {'P21/So':>11} {'-p P21/(2q)':>13}")
for qf in ['0.70','0.80','0.88','0.96']:
    q=mp.mpf(qf);p=1-q;N=int(70/(1-q))
    P12,P22,P11,P21=cocyc(q,N); Se,So=Se_So(q)
    print(f"{qf:>7} {float(P21):>12.6f} {float(So):>11.6f} {float(P21/So):>11.6f} {float(-p*P21/(2*q)):>13.6f}")
