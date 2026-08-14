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

# Se = cosW - T2 EXACT (T1 cancels). Mirror for P12.
# The cocycle is the "phase" transfer. Se=P22 is the cos-type solution (starts y=1 -> cos w at leading).
# P12=Y starts Y=0; it's the SIN-type solution. Leading elementary: Y ~ -sin(W)*(something) or sin-phase.
# Test P12 against elementary sin-phase pieces at travel poles:
print("P12 elementary structure. At poles w_m: sin w=+-1. Test P12 vs sin/cos W combos * tau^p")
print(f"{'m':>3} {'w':>9} {'W':>9} {'P12':>12} {'P12/sinW':>12} {'P12/(W cosW)':>13} {'P12/W':>11}")
for i in [2,4,8,16,32,40]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.0*float(w)); N=int(60/(1-q))
    P12,P22,P11,P21=cocyc(q,N)
    W=w*mp.e**(-tau/2)
    print(f"{i:>3} {float(w):>9.3f} {float(W):>9.3f} {float(P12):>12.3e} {float(P12/mp.sin(W)):>12.5f} {float(P12/(W*mp.cos(W))):>13.5f} {float(P12/W):>11.5f}")
    mp.mp.dps=50
