import mpmath as mp

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y   # P12, Se

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("DECISIVE: is P12 leading order ELEMENTARY E=(1/2)(w-W)^2 sinw sin(w-W), R=P12-E subleading?")
print("If YES, P12 ~ sinw tau^1.5/(4sqrt2) is ELEMENTARY (like Se's phase shift), R2 closes on the")
print("lem:Bbounded BOUND alone (same as R1), NOT a new off-diagonal saddle constant.")
print("Track R/tau^1.5 -> 0 (subleading) and R/(tau^2 sinw) -> finite (next order).")
print("="*110)
print(f"{'m':>3} {'tau':>10} {'P12/t^1.5':>12} {'E/t^1.5':>12} {'R/t^1.5':>12} {'R/(t^2 sinw)':>13} {'(P12-E)/E':>11}")
for m in [4,8,16,24,32,40,48,56,64,72,78]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(1.5*float(w))
    W=w*mp.e**(-tau/2)
    N=int(60/(1-q))
    P12,Se=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    t15=tau**mp.mpf('1.5')
    E=mp.mpf(1)/2*(w-W)**2*sw*swW
    R=P12-E
    print(f"{m:>3} {float(tau):>10.3e} {float(P12/t15):>12.7f} {float(E/t15):>12.7f} {float(R/t15):>12.3e} {float(R/(tau**2*sw)):>13.5f} {float(R/E):>11.3e}",flush=True)
    mp.mp.dps=30
print()
print("1/(4sqrt2) =", float(1/(4*mp.sqrt(2))))
print("If E/t^1.5 -> 1/(4sqrt2) and R/t^1.5 -> 0, the saddle in P12pred is ELEMENTARY (no new constant).")
