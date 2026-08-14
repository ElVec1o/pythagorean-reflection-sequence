import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Is P12 a parameter-derivative of Se? The cocycle y (=Se=P22) starts (x,y)=(0,1).
# P12=Y starts (X,Y)=(1,0). These are the two independent solutions. 
# Standard: the "other" solution Y can be written Y_n = y_n * sum_{k=1}^n 1/(y_k y_{k-1}) * (det step)
# which is EXACTLY our VOP: Y_N/y_N = sum 2q3n/(y_n y_{n-1}). Good, consistent.
#
# Now is the P12 AMPLITUDE 1/(4 sqrt2) tied to the lem:cos saddle sqrt2/36?
# Relations: 1/(4 sqrt2)=0.17678. sqrt2/36=0.03928. ratio=4.5=9/2. 
# 0.17678 = (sqrt2/36)*4.5 = (sqrt2/36)*(9/2)=9 sqrt2/72=sqrt2/8=0.17678. YES! 1/(4sqrt2)=sqrt2/8.
print("1/(4 sqrt2) =", float(1/(4*mp.sqrt(2))))
print("sqrt2/8     =", float(mp.sqrt(2)/8))
print("=> P12 amp = sqrt2/8 EXACTLY (1/(4 sqrt2)=sqrt2/8). Clean.")
print("lem:cos saddle sqrt2/36 =", float(mp.sqrt(2)/36), " ratio (sqrt2/8)/(sqrt2/36)=36/8=4.5")
print()
# So the question is whether P12 ~ (sqrt2/8) tau^{3/2} sin w is the SAME saddle integral as Se's T2.
# Se ~ sqrt(tau/2) sin w (leading ELEMENTARY, not the T2 saddle!). The genuine T2 saddle is O(tau) smaller.
# But P12's LEADING term IS a saddle (no elementary part survives), size tau^{3/2}.
# Compare scales: Se leading ~ tau^{1/2}; P12 leading ~ tau^{3/2}; ratio tau. t1=P12/Se~tau. consistent.
#
# Does P12 reduce to a derivative of a proven block? Test P12 vs d/dtau or d/d? of Se-type sums.
# Numeric: is P12 = c * (Se - cos W) type? Se-cosW = -T2 (the saddle). compare:
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
print("P12 vs -T2=(Se-cosW) [the lem:cos saddle of Se]:")
print(f"{'m':>3} {'P12':>12} {'-T2=Se-cosW':>13} {'P12/(-T2)':>11} {'P21=x':>12} {'P12/P21':>10}")
for i in [4,8,16,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.2*float(w)); N=int(60/(1-q))
    P12,P22,P11,P21=cocyc(q,N); W=w*mp.e**(-tau/2)
    nT2=P22-mp.cos(W)
    print(f"{i:>3} {float(P12):>12.3e} {float(nT2):>13.3e} {float(P12/nT2):>11.5f} {float(P21):>12.3e} {float(P12/P21):>10.5f}")
    mp.mp.dps=50
