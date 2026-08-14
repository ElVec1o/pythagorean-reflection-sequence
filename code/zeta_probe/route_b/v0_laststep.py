import mpmath as mp
mp.mp.dps=30
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# v_0 = (v_1(1+2q^2)+2q^3)/(1-2q^2-2q v_1). Examine v_1 along poles.
print(f"{'m':>3}{'v_1':>12}{'1-2q-2v1':>12}{'v0':>12}{'v0/tau':>9}")
for m in [1,2,4,8,16,32,64]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q)
    v=mp.mpf(0)
    for b in range(N,1,-1):  # stop at b=2 to get v_1
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        v=(v*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*v)
    v1=v
    q2=q*q; q3=q2*q
    v0=(v1*(1+2*q2)+2*q3)/(1-2*q2-2*q*v1)
    denom=1-2*q2-2*q*v1
    print(f"{m:>3}{float(v1):>12.7f}{float(denom):>12.7f}{float(v0):>12.8f}{float(v0/tau):>9.5f}")
print()
# v0=tau/4 means numerator ~ (tau/4)*denom. Numerator=v1(1+2q^2)+2q^3.
# As q->1: 1+2q^2->3, 2q^3->2. So numerator-> 3 v1 + 2. denom->1-2-2v1=-1-2v1.
# v0=(3v1+2)/(-1-2v1)*[corrections]. For v0->0 we need 3v1+2->0 => v1->-2/3.
# Check v1->-2/3:
print("v1 -> -2/3 =",float(mp.mpf(-2)/3),"?  (see table: v1 column should approach -0.6667)")
