import mpmath as mp
mp.mp.dps=40
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# v0=(v1(1+2q^2)+2q^3)/(1-2q^2-2q v1). Want to show v0->tau/4 given v1->-2/3.
# Write q=e^{-t}, t=tau. 1+2q^2=1+2e^{-2t}=3-4t+4t^2-...; 2q^3=2-6t+9t^2..;
# 1-2q^2=1-2e^{-2t}=-1+4t-4t^2..; 2q=2-2t+t^2..
# Let v1=-2/3+d. numerator=( -2/3+d)(3-4t+..)+2-6t+..
#  = -2 + (8/3)t + 3d + .. + 2 -6t +.. = (8/3-6)t +3d + O(t^2,dt)= (-10/3)t+3d.
# denom = (-1+4t..) -2q v1 = -1+4t -2(1-t)(-2/3+d)= -1+4t +(2-2t)(2/3-d)... let me just be careful:
#  -2q v1 = -2(1-t+..)(-2/3+d)=  (2-2t)(2/3-d)=4/3 -2d -4t/3+2t d..
#  denom= -1+4t +4/3-2d-4t/3 = 1/3 + (4-4/3)t -2d = 1/3 +(8/3)t -2d.
# v0=( -10t/3 +3d )/(1/3+8t/3-2d) ~ 3*(-10t/3+3d)=(-10t+9d) at leading denom 1/3.
# For v0~tau/4: -10t+9d = (1/3)*(t/4)? no: v0=( -10t/3+3d)/(1/3)= -10t+9d (if d,t small).
# v0=tau/4=t/4 => -10t+9d=t/4 => 9d=t/4+10t=41t/4 => d=41t/36 ~1.139t.
# So PREDICT v1 = -2/3 + (41/36) tau. Check numerically:
print("Predict v1 = -2/3 + (41/36)*tau, i.e. (v1+2/3)/tau -> 41/36 =",float(mp.mpf(41)/36))
for m in [4,8,16,32,64]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q)
    v=mp.mpf(0)
    for b in range(N,1,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        v=(v*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*v)
    v1=v
    print(f'm={m}: (v1+2/3)/tau={float((v1+mp.mpf(2)/3)/tau):.6f}')
