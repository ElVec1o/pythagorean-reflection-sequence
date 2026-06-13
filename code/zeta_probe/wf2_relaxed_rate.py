import mpmath as mp
mp.mp.dps=40
v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349]
r=[mp.mpf(v[i+1])/mp.mpf(v[i]) for i in range(len(v)-1)]  # r[i]=r_{i+1}
# model r_n = R + (A + B cos(pi n/2) + C sin(pi n/2) + D (-1)^n)/n  (period 4)
# Fit over a tail window with least squares (5 params).
import math
def basis(n):
    return [mp.mpf(1),
            mp.cos(mp.pi*n/2)/n,
            mp.sin(mp.pi*n/2)/n,
            ((-1)**n)/mp.mpf(n),
            mp.mpf(1)/n]
def fit(idxs):
    rows=[]; rhs=[]
    for i in idxs:
        n=i+1
        rows.append(basis(n)); rhs.append(r[i])
    A=mp.matrix(rows); b=mp.matrix(rhs)
    # least squares
    AtA=A.T*A; Atb=A.T*b
    x=mp.lu_solve(AtA,Atb)
    return x[0]
L=len(r)
for w in (12,16,20,24):
    idxs=list(range(L-w,L))
    R=fit(idxs)
    print(f"window last {w}: R_inf = {mp.nstr(R,14)}")
# also period-4 grouped means: average r over 4 consecutive (kills period-4 osc)
print("\n4-consecutive means (centered), then extrapolate a+b/n:")
g=[(r[i]+r[i+1]+r[i+2]+r[i+3])/4 for i in range(len(r)-3)]
# g[i] ~ smooth, fit a+b/n with n=i+2.5
for w in (6,10,14):
    Sx=Sy=Sxx=Sxy=mp.mpf(0); idx=list(range(len(g)-w,len(g)))
    for i in idx:
        x=mp.mpf(1)/(i+2.5); y=g[i]; Sx+=x;Sy+=y;Sxx+=x*x;Sxy+=x*y
    b=(w*Sxy-Sx*Sy)/(w*Sxx-Sx*Sx); a=(Sy-b*Sx)/w
    print(f"  smoothed tail {w}: a={mp.nstr(a,12)} (b={mp.nstr(b,6)})")
print("\nbeta2=1.4995, 3/2=1.5")
