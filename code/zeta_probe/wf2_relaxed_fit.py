import mpmath as mp
mp.mp.dps=40
v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349]
r=[mp.mpf(v[i+1])/mp.mpf(v[i]) for i in range(len(v)-1)]
# fit r_n = a + b/n using last window via least squares on pairs (eliminates b):
# a = (n2*r_n2 - n1*r_n1)/(n2-n1) for two indices -> Richardson; do many pairs.
import statistics
print("pairwise a-estimates  a = (n2 r2 - n1 r1)/(n2-n1):")
ns=list(range(1,len(r)+1))  # r[i] is r_{i+1}, n=i+1
est=[]
for span in (4,6,8,10):
    i2=len(r)-1; i1=i2-span
    n1=i1+1; n2=i2+1
    a=(n2*r[i2]-n1*r[i1])/(n2-n1)
    est.append(a)
    print(f"  span {span}: n=({n1},{n2}) -> a={mp.nstr(a,12)}")
# fit r_n = a + b/n + c/n^2 via 3 points (last three spans)
def fit3(i1,i2,i3):
    import mpmath as mp
    n1,n2,n3=i1+1,i2+1,i3+1
    A=mp.matrix([[1,mp.mpf(1)/n1,mp.mpf(1)/n1**2],
                 [1,mp.mpf(1)/n2,mp.mpf(1)/n2**2],
                 [1,mp.mpf(1)/n3,mp.mpf(1)/n3**2]])
    b=mp.matrix([r[i1],r[i2],r[i3]])
    x=mp.lu_solve(A,b)
    return x[0]
L=len(r)-1
print("\n3-point fits r_n=a+b/n+c/n^2 (a=limit):")
for d in (3,5,7):
    a=fit3(L-2*d,L-d,L)
    print(f"  pts spaced {d}: a={mp.nstr(a,12)}")
# direct linear fit a+b/n over a tail window
def linfit(idxs):
    import mpmath as mp
    Sx=Sy=Sxx=Sxy=mp.mpf(0); m=len(idxs)
    for i in idxs:
        x=mp.mpf(1)/(i+1); y=r[i]
        Sx+=x;Sy+=y;Sxx+=x*x;Sxy+=x*y
    b=(m*Sxy-Sx*Sy)/(m*Sxx-Sx*Sx)
    a=(Sy-b*Sx)/m
    return a,b
a,b=linfit(list(range(len(r)-12,len(r))))
print(f"\nleast-squares a+b/n on last 12: a={mp.nstr(a,12)} b={mp.nstr(b,8)}")
a,b=linfit(list(range(len(r)-8,len(r))))
print(f"least-squares a+b/n on last 8:  a={mp.nstr(a,12)} b={mp.nstr(b,8)}")
