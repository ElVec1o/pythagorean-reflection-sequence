import cmath, math, sys
from ev import series
def wind(f, r, n):
    tot=0.0; prev=None; minabs=1e300
    for j in range(n+1):
        z=r*cmath.exp(2j*math.pi*j/n)
        v,_=f(z); minabs=min(minabs,abs(v))
        if prev is not None:
            d=cmath.phase(v/prev)
            tot+=d
        prev=v
    return tot/(2*math.pi), minabs
for name,sh in [('B',0),('Se',1)]:
    f=lambda z: series(z,sh)
    for r in [0.3,0.5,0.6,0.7,0.8,0.85,0.9,0.93]:
        w1,m1=wind(f,r,4000); w2,m2=wind(f,r,8000)
        print(name, r, round(w1,4), round(w2,4), 'min|f|=%.2e'%m2, flush=True)
