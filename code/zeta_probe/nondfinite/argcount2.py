import cmath, math
from ev import series
def wind(sh, r, n):
    tot=0.0; prev=None; minabs=1e300; bigmax=0
    for j in range(n+1):
        z=r*cmath.exp(2j*math.pi*j/n)
        v,b=series(z,sh); minabs=min(minabs,abs(v)); bigmax=max(bigmax,b)
        if prev is not None: tot+=cmath.phase(v/prev)
        prev=v
    return tot/(2*math.pi), minabs, bigmax
for sh,name in [(0,'B'),(1,'Se')]:
  for r in [0.94,0.95,0.96,0.97]:
    w1=wind(sh,r,20000); w2=wind(sh,r,40000)
    print(name,r,round(w1[0],3),round(w2[0],3),'min %.1e big %.1e'%(w2[1],w2[2]),flush=True)
