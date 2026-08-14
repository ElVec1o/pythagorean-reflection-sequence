import mpmath as mp, pickle, numpy as np
mp.mp.dps=55
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]

# ROBUST nearest-singularity estimate: the cut-foot. Use the fact that Re(A) is the STABLE
# coordinate (~2.8 from recurrence; 1.6-3.0 from Pade). Average all dominant-pair estimators.
ests=[
 ("recur n=10",2.684,4.456),("recur n=14",2.789,5.104),("recur n=18",2.868,5.393),
 ("Pade pair1",1.612,5.392),("Pade pair2",2.954,4.951),
 ("Prony K3",2.096,3.530),("Prony K4",3.369,5.373),
]
Re=np.mean([e[1] for e in ests]); Im=np.mean([e[2] for e in ests])
print("Dominant-pair estimators (Re,Im of nearest singularity A0):")
for nm,r,i in ests: print(f"  {nm:12s}: Re={r:.3f} Im={i:.3f} |A|={ (r*r+i*i)**.5:.3f} arg={np.degrees(np.arctan2(i,r)):.1f}")
print(f"\n  MEAN: Re(A0)={Re:.3f}  Im(A0)={Im:.3f}  |A0|={ (Re*Re+Im*Im)**.5:.3f}  arg={np.degrees(np.arctan2(Im,Re)):.1f} deg")
print(f"  Spread: Re in [1.6,3.4], Im in [3.5,5.4]")
print(f"\n  ==> CONSERVATIVE perpendicular distance R+ to nearest sing:  R = min Im(A0) >= 3.5")
print(f"      (Prony K3 gives the smallest, Im=3.53; all others >=4.46)")

# The exponential type on R_+: for B analytic in the strip |Im t|<R0 (R0=min Im over all sings),
# B grows at most like exp(t/R0)*poly? NO -- on R_+ the growth is governed by the NEAREST sing's
# REAL part: B(t)~ C e^{t * Re(1/A0)}? Let's get the right rate. For a sqrt branch at A0=R e^{i th}
# (th in (0,pi/2)), b_n ~ Re(c A0^{-n} n^{-3/2}) => B(t)=sum b_n t^n has radius |A0| and on the
# real axis B(t) is dominated, for t->|A0|^-, by 2|c| t^{?}... but past |A0| it's the ANALYTIC
# CONTINUATION around the cut. The Borel sum int_0^inf e^{-s/tau}B(s)ds only needs the growth of
# the CONTINUATION on R_+, which for a fn analytic in a strip about R_+ is exp-type 1/R0.
# Measure directly: fit B(t)~K e^{t/R} to the RELIABLE points t=1..4.
import math
pts=[(1,3.10289),(2,10.79728),(3,27.32165),(4,59.53596)]
# log B = log K + t/R  -> linear regression
T=np.array([p[0] for p in pts]); LB=np.array([math.log(p[1]) for p in pts])
A_=np.vstack([np.ones(len(T)),T]).T
c,_,_,_=np.linalg.lstsq(A_,LB,rcond=None)
print(f"\n  Fit B(t)=K e^(t/R) on t=1..4: K={math.exp(c[0]):.3f}, 1/R={c[1]:.4f} => R={1/c[1]:.3f}")
print(f"  (This R~1.1 is the EFFECTIVE rate in the pre-asymptotic range; true R0 from sing geometry.)")
