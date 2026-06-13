#!/usr/bin/env python3
"""ROUTE B v3: robust extrapolation with honest error bar, then symbolic ID on the
central value. Use BST/Richardson on smoothed ratios and report a spread."""
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps=50

u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
   11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,
   1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,
   29338781,43997388,65932461,98849591,147969934]
N=len(u)
r=[mp.mpf(u[i+1])/u[i] for i in range(N-1)]

# Smooth out the period-2 oscillation once: s_n = (r_n+r_{n+1})/2
s=[(r[i]+r[i+1])/2 for i in range(len(r)-1)]  # len 41, indexed by n

# Model A: s_n = beta + C/n  (power law). Richardson: beta ~ n*s_n-(n-1)*s_{n-1}
print("Richardson assuming s_n = beta + C/n   (b_n = n*s_n-(n-1)*s_{n-1}):")
rich1=[]
for i in range(1,len(s)):
    n2=i+1; n1=i           # crude index; use position+1 as 'n'
    b=n2*s[i]-n1*s[i-1]
    rich1.append(b)
for v in rich1[-6:]:
    print("   ", mp.nstr(v,12))

# Model B: s_n = beta + C/n^2.  b_n = (n^2 s_n - (n-1)^2 s_{n-1})/(n^2-(n-1)^2)
print("\nRichardson assuming s_n = beta + C/n^2:")
rich2=[]
for i in range(1,len(s)):
    n2=mp.mpf(i+1); n1=mp.mpf(i)
    b=(n2**2*s[i]-n1**2*s[i-1])/(n2**2-n1**2)
    rich2.append(b)
for v in rich2[-6:]:
    print("   ", mp.nstr(v,12))

# Model C: s_n = beta + C*lambda^n (geometric) -> single Aitken on s, take tail mean
def aitken(seq):
    out=[]
    for i in range(len(seq)-2):
        a,b,c=seq[i],seq[i+1],seq[i+2]
        den=c-2*b+a
        out.append(b if den==0 else c-(c-b)**2/den)
    return out
a1=aitken(s)
print("\nSingle Aitken on smoothed s, tail:")
for v in a1[-6:]:
    print("   ", mp.nstr(v,12))

# Collect a robust central estimate and spread from the most-trustworthy tail values
pool=[]
pool += rich1[-4:]
pool += rich2[-4:]
pool += a1[-4:]
pool += s[-2:]            # raw smoothed tail
pool += [(mp.mpf(u[N-1])/u[N-11])**(mp.mpf(1)/10)]  # geometric window [32..42]
pool += [(mp.mpf(u[N-1])/u[N-6])**(mp.mpf(1)/5)]     # window [37..42]
pool=[p for p in pool if 1.49<p<1.51]
vmin=min(pool); vmax=max(pool)
center=(vmin+vmax)/2
print(f"\nPool size {len(pool)}")
print(f"min={mp.nstr(vmin,12)} max={mp.nstr(vmax,12)}")
print(f"center={mp.nstr(center,12)}  half-spread={mp.nstr((vmax-vmin)/2,8)}")

beta=center
err=(vmax-vmin)/2
print(f"\n>>> beta_2 ~ {mp.nstr(beta,10)} +/- {mp.nstr(err,4)}")
gap=abs(beta-mp.mpf(1.5))
print(f">>> |beta-3/2| = {mp.nstr(gap,6)};  err={mp.nstr(err,4)}")
print(f">>> trustworthy digits ~ {max(0,int(-mp.log10(err)))}")

# Symbolic ID on 3/2 specifically and on center
print("\n--- symbolic tests on center value ---")
print("3/2 within error?", gap<err)
# quadratics with tiny height
print("nearest small quadratic integer roots (|a|,|b|<=6):")
res=[]
for a in range(-6,7):
    for b in range(-6,7):
        d=a*a-4*b
        if d<0: continue
        rt=(-a+mp.sqrt(d))/2
        if abs(rt-beta)<err*3:
            res.append((abs(rt-beta),a,b,rt))
res.sort()
for d,a,b,rt in res[:8]:
    print(f"  x^2+({a})x+({b}): root {mp.nstr(rt,10)} diff {mp.nstr(d,4)}")

# PSLQ won't work (only ~3 good digits) but show it fails honestly
print("\nPSLQ on [1,beta,beta^2] (expected: meaningless given low precision):")
rel=mp.pslq([mp.mpf(1),beta,beta**2],maxcoeff=10**4,maxsteps=10**5)
print("  ", rel)
print("identify(beta):", mp.identify(beta))
