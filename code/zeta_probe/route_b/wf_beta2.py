#!/usr/bin/env python3
"""
ROUTE B v2: careful look at the ratio sequence. The error is NOT clean geometric;
it oscillates. Diagnose the subdominant singularity structure before extrapolating.
"""
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 50

u = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
     11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,
     1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,
     29338781,43997388,65932461,98849591,147969934]
N=len(u)
r=[mp.mpf(u[i+1])/u[i] for i in range(N-1)]   # 42 ratios

print("n :  u_{n+1}/u_n")
for i,x in enumerate(r):
    print(f"{i:2d}: {mp.nstr(x,12)}")

# Look at the ROOT growth: u_n^{1/n}
print("\nu_n^(1/n):")
for n in range(5,N):
    print(f" n={n:2d}: {mp.nstr(mp.mpf(u[n])**(mp.mpf(1)/n),12)}")

# averaged ratio over a window (geometric mean of ratios) = (u_b/u_a)^(1/(b-a))
def gmean_ratio(a,b):
    return (mp.mpf(u[b])/u[a])**(mp.mpf(1)/(b-a))
print("\nWindowed geometric-mean ratio (u_b/u_a)^(1/(b-a)):")
for w in [(0,N-1),(10,N-1),(20,N-1),(30,N-1),(N-6,N-1),(N-11,N-1),(N-21,N-1)]:
    a,b=w
    print(f"  [{a}..{b}] : {mp.nstr(gmean_ratio(a,b),14)}")

# The ratio oscillates -> average consecutive pairs to damp period-2 oscillation
print("\nPairwise-averaged ratios (r_n + r_{n+1})/2:")
ravg=[(r[i]+r[i+1])/2 for i in range(len(r)-1)]
for i in range(len(ravg)-8,len(ravg)):
    print(f"  {i:2d}: {mp.nstr(ravg[i],14)}")

# geometric mean of consecutive pair sqrt(r_n r_{n+1})
print("\nsqrt(r_n * r_{n+1}) (geom mean of pairs), last few:")
rgm=[mp.sqrt(r[i]*r[i+1]) for i in range(len(r)-1)]
for i in range(len(rgm)-8,len(rgm)):
    print(f"  {i:2d}: {mp.nstr(rgm[i],14)}")

# ---- Single Aitken on the SMOOTHED (pair-averaged) sequence ----
def aitken(seq):
    out=[]
    for i in range(len(seq)-2):
        a,b,c=seq[i],seq[i+1],seq[i+2]
        den=c-2*b+a
        out.append(b if den==0 else c-(c-b)**2/den)
    return out

print("\n--- Aitken applied ONCE then track tail, on pair-averaged seq ---")
s=ravg
for k in range(1,6):
    s2=aitken(s)
    print(f" after {k} Aitken on ravg: last={mp.nstr(s2[-1],14)} 2nd-last={mp.nstr(s2[-2],14)}")
    s=s2

print("\n--- Aitken once then tail, on geom-mean-pair seq ---")
s=rgm
for k in range(1,6):
    s2=aitken(s)
    print(f" after {k} Aitken on rgm: last={mp.nstr(s2[-1],14)} 2nd-last={mp.nstr(s2[-2],14)}")
    s=s2

# ---- Model fit: r_n = beta + A*lambda^n*cos(theta n + phi).
# Estimate beta by fitting r_n with damped oscillation via least-squares on last K points,
# using a grid? Simpler: use the fact that if r_n -> beta with oscillation,
# the running average of r converges. Cesaro / repeated averaging (Euler-style).
print("\n--- Repeated averaging (smoothing) of raw ratios, take tail ---")
s=list(r)
for k in range(1,12):
    s=[(s[i]+s[i+1])/2 for i in range(len(s)-1)]
    print(f"  smooth {k:2d}: last={mp.nstr(s[-1],14)} (len {len(s)})")

# ---- Best honest estimate: bracket from monotone sub/super sequences ----
# odd-index ratios vs even-index ratios appear to bracket
print("\nEven-index ratios (r_0,r_2,...) tail:")
for i in range(len(r)-8,len(r)):
    tag = "even" if i%2==0 else "odd"
    print(f"  r[{i}] ({tag}) = {mp.nstr(r[i],12)}")

# converged estimate from smoothing:
sm=list(r)
for k in range(6):
    sm=[(sm[i]+sm[i+1])/2 for i in range(len(sm)-1)]
print(f"\nSmoothed(6) tail value ~ {mp.nstr(sm[-1],12)}")
print(f"3/2 = 1.5 ; diff = {mp.nstr(sm[-1]-mp.mpf(1.5),8)}")
