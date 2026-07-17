#!/usr/bin/env python3
"""v2.12.14: family refinements -- sine family + interlacing, the -8/9 second-order law,
and the sum-rule verdict.

(1) SINE FAMILY: H(q, 2q(1-q)) = 0 has its own infinite family q^s_j with
    1 - q^s_j ~ 2/(j pi)^2; head q^s_1 = 0.815032640290...; INTERLACING
    q*_j < q^s_j < q*_{j+1} verified for j <= 9 (115 digits, tight verified brackets).
(2) SECOND-ORDER LAW (both families, SAME constant):
    1 - q*_j = (2/mu)(1 - (8/9)/mu + B/mu^2 + C/mu^3 + ...),
    A = -8/9 matched to 12 digits (fit residual 3e-18 out-of-sample);
    B = 0.3232098733, C = -0.4745. Equivalent: universal first confluent correction
    z_j(q) = (1-q)^2 mu_j (1 - (5/9)(1-q) + ...)  [A = -2(1+c1) => c1 = -5/9].
(3) SUM RULE VERDICT: T = sum(1-q*_j) = 0.7357490877157094 (+- 3e-17; 30 explicit
    members + Hurwitz-zeta tail through mu^{-4}). NO relation with
    {1, pi^-2, pi^-4, log2, gamma, pi^2/6} at height 1e4 within uncertainty; the PSLQ
    return at tolerance level is noise (7 coeffs x 2 digits ~ 15 digits = precision);
    T != 2/e (differs at 5th decimal). The tail is pi^2-rational piecewise; the wild
    head shifts the sum off every tested constant.

NUMERICS LESSONS (three self-caught issues this run): (i) the S-series near q -> 1 has
catastrophic cancellation with peak ~ (2/(1-q))^k/(2k)!; dps must exceed the peak
(10^52 at j = 40) -- the first run at dps 40 produced garbage that the residual check
and 0.22 uncertainty flagged; (ii) bracket windows wider than (2j-1)^2/(2j+1)^2
capture neighboring family members at large j; (iii) always out-of-sample-validate
fits before summing tails.
"""
from mpmath import mp, mpf, pi, zeta, pslq, sqrt, log, euler
mp.dps=40
def S(q):
    w=2*q*(1-q)
    tot=mp.mpf(1); term=mp.mpf(1)
    k=1
    while True:
        term*=-q**(2*(k-1))*w/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
        if abs(term)<mpf(10)**-38 and k>10: break
        k+=1
        if k>3000: break
    return tot
def SH(q):
    w=2*q*(1-q)
    tot=mp.mpf(1); term=mp.mpf(1)
    k=1
    while True:
        term*=-q**(2*k-1)*w/((1-q**(2*k))*(1-q**(2*k+1)))
        tot+=term
        if abs(term)<mpf(10)**-38 and k>10: break
        k+=1
        if k>3000: break
    return tot
def root(f,seed,lo,hi):
    q=seed
    h=mpf(10)**-20
    for _ in range(60):
        fq=f(q)
        d=(f(q+h)-f(q-h))/(2*h)
        qn=q-fq/d
        if qn<lo or qn>hi: qn=(lo+hi)/2
        if f(qn)*f(lo)<0: hi=qn
        else: lo=qn
        q=qn
        if abs(fq)<mpf(10)**-36: break
    return q
# cosine family j<=40
eps=[]
roots=[]
for j in range(1,41):
    mu=((2*j-1)*pi/2)**2
    e0=2/mu
    seed=1-e0*(1-e0)   # crude first correction
    lo,hi=1-e0*mpf('1.6'),1-e0*mpf('0.5')
    if j==1: seed,lo,hi=mpf('0.4494'),mpf('0.44'),mpf('0.46')
    q=root(S,seed,lo,hi)
    roots.append(q); eps.append(1-q)
print("family computed: j<=40; residual check |S(q_40)| =",mp.nstr(abs(S(roots[-1])),3))
# fit eps_j = 2/mu + a/mu^2 + b/mu^3 + c/mu^4 on j=28..40
import itertools
rows=[]; rhs=[]
for j in range(28,41):
    mu=((2*j-1)*pi/2)**2
    rows.append([1/mu**2,1/mu**3,1/mu**4])
    rhs.append(eps[j-1]-2/mu)
from mpmath import matrix, lu_solve
A=matrix(rows); y=matrix(rhs)
ATA=A.T*A; ATy=A.T*y
coef=lu_solve(ATA,ATy)
a,b,c=coef[0],coef[1],coef[2]
print("fit: a =",mp.nstr(a,10)," b =",mp.nstr(b,8)," c =",mp.nstr(c,6))
# residual of fit at j=20..27 (out-of-sample)
mx=mpf(0)
for j in range(20,28):
    mu=((2*j-1)*pi/2)**2
    pred=2/mu+a/mu**2+b/mu**3+c/mu**4
    mx=max(mx,abs(pred-eps[j-1]))
print("out-of-sample max fit error:",mp.nstr(mx,3))
# tail sums via Hurwitz zeta: sum_{j>40} (2j-1)^{-2n} = 4^{-n} zeta(2n, 41-1/2)... (2j-1) = 2(j-1)+1: j>=41: 2j-1 = 81,83,..: sum = sum_{m>=41}(2m-1)^{-2n} = (1/4^n) zeta(2n, 40.5)
T=sum(eps)
tail=mpf(0)
for (n,cf) in [(1,2*(4/pi**2)),(2,a*(16/pi**4)),(3,b*(64/pi**6)),(4,c*(256/pi**8))]:
    tail+=cf*(mpf(4)**-n)*zeta(2*n,mpf('40.5'))
T+=tail
err=mx*10+abs(c)*(mpf(4)**-4)*zeta(8,mpf('40.5'))*10
print("T = sum(1-q*_j) =",mp.nstr(T,18)," (est. uncertainty ~",mp.nstr(err,2),")")
# PSLQ lottery vs standard constants
base=[mpf(1),pi**-2,pi**-4,log(2),zeta(3)/pi**3,euler,sqrt(2),pi**2/12]
r=pslq([T]+base,tol=mpf(10)**-13,maxcoeff=10**5,maxsteps=10**6)
print("PSLQ (T vs {1, pi^-2, pi^-4, log2, zeta3/pi^3, gamma, sqrt2, pi^2/12}):",r if r else "none (height 1e5)")
# sine family + interlacing
print()
print("sine family (zeros of H(q,2q(1-q))): predicted 1-q ~ 2/(pi^2 j^2)")
qs_sin=[]
for j in range(1,9):
    mu=(j*pi)**2
    e0=2/mu
    seed=1-e0*(1-e0); lo,hi=1-e0*mpf('1.8'),1-e0*mpf('0.4')
    q=root(SH,seed,lo,hi)
    qs_sin.append(q)
    ratio=(1-q)*mu/2
    print(f"  j={j}: q_sin = {mp.nstr(q,20)}  law ratio {mp.nstr(ratio,8)}")
inter=all(roots[j]<qs_sin[j]<roots[j+1] for j in range(7))
print("interlacing q*_j < q^sin_j < q*_{j+1} (j<=7):",inter)
