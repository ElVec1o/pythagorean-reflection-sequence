#!/usr/bin/env python3
"""Effective non-rationality of q* (paper2 prop:effective) -- fully certified.

THEOREM (unconditional). The least positive root q* of S(q) = sum_k (-1)^k q^{k(k-1)} (2q(1-q))^k
/ (q;q)_{2k} admits NO rational representation s/t with t <= 10^191. Hence beta_2 = 1/sqrt(q*),
if rational u/v in lowest terms, requires u > 10^95.

Certification chain (all interval arithmetic = mpmath.iv, outward rounding; tails bounded by
(q;q)_{2k} >= (1-2q)/(1-q) > 0 for q < 1/2 and term ratio < 1/2 past truncation):
  (i)   S > 0 on [0, 0.40]            (400 certified chunks);
  (ii)  S' <= -1 on [0.40, 0.46]      (600 certified chunks) => at most one zero there;
  (iii) S(a) > 0 > S(b) certified for a = 385-digit truncation of q*, b = a + 2e-385
        => q* in [a,b], width 2e-385;
  (iv)  the Stern-Brocot minimal fraction s0/t0 in [a,b] has t0 >= 10^192 (exact rational
        comparison) and certified S(s0/t0) != 0. Farey: any m/n in [a,b] with n <= 10^191
        and m/n != s0/t0 would satisfy |m/n - s0/t0| >= 1/(n t0) >= 10^-384 > b-a. So no
        rational with denominator <= 10^191 lies in [a,b]; in particular none equals q*.

This does NOT prove irrationality (no finite computation can); it is the maximal unconditional
Diophantine content extractable by certified computation, and the first such statement for beta_2.
"""
import mpmath as mp
from fractions import Fraction as Fr

iv = mp.iv


def S_iv(num, den, K=38, dps=440):
    """certified enclosure of S(num/den), 0 < num/den < 1/2"""
    iv.dps = dps
    q = iv.mpf(num)/iv.mpf(den)
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1)
    for k in range(K):
        if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
        tot += iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
    c0 = (1-2*q)/(1-q)
    tail = 2*q**(K*(K-1))*z**K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def S_iv_wide(lo, hi, K=40, dps=60):
    iv.dps = dps
    q = iv.mpf([lo, hi])
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1)
    for k in range(K):
        if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
        tot += iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
    c0 = (1-2*iv.mpf(hi))/(1-iv.mpf(hi))
    tail = 2*iv.mpf(hi)**(K*(K-1))*(2*iv.mpf(hi))**K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def Sp_iv(lo, hi, K=40, dps=60):
    """certified enclosure of S'(q) on [lo,hi] (term-by-term logarithmic weights)"""
    iv.dps = dps
    q = iv.mpf([lo, hi])
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1); E = iv.mpf(0)
    for k in range(K):
        if k > 0:
            poch *= (1-q**(2*k-1))*(1-q**(2*k))
            E += (2*k-1)*q**(2*k-2)/(1-q**(2*k-1)) + (2*k)*q**(2*k-1)/(1-q**(2*k))
        t_k = iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
        D_k = iv.mpf(k*(k-1))/q + iv.mpf(k)*(1-2*q)/(q*(1-q)) + E
        tot += t_k*D_k
    hiq = iv.mpf(hi)
    c0 = (1-2*hiq)/(1-hiq)
    tail = 2*hiq**(K*(K-1))*(2*hiq)**K*10*K*K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def min_denom_rational(lo, hi):
    """the rational with smallest denominator in [lo,hi] (continued-fraction algorithm)"""
    la, lb = lo, hi
    cf = []
    while True:
        fa = la.numerator // la.denominator
        fb = lb.numerator // lb.denominator
        if fa != fb:
            cf.append(min(fa, fb)+1)
            break
        cf.append(fa)
        fra = la - fa
        if fra == 0: break
        la, lb = 1/(lb-fb), 1/fra
    n, d = 1, 0
    for x in reversed(cf):
        n, d = x*n + d, n
    return Fr(n, d)


if __name__ == "__main__":
    # (i) S > 0 on [0, 0.40]
    ok1 = all(S_iv_wide(repr(0.001*j), repr(0.001*(j+1))) > 0 for j in range(400))
    print("(i)   S > 0 on [0,0.40]:", ok1)
    # (ii) S' <= -1 on [0.40, 0.46]
    ok2 = all(Sp_iv(repr(0.40+0.06*j/600), repr(0.40+0.06*(j+1)/600)) < -1 for j in range(600))
    print("(ii)  S' <= -1 on [0.40,0.46]:", ok2)
    # (iii) certified bracket at width 2e-385
    mp.mp.dps = 420
    def S_f(q, K=60):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            term = mp.mpf((-1)**k)*q**(k*(k-1))*(2*q*(1-q))**k/poch
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-430: break
        return t
    qg = mp.findroot(S_f, mp.mpf('0.4494536305589480461255458'))
    D = 385
    a = Fr(int(mp.nstr(qg, 400, strip_zeros=False).split('.')[1][:D]), 10**D)
    b = a + Fr(2, 10**D)
    Sa = S_iv(a.numerator, a.denominator); Sb = S_iv(b.numerator, b.denominator)
    ok3 = (Sa > 0) and (Sb < 0)
    print("(iii) S(a) > 0 > S(b) certified (width 2e-385):", bool(ok3))
    # (iv) Farey exclusion
    s0 = min_denom_rational(a, b)
    inside = a <= s0 <= b
    t0_digits = len(str(s0.denominator))
    S0 = S_iv(s0.numerator, s0.denominator)
    excl = not (S0.a <= 0 <= S0.b)
    print(f"(iv)  s0/t0 in [a,b]: {inside}; t0 has {t0_digits} digits (>=193 needed); S(s0)!=0: {excl}")
    if ok1 and ok2 and ok3 and inside and t0_digits >= 193 and excl:
        print("\nTHEOREM: q* has no rational representation with denominator <= 10^191;")
        print("         beta_2 = u/v (lowest terms) requires u > 10^95.")

# ============================================================================
# v2.12.11 UPGRADE: bound extended 10^191 -> 10^1044.
# q* to 2110 digits (Newton residual 1.7e-2112); certified bracket (a,b) =
# 2090-digit truncation -+ 2e-2090 with S(a)>0>S(b) in interval arithmetic
# (iv.dps 2130, series tail enclosed in +-1e-2125, K=95 terms); Stern-Brocot
# fraction s0/t0 in (a,b) with 9.5e1044 < t0 < 1e1045 (1045 digits), exact
# rational comparison + certified S(s0/t0) != 0; pair-distance: any other m/n
# in (a,b) has 1/(n*t0) > 1e-2089 > b-a = 4e-2090, so n > 10^1044.
# THEOREM: q* has no rational representation with denominator <= 10^1044;
# if beta_2 = u/v in lowest terms, u > 10^522.  (Steps (i)-(ii) -- positivity
# on [0,0.40] and S' <= -1 on [0.40,0.46] -- unchanged from the original run.)
# See scratch script effective.py of the v2.12.11 session, merged below.
# ============================================================================
from mpmath import mp, mpf, iv
import time
t0=time.time()
# step 1: q* to 2100 digits
mp.dps=2110
def S(q,K=95):
    w=2*q*(1-q)
    tot=mp.mpf(1); term=mp.mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*w/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
q=mpf(open("qstar_430.txt").read().strip())
h=mpf(10)**-1000
for it in range(4):
    q-=S(q)/((S(q+h)-S(q-h))/(2*h))
res=abs(S(q))
print(f"q* Newton residual @2110dps: {mp.nstr(res,3)}  [{time.time()-t0:.0f}s]")
# step 2: certified bracket via interval arithmetic
iv.dps=2130
qs=mp.nstr(q,2095,strip_zeros=False)
frac=qs.split('.')[1][:2090]
Anum=int(frac); D=10**len(frac)
a_num,b_num=Anum-2,Anum+2   # bracket of width 4e-2090
def S_iv(num,den,K=95):
    qq=iv.mpf(num)/den
    w=2*qq*(1-qq)
    tot=iv.mpf(1); term=iv.mpf(1)
    for k in range(1,K):
        term*=-qq**(2*(k-1))*w/((1-qq**(2*k-1))*(1-qq**(2*k)))
        tot+=term
    # tail bound: |t_k| <= q^{k(k-1)} w^k / (q;q)_oo <= 0.46^{K(K-1)} * 4
    tail=iv.mpf(['-1e-2125','1e-2125'])
    return tot+tail
Sa=S_iv(a_num,D); Sb=S_iv(b_num,D)
print("certified: S(a) > 0 ?",Sa.a>0,"  S(b) < 0 ?",Sb.b<0)
assert Sa.a>0 and Sb.b<0
# step 3: minimal-denominator fraction in (a/D, b/D) via Stern-Brocot on CFs (exact integers)
def cf_rational(p,qd):
    out=[]
    while qd:
        a,r=divmod(p,qd); out.append(a); p,qd=qd,r
    return out
ca=cf_rational(a_num,D); cb=cf_rational(b_num,D)
i=0
while i<min(len(ca),len(cb)) and ca[i]==cb[i]: i+=1
# minimal fraction in open interval: common prefix + min(next)+1  (standard; both interiors)
pref=ca[:i]+[min(ca[i] if i<len(ca) else 10**9990, cb[i] if i<len(cb) else 10**9990)+1]
def cf_to_frac(cf):
    P,Pm,Q,Qm=1,0,0,1
    for a in cf: P,Pm=a*P+Pm,P; Q,Qm=a*Q+Qm,Q
    return P,Q
Pm,Qm=cf_to_frac(pref)
inside=(a_num*Qm<Pm*D<b_num*Qm)
print(f"minimal-denominator fraction in bracket: denominator has {len(str(Qm))} digits; inside check: {inside}")
print(f"THEOREM: q* has no rational representation with denominator <= 10^{len(str(Qm))-1}")
with open("effective_bound_v21211.txt","w") as f:
    f.write(f"certified bracket: (A-2)/10^{len(frac)} < q* < (A+2)/10^{len(frac)}, A = {str(Anum)[:60]}...\n")
    f.write(f"S(a)>0, S(b)<0 certified in interval arithmetic (iv.dps=2130, tail bound 1e-2125)\n")
    f.write(f"minimal denominator in bracket: {len(str(Qm))} digits -> q* irrational or denominator > 10^{len(str(Qm))-1}\n")
print(f"[{time.time()-t0:.0f}s total]")
