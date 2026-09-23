# Step 1: certified bracket for q* (least positive zero of S) and for beta2=1/sqrt(q*).
# Re-derives paper2 prop:effective steps (i)-(iii); writes integers to bracket.txt
# (in the current working directory). Self-contained: needs only mpmath.
import time, mpmath
from mpmath import mp, mpf, iv
t0=time.time()

# ---------------------------------------------------------------------------
# VENDORED verbatim from code/zeta_probe/beta2_effective_irrationality.py
# (functions S_iv_wide and Sp_iv; interval arithmetic = mpmath.iv, outward rounding).
# S(q) = sum_k (-1)^k q^{k(k-1)} (2q(1-q))^k / (q;q)_{2k}.
# Tails bounded via (q;q)_{2k} >= (1-2q)/(1-q) > 0 for q < 1/2.
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
# ---------------------------------------------------------------------------

# (i) S>0 on [0,0.40] (400 chunks); (ii) S'<=-1 on [0.40,0.46] (600 chunks) => unique zero there
ok1=all(S_iv_wide(repr(0.001*j),repr(0.001*(j+1)))>0 for j in range(400))
ok2=all(Sp_iv(repr(0.40+0.06*j/600),repr(0.40+0.06*(j+1)/600))< -1 for j in range(600))
print("(i)",ok1,"(ii)",ok2,f"[{time.time()-t0:.0f}s]",flush=True)
DP=2110
def S(q,K=95):
    w=2*q*(1-q); tot=mpf(1); term=mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*w/((1-q**(2*k-1))*(1-q**(2*k))); tot+=term
    return tot
q=mpf('0.4494536305589480461255458'); prec=40
while True:
    mp.dps=prec+20; h=mpf(10)**-(prec//2)
    for _ in range(6): q-=S(q)/((S(q+h)-S(q-h))/(2*h))
    if prec>=DP: break
    prec=min(2*prec,DP)
mp.dps=DP
print("residual",mpmath.nstr(abs(S(q)),3),f"[{time.time()-t0:.0f}s]",flush=True)
Dd=2090
A=int(mp.nstr(q,2095,strip_zeros=False).split('.')[1][:Dd]); D=10**Dd
a_num,b_num=A-2,A+2
iv.dps=2130
def S_iv(num,den,K=95):
    qq=iv.mpf(num)/den; w=2*qq*(1-qq); tot=iv.mpf(1); term=iv.mpf(1)
    for k in range(1,K):
        term*=-qq**(2*(k-1))*w/((1-qq**(2*k-1))*(1-qq**(2*k))); tot+=term
    return tot+iv.mpf(['-1e-2125','1e-2125'])  # tail: 4*0.46^(95*94) < 1e-3000
Sa=S_iv(a_num,D); Sb=S_iv(b_num,D)
ok3=bool(Sa.a>0 and Sb.b<0)
print("(iii) S(a)>0>S(b):",ok3,f"[{time.time()-t0:.0f}s]",flush=True)
assert ok1 and ok2 and ok3
# beta2 bracket: beta in [1/sqrt(b), 1/sqrt(a)], outward-rounded to E=2080 decimal digits
E=2080
mp.dps=2150
T=10**E
blo=int(mpmath.floor(T/mpmath.sqrt(mpf(b_num)/D)))-2
bhi=int(mpmath.ceil(T/mpmath.sqrt(mpf(a_num)/D)))+2
# exact integer verification: beta_lo=blo/T <= 1/sqrt(b)  <=>  blo^2 * b_num <= T^2 * D
assert blo*blo*b_num <= T*T*D, "blo"
assert bhi*bhi*a_num >= T*T*D, "bhi"
print("beta bracket width (units 1e-2080):", bhi-blo)
open("bracket.txt","w").write(f"{a_num}\n{b_num}\n{Dd}\n{blo}\n{bhi}\n{E}\n")
print("written",f"[{time.time()-t0:.0f}s]")
