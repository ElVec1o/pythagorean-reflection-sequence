"""
Verification of colleague's claims about (A) D_p uniform bound.

D_p(W) = sum_{k>=0} k^p (-1)^k W^{2k}/(2k)!
       = 2^{-p} f^{(p)}(log W), f(t)=cos(e^t)         [claim]
       = p! [s^p] cos(W e^{s/2})                       [GF claim]
recursion D_0 = cos W, D_{p+1} = (W/2) D_p'.

Claims to test:
 (0) D_p definition == GF coeff == recursion.
 (1) LITERAL (A) FALSE: no absolute C_D with sup_[0,w]|D_p| <= C_D (w/2)^p.
 (2) SHARP: sup_{W in [0,w]} |D_p(W)| <= (w/2)^p exp(p^2/(2w))    (C_D=1, conjectural)
     pointwise: |D_p(W)| <= (W/2)^p exp(p^2/(2W))
 (3) RIGOROUS FAMILY: |D_p(W)| <= inf_rho 2^{-p} p! rho^{-p} exp((W^2/2)(I0(2rho)-1))
 (4) J(W,rho) := (1/2pi) int e^{W G(psi)} dpsi <= exp((W^2/2)(I0(2rho)-1)),
     G(psi)=Im(e^{rho e^{i psi}}); also tighter exp((W^2/4)(I0(2rho)-1)).
"""
import mpmath as mp
mp.mp.dps = 50

# ---------- D_p via three routes ----------
def Dp_series(p, W, K=400):
    # sum_k k^p (-1)^k W^{2k}/(2k)!  -- direct, needs care for cancellation
    s = mp.mpf(0)
    term_logbound = None
    for k in range(0, K+1):
        if k == 0:
            kp = mp.mpf(0) if p > 0 else mp.mpf(1)
        else:
            kp = mp.mpf(k)**p
        t = (-1)**k * kp * W**(2*k) / mp.factorial(2*k)
        s += t
        if k > float(W)+5 and abs(t) < mp.mpf('1e-45')*max(abs(s), mp.mpf(1)):
            break
    return s

def Dp_recursion(p, W):
    # D_0 = cos W ; D_{p+1}=(W/2)D_p' -- via mpmath diff of symbolic? do numeric:
    # easier: use GF coefficient via Taylor of cos(W e^{s/2}) in s
    pass

def Dp_GF(p, W):
    # p! [s^p] cos(W e^{s/2})  via mpmath taylor
    f = lambda s: mp.cos(W * mp.e**(s/2))
    coeffs = mp.taylor(f, 0, p+2)
    return mp.factorial(p) * coeffs[p]

def Dp_flog(p, W):
    # 2^{-p} f^{(p)}(log W), f(t)=cos(e^t)
    if W <= 0: return mp.nan
    t0 = mp.log(W)
    g = lambda t: mp.cos(mp.e**t)
    d = mp.diff(g, t0, p)
    return d / mp.mpf(2)**p

print("="*70)
print("(0) D_p: series vs GF vs f-log identity")
print("="*70)
maxerr = mp.mpf(0)
for p in range(0, 16):
    for Wv in [mp.mpf('0.5'), mp.mpf('2'), mp.mpf('5'), mp.mpf('10')]:
        a = Dp_series(p, Wv)
        b = Dp_GF(p, Wv)
        c = Dp_flog(p, Wv)
        e1 = abs(a-b); e2 = abs(b-c)
        maxerr = max(maxerr, e1, e2)
print(f"  max |series-GF| and |GF-flog| over p<=15, W in (0.5,2,5,10) = {mp.nstr(maxerr,3)}")
print(f"  => {'AGREE (identities hold)' if maxerr < mp.mpf('1e-30') else 'DISAGREE'}")

# ---------- (1) literal (A) is FALSE ----------
print()
print("="*70)
print("(1) literal (A): sup_[0,w]|D_p|/(w/2)^p  -- is it bounded in p?")
print("="*70)
def supDp(p, w, N=1500):
    best = mp.mpf(0)
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        if Wv == 0:
            v = mp.mpf(0) if p > 0 else mp.mpf(1)
        else:
            v = abs(Dp_series(p, Wv))
        best = max(best, v)
    return best

for w in [mp.mpf('16'), mp.mpf('40'), mp.mpf('80')]:
    print(f"  w={float(w):.0f}: ratio sup|D_p|/(w/2)^p for p=0,4,...,")
    line = []
    for p in [0, 8, 16, 24, 32, 40, 48]:
        r = supDp(p, w) / (w/2)**p
        line.append(f"p={p}:{float(r):.3g}")
    print("    " + "  ".join(line))
