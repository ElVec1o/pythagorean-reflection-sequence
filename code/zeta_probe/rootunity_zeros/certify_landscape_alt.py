# certify_landscape_alt.py -- interval-arithmetic certificate for the landscape inequalities of the
# ALTERNATING q-series S_e(q) = sum (-1)^k p^k b_k and S_-(q) = sum (-1)^k p^{-k} b_k near q = -1
# (paper2a.tex, Proposition prop:t1minusone; companion of certify_landscape.py for prop:minusone).
#
# Notation as in certify_landscape.py: q=-e^{-t}, p=e^{-t}, t=r e^{i theta}, L=log 4,
#   Phi(x) = x L - x^2 - Li2(e^{-4x})/4 + pi^2/24,  x0 = log(2+sqrt5)/2,  Phi0 = Phi(x0).
# A term e^{(Phi(x) + i pi nu x)/t} has modulus e^{Om_nu(x)/r},
#   Om_nu(x) = Re((Phi(x) + i pi nu x) e^{-i theta}).
# The main term of S_e and S_- is the frequency nu=+1 saddle at x_+ = x0 + i pi/2, of modulus
#   e^{T'/r},  T' = Re(E_+ e^{-i theta}),  E_+ = Phi0 - pi^2/4 + i pi L/2.
# For EVERY (theta, R) in the box theta in theta1 +- 0.001, R = |x_A| in [0.0495, 0.0505],
# x_A = R e^{i theta}, we certify  sup Om_nu - T' <= -MARGIN  on
#   V+  (nu=+1):  x = Re x_A + i y,  R sin(theta) <= y <= pi/2     (path of J+ up to the saddle line)
#   V-  (nu=-1):  x = Re x_A + i y, -pi/2 <= y <= R sin(theta)     (path of J-)
#   C+  (nu=+3):  x = x_A + i y, 0 <= y <= pi                       (kernel remainder E+)
#   C-  (nu=-3):  x = x_A - i y, 0 <= y <= pi                       (kernel remainder E-)
# and the closed-form bounds on the two horizontal lines Im x = +-pi/2, on the two shifted rays
# x_A +- i pi + e^{i theta}[0,oo), for the head k <= K, and for the connector kernels.
#
# Method: identical to certify_landscape.py (mpmath.iv, 53-bit outward rounding; mean-value cells
# with |d/dx(Phi + i pi nu x)| <= L + 2|x| + max(-log(1-rho), log 2) + pi/2 + pi|nu|;
# Li2 by its series plus an explicit tail; theta and R carried as intervals; bisection).
#
# Run (memory < 100 MB):  perl -e 'alarm 290; exec @ARGV' python3 certify_landscape_alt.py
import sys, time
from mpmath import iv, mpf, mp

iv.prec = 53
mp.prec = 53
PI = iv.pi
L = iv.log(4)
from mpmath import atan as _atan, pi as _pi, log as _log
TH1 = _atan(_pi / _log(4))
DTH = mpf('0.001')
TH = iv.mpf([TH1 - DTH, TH1 + DTH])
R_LO, R_HI = mpf('0.0495'), mpf('0.0505')
RB = iv.mpf([R_LO, R_HI])
NLI = 120
MARGIN = mpf('0.10')
COS, SIN = iv.cos(TH), iv.sin(TH)


def hi(x):
    return mpf(x._mpi_[1]) if hasattr(x, '_mpi_') else mpf(x)


def lo(x):
    return mpf(x._mpi_[0]) if hasattr(x, '_mpi_') else mpf(x)


class C:
    __slots__ = ('re', 'im')

    def __init__(s, re, im=0):
        s.re = iv.mpf(re); s.im = iv.mpf(im)

    def __add__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.re + o.re, s.im + o.im)
    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.re - o.re, s.im - o.im)

    def __mul__(s, o):
        if not isinstance(o, C):
            o = iv.mpf(o); return C(s.re * o, s.im * o)
        return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
    __rmul__ = __mul__


def li2_exp(x, rho):
    a = iv.exp(-4 * x.re); an = iv.mpf(1)
    sr = iv.mpf(0); si = iv.mpf(0)
    for n in range(1, NLI + 1):
        an = an * a
        ph = 4 * n * x.im
        c = an / (n * n)
        sr = sr + c * iv.cos(ph); si = si - c * iv.sin(ph)
    tail = iv.mpf(rho) ** (NLI + 1) / ((NLI + 1) ** 2 * (1 - iv.mpf(rho)))
    e = iv.mpf([-hi(tail), hi(tail)])
    return C(sr + e, si + e)


def Om(x, nu, rho):
    """enclosure of Re((Phi(x) + i pi nu x) e^{-i theta}), theta in TH"""
    F = x * L - x * x - li2_exp(x, rho) * iv.mpf(0.25) + PI ** 2 / 24 + C(0, PI * nu) * x
    return F.re * COS + F.im * SIN


# ---------------- Phi0, T, T' ----------------
x0 = iv.log(2 + iv.sqrt(5)) / 2
z0sq = 9 - 4 * iv.sqrt(5)
li = iv.mpf(0); pw = iv.mpf(1)
for n in range(1, 60):
    pw = pw * z0sq; li = li + pw / (n * n)
li = li + iv.mpf([0, (z0sq.b ** 60) / (1 - z0sq.b)])
PHI0 = x0 * L - x0 ** 2 - li / 4 + PI ** 2 / 24
T = PHI0 * COS
TP = (PHI0 - PI ** 2 / 4) * COS + (PI * L / 2) * SIN      # T' = Re(E_+ e^{-i theta})
TP_LO = TP.a
print('Phi0 in', PHI0)
print('T  = Phi0 cos(theta)              in', T)
print("T' = Re(E_+ e^{-i theta})          in", TP, '  (main term of S_e, S_-)')

RE_MIN = (RB * COS).a
RHO = hi(iv.exp(-4 * iv.mpf(RE_MIN)))
LOGB = iv.mpf(max(hi(-iv.log(1 - iv.mpf(RHO))), hi(iv.log(2)))) + PI / 2
print('min Re x = %.5f on all four segments, rho <= %.5f' % (RE_MIN, RHO))


def segment(name, nu, xfun, dxdu, absx_max):
    M = L + 2 * iv.mpf(absx_max) + LOGB + PI * abs(nu)
    M = iv.mpf(hi(M)); dxdu = iv.mpf(hi(iv.mpf(dxdu)))
    stack = [(mpf(i) / 64, mpf(i + 1) / 64) for i in range(64)]
    worst = mpf(-10); cells = 0
    while stack:
        a, b = stack.pop()
        uc = (a + b) / 2
        w = Om(xfun(iv.mpf(uc)), nu, RHO)
        bound = hi(w + M * dxdu * (iv.mpf(b) - a) / 2 - TP_LO)
        cells += 1
        if bound > -MARGIN and (b - a) > mpf(2) ** -14:
            stack += [(a, uc), (uc, b)]
            continue
        worst = max(worst, bound)
    print("%-44s cells=%5d  |F'|<=%.2f  certified sup(Om - T') <= %+.5f" % (name, cells, float(hi(M)), float(worst)), flush=True)
    return worst


t0 = time.time()
ReA = RB * COS
ImA = RB * SIN
res = {}
# V+: y from R sin(theta) to pi/2 ; parametrise y = ImA + u (pi/2 - ImA), |dx/du| <= pi/2
res['V+'] = segment("V+ (nu=+1)  Re x_A + i y, Im x_A<=y<=pi/2", 1,
                    lambda u: C(ReA, ImA + u * (PI / 2 - ImA)), hi(PI / 2), hi(iv.mpf(R_HI) + PI / 2))
# V-: y from R sin(theta) down to -pi/2 ; |dx/du| <= pi/2 + R_HI
res['V-'] = segment("V- (nu=-1)  Re x_A + i y, -pi/2<=y<=Im x_A", -1,
                    lambda u: C(ReA, ImA - u * (PI / 2 + ImA)), hi(PI / 2 + iv.mpf(R_HI)), hi(iv.mpf(R_HI) + PI / 2))
res['C+'] = segment("C+ (nu=+3)  x_A + i y, 0<=y<=pi", 3,
                    lambda u: C(ReA, ImA + PI * u), hi(PI), hi(iv.mpf(R_HI) + PI))
res['C-'] = segment("C- (nu=-3)  x_A - i y, 0<=y<=pi", -3,
                    lambda u: C(ReA, ImA - PI * u), hi(PI), hi(iv.mpf(R_HI) + PI))

# ---------------- closed-form pieces ----------------
# Horizontal line Im x = +pi/2 (nu=+1): exactly Om_1(xi + i pi/2) = Phi(xi) cos(theta) + (T' - T),
# with Phi(xi) real and <= Phi0: maximum T' at xi = x0 (the saddle; Laplace). Nothing to certify.
# Horizontal line Im x = -pi/2 (nu=-1): Om_{-1} = Phi(xi) cos(theta) + Re((-pi^2/4 - i pi L/2) e^{-i theta}).
hm = T + (-(PI ** 2) / 4) * COS - (PI * L / 2) * SIN
print("line Im x=-pi/2 (nu=-1): sup Om - T' <= %+.4f" % float(hi(hm - TP_LO)))
# Shifted rays. On x_A + i pi + e^{i theta}[0,oo) the E+ integrand is, by the quasi-periodicity
# f(s+a) = e^{-2 pi i s} e^{(pi^2 + i pi L_t)/t} f(s), a = i pi/t, equal to
#   -e^{i pi s} e^{(-2 pi^2 + i pi L_t)/t} F(s),  s real >= s_A;
# on x_A - i pi + e^{i theta}[0,oo) the E- integrand is  -e^{-i pi s} e^{(-2 pi^2 - i pi L_t)/t} F(s).
# On the real s-ray Re(Phi(x) e^{-i theta}) <= L^2/(4 cos theta) + pi^2/12 (as in certify_landscape.py).
ray = L ** 2 / (4 * COS) + PI ** 2 / 12
rp = ray + (-2 * PI ** 2) * COS + (PI * L) * SIN
rm = ray + (-2 * PI ** 2) * COS - (PI * L) * SIN
print("ray x_A+i pi+e^{i theta}R+ (E+): sup Om - T' <= %+.4f" % float(hi(rp - TP_LO)))
print("ray x_A-i pi+e^{i theta}R+ (E-): sup Om - T' <= %+.4f" % float(hi(rm - TP_LO)))
# head: r log|b_k| <= R_HI log(4e/(1.8 R_HI)) (certify_landscape.py), and |p^{+-k}| <= e^{k r} <= e^{R_HI/cos}
z = 2 * iv.mpf(R_HI)
chk09 = 1 - (iv.exp(z) - 1 - z) / z
head = iv.mpf(R_HI) * iv.log(4 * iv.e / (iv.mpf('1.8') * R_HI))
print("head: |1-e^{-z}|/|z| >= %.4f (need >= 0.9); r log|b_k| <= %.5f ; head - T' <= %+.5f"
      % (float(-hi(-chk09)), float(hi(head)), float(hi(head - TP_LO))))
# connector kernels on C+-: 1/|1 - e^{+-2 pi i s}| <= 1/(1 - e^{-pi/(2 tan theta)})
kmin = 1 - iv.exp(-PI / (2 * (SIN / COS)))
print('connector kernel <= %.4f' % float(hi(1 / kmin)))
# saddle geometry: T' - T > 0 and the saddle x_+ sits at arg x_+ < theta (so Im s_+ < 0: J+ is not a
# kernel-side quantity, it is an entire-integrand integral and its path is free)
print("T' - T in", TP - T)

ok = all(v <= -MARGIN for v in res.values()) and hi(hm - TP_LO) < -MARGIN and hi(rp - TP_LO) < -MARGIN \
    and hi(rm - TP_LO) < -MARGIN and hi(head - TP_LO) < -MARGIN and -hi(-chk09) >= mpf('0.9') \
    and hi(kmin * -1) < 0
print('ALL CERTIFIED' if ok else 'FAILED', ' (%.1fs)' % (time.time() - t0))
sys.exit(0 if ok else 1)
