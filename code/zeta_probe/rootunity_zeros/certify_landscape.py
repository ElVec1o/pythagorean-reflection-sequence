# certify_landscape.py -- interval-arithmetic certificate for the landscape inequalities
# (step 4 of the proof that the zeros of B(q)=cos(Z;q^2) accumulate at q=-1; see
#  paper2a.tex, Proposition prop:minusone).
#
# Notation. q=-e^{-t}, t=r e^{i theta}, L=log 4,
#   Phi(x) = x L - x^2 - Li2(e^{-4x})/4 + pi^2/24,
#   W_n(x) = Re( (Phi(x) + 2 pi i n x) e^{-i theta} ),   T(theta) = Phi0 cos(theta),
#   Phi0 = Phi(x0), x0 = log(2+sqrt5)/2.
# A term e^{(Phi(x)+2 pi i n x)/t} has modulus e^{W_n(x)/r}; the main term J0 has modulus
# ~ e^{T/r}.  We certify, for EVERY (theta, R) in the box
#   theta in [theta1-DTH, theta1+DTH],  R = |x_A| in [R_LO, R_HI],  x_A = R e^{i theta},
# that   sup W_n - T < 0   on the four segments
#   arc (n=0):  x = R e^{i phi}, 0 <= phi <= theta
#   C1  (n=1):  x = x_A + i y,   0 <= y <= pi
#   C-  (n=-1): x = x_A - i y,   0 <= y <= pi
#   C+  (n=2):  x = x_A + i y,   0 <= y <= 2 pi
# plus the E-/E+ remainder exponents, the head exponent, and the connector-kernel bound.
#
# Method: mpmath.iv (outward-rounded interval arithmetic, 53-bit).  Each segment is cut into
# cells in its parameter u; on a cell, W_n(u) <= W_n(u_c) + M * |dx/du| * du/2 (mean value
# theorem), where W_n(u_c) is enclosed in interval arithmetic with theta and R carried as
# intervals (so the bound holds on the whole box), and
#   |d/dx (Phi + 2 pi i n x)| = |L - 2x - log(1-e^{-4x}) + 2 pi i n|
#       <= L + 2|x| + max(-log(1-rho), log 2) + pi/2 + 2 pi |n|,   rho >= |e^{-4x}|,
# since |log(1-z)| <= |log|1-z|| + |arg(1-z)| and Re(1-z) > 0 for |z|<1.
# Li2(e^{-4x}) is enclosed by sum_{n<=N} e^{-4nx}/n^2 (each power in polar form, no wrapping)
# plus the square of half-side rho^{N+1}/((N+1)^2 (1-rho)).
# Cells whose bound is not below -MARGIN are bisected.
#
# Run (memory < 100 MB):  perl -e 'alarm 290; exec @ARGV' python3 certify_landscape.py
import sys, time
from mpmath import iv, mpf, mp

iv.prec = 53
mp.prec = 53
PI = iv.pi
L = iv.log(4)
from mpmath import atan as _atan, pi as _pi, log as _log
TH1 = _atan(_pi / _log(4))   # float centre; the box below contains the exact theta1 with room to spare
DTH = mpf('0.001')
TH = iv.mpf([TH1 - DTH, TH1 + DTH])                 # theta box
R_LO, R_HI = mpf('0.0495'), mpf('0.0505')
RB = iv.mpf([R_LO, R_HI])                           # R box
NLI = 120                                            # Li2 truncation
MARGIN = mpf('0.10')                                 # target certified gap per cell (bisect until reached)
COS, SIN = iv.cos(TH), iv.sin(TH)


def hi(x):
    """upper endpoint of an interval, as an exact mpf"""
    return mpf(x._mpi_[1]) if hasattr(x, '_mpi_') else mpf(x)


class C:
    """complex interval (rectangle) with iv.mpf parts"""
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


def cexp(z):
    m = iv.exp(z.re); return C(m * iv.cos(z.im), m * iv.sin(z.im))


def li2_exp(x, rho):
    """enclosure of Li2(e^{-4x}) for Re x >= RE_MIN, |e^{-4x}| <= rho < 1.
    Powers are taken in polar form, z^n = e^{-4n Re x} (cos 4n Im x - i sin 4n Im x),
    which avoids the wrapping effect of repeated rectangular multiplication."""
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


def Wn(x, n, rho):
    """enclosure of W_n(x) = Re((Phi(x)+2 pi i n x) e^{-i theta}), theta in TH"""
    F = x * L - x * x - li2_exp(x, rho) * iv.mpf(0.25) + PI ** 2 / 24 + C(0, 2 * PI * n) * x
    return F.re * COS + F.im * SIN


# ---------------- Phi0, T ----------------
x0 = iv.log(2 + iv.sqrt(5)) / 2
z0sq = 9 - 4 * iv.sqrt(5)                           # e^{-4 x0} = (sqrt5-2)^2
li = iv.mpf(0); pw = iv.mpf(1)
for n in range(1, 60):
    pw = pw * z0sq; li = li + pw / (n * n)
li = li + iv.mpf([0, (z0sq.b ** 60) / (1 - z0sq.b)])
PHI0 = x0 * L - x0 ** 2 - li / 4 + PI ** 2 / 24
T = PHI0 * COS
T_LO = T.a
print('Phi0 in', PHI0, '\ntheta box (deg) [%.5f, %.5f], R box [%s, %s]' % (
    float(TH.a) * 180 / float(PI.a), float(TH.b) * 180 / float(PI.a), R_LO, R_HI))
print('T = Phi0 cos(theta) >= %.6f' % float(T_LO))

# lower bound on Re x on every segment: R cos(theta) (arc: R cos(phi) >= R cos(theta))
RE_MIN = (RB * COS).a
RHO = hi(iv.exp(-4 * iv.mpf(RE_MIN)))
LOGB = iv.mpf(max(hi(-iv.log(1 - iv.mpf(RHO))), hi(iv.log(2)))) + PI / 2
print('min Re x = %.5f, rho = sup|e^{-4x}| <= %.5f, |log(1-e^{-4x})| <= %.4f' % (RE_MIN, RHO, float(hi(LOGB))))


def segment(name, n, xfun, dxdu, absx_max):
    """adaptive mean-value certificate on u in [0,1]; returns sup bound of W_n - T"""
    M = L + 2 * iv.mpf(absx_max) + LOGB + 2 * PI * abs(n)    # |F'| bound (interval; use its sup)
    M = iv.mpf(hi(M)); dxdu = iv.mpf(hi(iv.mpf(dxdu)))
    stack = [(mpf(0), mpf(1))] if False else [(mpf(i) / 64, mpf(i + 1) / 64) for i in range(64)]
    worst = mpf(-10); cells = 0
    while stack:
        a, b = stack.pop()
        uc = (a + b) / 2
        w = Wn(xfun(iv.mpf(uc)), n, RHO)
        bound = hi(w + M * dxdu * (iv.mpf(b) - a) / 2 - T_LO)
        cells += 1
        if bound > -MARGIN and (b - a) > mpf(2) ** -14:
            stack += [(a, uc), (uc, b)]
            continue
        worst = max(worst, bound)
    print('%-34s cells=%5d  |F\'|<=%.2f   certified sup(W_n - T) <= %+.5f' % (name, cells, float(hi(M)), float(worst)), flush=True)
    return worst


t0 = time.time()
xA = lambda: C(RB * COS, RB * SIN)
res = {}
# arc: x = R e^{i theta u}, |dx/du| = R theta
res['arc'] = segment('arc  (n=0)  R e^{i phi}, phi<=theta', 0,
                     lambda u: C(RB * iv.cos(TH * u), RB * iv.sin(TH * u)),
                     hi(RB * TH), R_HI)
res['C1'] = segment('C1   (n=1)  x_A + i y, y<=pi', 1,
                    lambda u: xA() + C(0, PI * u), hi(PI), hi(iv.mpf(R_HI) + PI))
res['C-'] = segment('C-   (n=-1) x_A - i y, y<=pi', -1,
                    lambda u: xA() - C(0, PI * u), hi(PI), hi(iv.mpf(R_HI) + PI))
res['C+'] = segment('C+   (n=2)  x_A + i y, y<=2pi', 2,
                    lambda u: xA() + C(0, 2 * PI * u), hi(2 * PI), hi(iv.mpf(R_HI) + 2 * PI))

# ---------------- remainders after the quasi-periodic shift ----------------
# E-: shifted J0-path (arc and real axis) with factor e^{(-pi^2 - i pi L)/t}:
#   on the real axis W = cos(theta) Phi(x) <= cos(theta) Phi0 (Phi real, concave, max at x0);
#   on the arc W = W_0 (certified above). Extra constant:
cm = -(PI ** 2) * COS - PI * L * SIN
print('E-  shift constant  Re((-pi^2 - i pi L)e^{-i theta}) <= %.4f  (so W - T <= %.4f on the real axis,'
      ' and <= arc bound + this on the arc)' % (float(hi(cm)), float(hi(cm + PHI0 * COS - T_LO))))
# E+: ray x = rho e^{i theta}, rho >= R, factor e^{(-4 pi^2 + 2 pi i L)/t}:
#   Re(Phi(x) e^{-i theta}) <= rho L - rho^2 cos(theta) + pi^2/24 + |Li2|/4 <= L^2/(4 cos theta) + pi^2/12
cp = -4 * PI ** 2 * COS + 2 * PI * L * SIN
rayb = L ** 2 / (4 * COS) + PI ** 2 / 12 + cp
print('E+  ray: sup W - T <= L^2/(4cos) + pi^2/12 + Re((-4pi^2+2pi i L)e^{-i theta}) - T <= %.4f' % float(hi(rayb - T_LO)))
# head: |f(k)| <= (4e/(1.8 k r))^k and k r <= R  =>  r log|f(k)| <= R_HI log(4e/(1.8 R_HI))
# (valid since |1-e^{-z}| >= 0.9|z| for |z| <= 2 R_HI, and x log(4e/(1.8x)) increases for x<4/1.8)
z = 2 * iv.mpf(R_HI)
chk09 = 1 - (iv.exp(z) - 1 - z) / z
head = iv.mpf(R_HI) * iv.log(4 * iv.e / (iv.mpf('1.8') * R_HI))
print('head: |1-e^{-z}|/|z| >= %.4f (need >= 0.9);  r log|f(k)| <= %.5f ;  head - T <= %+.5f'
      % (float(-hi(-chk09)), float(hi(head)), float(hi(head - T_LO))))
# kernel on connectors: |1 + e^{-v e^{-i theta}}| >= 1 - e^{-pi/(2 tan theta)} for all v >= 0
kmin = 1 - iv.exp(-PI / (2 * (SIN / COS)))
print('connector kernel: 1/|1-e^{-+2 pi i s}| <= %.4f' % float(hi(1 / kmin)))

ok = all(v < 0 for v in res.values()) and hi(cm + PHI0 * COS - T_LO) < 0 and hi(rayb - T_LO) < 0 \
    and hi(head - T_LO) < 0 and -hi(-chk09) >= mpf('0.9') and hi(kmin * -1) < 0
print('ALL CERTIFIED' if ok else 'FAILED', ' (%.1fs)' % (time.time() - t0))
sys.exit(0 if ok else 1)
