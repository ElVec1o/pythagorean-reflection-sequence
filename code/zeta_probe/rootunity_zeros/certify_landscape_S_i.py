# certify_landscape_S_i.py -- Room J step (T). Interval certificate for the landscape of the bulk
# q-cosines S_pm(q) = sum_k b_k q^{pm k} near q = i. Same machinery, paths G-, G+ and start box as
# certify_landscape_i.py (which is for B); only the kernel and the main path change:
#   S_pm = sum_s (-1)^s G(s) on each branch (G = f_e e^{-+x} or +-i f_o e^{-+x}), kernel 1/(2i sin pi s)
#   = e^{-i pi s}/(1-e^{-2 pi i s}) = e^{-i pi s} + e^{-3 i pi s} K-  below, = -e^{i pi s}/(1-e^{2 pi i s}) above:
#   EXACT split  S = J_S + R_S- + R_S+,  J_S = int_{Pi_S} G e^{-i pi s} ds (nu = -1/2, saddle y0),
#   R_S- = int_{G-} G e^{-3 i pi s} K- ds (all nu <= -3/2), R_S+ = +int_{G+} G e^{i pi s}/(1-e^{2 pi i s}) ds (sign: the upper path enters with -k(s))
#   (all nu >= +1/2). Leading exponents W_nu, U_nu as below with n -> nu half-integer.
#   y0 = log(4+sqrt15)/4 + i pi/8, Phi'(y0) = i pi/2 exactly (e^{-4 y0} = -i(4-sqrt15)), T_S = W_{-1/2}(y0).
#   Pi_S: x_c -> vertically to Im x = pi/8 -> horizontally through y0. Crosses Re x = 0 at i pi/8.
#   The factor e^{-+x} is O(1) in the exponent: it adds |x| to Lambda and <= R_MAX to the tail slopes.
# Original header of certify_landscape_i.py follows.
# certify_landscape_i.py -- interval-arithmetic certificate for the landscape inequalities of
# B(q) = sum_k b_k,  b_k = (-2(1-q))^k q^{k^2}/(q;q)_{2k},  near q = i  (Room J, step (c)).
# Companion of certify_landscape.py (q=-1, paper2a prop:minusone Step 4). Bounds used here are
# Lemma lem:qi-bounds of qi_bounds.tex (step (b)).
#
# ---------------------------------------------------------------------------------------------
# SETUP.  q = i e^{-t}, p = e^{-t}, P = p^4, t = r e^{i theta}, theta in TH = theta_i +- 1e-3,
#   theta_i = arctan(pi/(6 log 2)) = 37.067 deg,  0 < r <= R_MAX = 0.005.
#   f_e(s) interpolates b_{2s}, f_o(s) interpolates b_{2s+1} (ident.py).  Coordinates:
#   x = 2 s t on the even branch, x = (2s+1) t on the odd branch.  c0 = -2+2i, Lw = log c0,
#     Phi(x) = x Lw - x^2 - Li2(e^{-8x})/16 + pi^2/96                       (Re x >= 0)
#     U(x)   = Re((x Lw - x^2 + 17 pi^2/96 + Li2(e^{8x})/16) e^{-i theta})
#              + sum_{rho=0..3} max_{m = rho mod 4} (1/2) Re((x - i pi m/4)^2 e^{-i theta})   (Re x <= 0)
#   A kernel term e^{2 pi i n s} has modulus e^{-n pi Im(x e^{-i theta})/r}, so the leading
#   exponent (in units 1/r) of |f e^{2 pi i n s}| is
#     W_n(x) = Re((Phi(x) + i pi n x) e^{-i theta})   (Re x >= 0),
#     U_n(x) = U(x) - n pi Im(x e^{-i theta})           (Re x <= 0, an UPPER bound, via theta reflection).
#   Saddles (PROVED in closed form, see qi_bounds.tex):  x0 = log(4+sqrt15)/4 + 3 i pi/8 (n = 0),
#   xm = x0 - i pi/2 (n = -1);  Phi'(x0) = 0 and Phi'(xm) - i pi = 0 exactly, because
#   (4+sqrt15)(1+(4-sqrt15)^2) = 8.  Heights T0 = W_0(x0), Tm = W_{-1}(xm); T0 = Tm = -0.0706856 at theta_i.
#   T_LO := min over the theta box of min(T0, Tm).
#
# CONTOURS.  B = int_{G-} F K- ds + int_{G+} F K+ ds  (F = f_e or f_o, each branch separately),
#   K- = 1/(1-e^{-2 pi i s}),  K+ = e^{2 pi i s}/(1-e^{2 pi i s}),  both paths leaving a half-integer
#   s_c < 0 chosen per branch so that |x_c| is within r of (pi/8)/sin(theta):  x_c lies in the box
#   B_c = [xc* - EPS, xc* + EPS] x [-pi/8 - EPS, -pi/8 + EPS],  xc* = -(pi/8) cot(theta_i).  No head:
#   f_e, f_o vanish at the negative integers.  K- = 1 + e^{-2 pi i s} + e^{-4 pi i s} K-, and the
#   entire integrand F (term n=0) is moved from G- to Pi_0.  This gives the EXACT split
#     B = J_0 + J_- + R_- + R_+,
#     J_0 = int_{Pi_0} F ds             (n = 0,  saddle x0),
#     J_- = int_{G-} F e^{-2 pi i s} ds  (n = -1, saddle xm),
#     R_- = int_{G-} F e^{-4 pi i s} K- ds   (ALL n <= -2 at once),
#     R_+ = int_{G+} F K+ ds                 (ALL n >= 1 at once).
#   Paths (x-plane):
#     G-   : x_c -> (connector inside B_c, direction e^{i theta/2} or e^{-i pi/4}) -> line Im x = -pi/8,
#            then horizontally to +oo, through xm.  Crosses Re x = 0 at -i pi/8.
#     Pi_0 : x_c -> vertically to Im x = 3 pi/8 (crossing the negative real axis), then horizontally to
#            +oo, through x0.  Crosses Re x = 0 at 3 i pi/8.
#     G+   : x_c -> i pi/8 (straight) -> ray i pi/8 + rho e^{i psi0}, psi0 = 55 deg.  Crosses Re x = 0
#            at i pi/8.
#   G- stays in Im s < 0 and G+ in Im s > 0 (Im s = Im(x e^{-i theta})/(2r)), both end in the decay
#   sector |arg x - theta/2| < pi/4.  Every crossing of Re x = 0 is at Im x = pi/8 mod pi/4.
#
# TAIL IN n (PROVED; this is the "analytic tail in n").  R_- and R_+ carry the whole geometric tails
#   sum_{n<=-2} e^{2 pi i n s} = e^{-4 pi i s} K-  and  sum_{n>=1} e^{2 pi i n s} = K+, so no term
#   is truncated.  The only thing needed is |1/(1-e^{-+2 pi i s})| <= KAPPA along G-+.  Proof: write
#   s - s_c = D = |D| e^{i alpha}.  Each piece of G+ has rotated direction arg(dx e^{-i theta}) in
#   [a1, a2], a subset of (0, pi), so D, a sum of such vectors, lies in the same cone; alpha' :=
#   min(alpha, pi - alpha) >= a_min.  Since e^{2 pi i s_c} = -1,  |1 - e^{2 pi i s}| = |1 + e^{-A+iB}|
#   with A = 2 pi |D| sin(alpha) >= 0 and B = 2 pi |D| cos(alpha).  If |B| <= pi/2 this is >= 1;
#   otherwise A = |B| tan(alpha') >= (pi/2) tan(a_min) and it is >= 1 - e^{-A}.  Hence
#   KAPPA = 1/(1 - exp(-(pi/2) tan a_min)).  G- is the mirror case.
#
# TAIL IN x (PROVED).  For Re x >= X, |z| <= e^{-2X} for every Pochhammer argument z, so
#   r log|prod_j (z_j;P)| <= e^{-2X} / ((1-e^{-2X}) cos(theta) (1 - 2 r cos theta)) =: tau(X)
#   (from -log|1-w| <= -log(1-|w|) <= |w|/(1-|w|) and 1-|P| >= 4 r cos(theta)(1 - 2r cos theta)).
#   So on the horizontal rays Re x >= X_T the leading exponent is at most
#   Wt_n(x) = Re((x(Lw + i pi n) - x^2 + pi^2/96) e^{-i theta}) + tau(X_T).  d/dRe x Wt_n =
#   Re((Lw + i pi n - 2 i Im x) e^{-i theta}) - 2 Re x cos(theta) is decreasing in Re x.  We certify
#   Wt_n(X_T) < T_LO and a slope <= -SLOPE < 0 at X_T.  The same holds on the G+ ray for rho >= RHO_T
#   (slope in rho: Re((Lw + i pi - i pi/4) e^{i(psi0-theta)}) - 2 rho cos(2 psi0 - theta), with cos > 0).
#   The lower-order term r(|x|/sqrt2 + c_l r |x|) of the lemma adds at most 0.72 R_MAX to the slope.
#
# METHOD.  mpmath.iv (outward rounding, 53 bits), theta carried as an interval, x_c as the box B_c.
#   Each path is cut into cells in its parameter u.  On a cell,
#     sup W <= W(center) + sup_cell |F'| * |dx/du| * (cell length)/2,
#   where W(center) is an interval evaluation and sup_cell |F'| is a DERIVATIVE ENCLOSURE over the
#   whole cell:  |Phi' + i pi n| <= |Lw + i pi n - 2x| + |log(1 - e^{-8x})|/2 on Re x >= 0, and
#   for U_n the max over the candidate indices of |Lw + i pi n + 2x - i pi (sum m)/4| + |log(1-e^{8x})|/2
#   (mean value theorem for a max of smooth functions).  |log(1-z)| <= sqrt(log^2|1-z| + (pi/2 min(1,|z|))^2)
#   for |z| <= 1.  The max over m in U is attained at one of the two members of each residue class
#   next to the vertex m* = 4 Im(x e^{-i theta})/(pi cos theta) (the function is a concave quadratic in m),
#   so the candidates are the class members in [m*-4, m*+4].
#   Li2(e^{-+8x}) = sum_{n<=N} z^n/n^2 (powers in polar form) + a tail of modulus
#   <= min(rho^{N+1}/((N+1)^2(1-rho)), 1/N).  Cells are bisected until the bound is below -TARGET
#   or the cell is shorter than MINW.
#   Saddle disks: on x_s + u, |u| <= DELTA (horizontal), W_n(x_s+u) - T_s = Re(u^2 e^{-i theta}
#   int_0^1 (1-tau) Phi''(x_s+tau u) d tau) <= (u^2/2) sup Re(Phi'' e^{-i theta}); we certify the sup < 0.
#   Also computed: the constants of Lemma lem:qi-bounds on every path (D, K, Lambda), c_l, KAPPA, and an
#   explicit r0 below which each competing contribution is <= e^{(T_LO - margin/2)/r}.
#
# Run (memory < 100 MB):  perl -e 'alarm 290; exec @ARGV' python3 certify_landscape_i.py
import sys, time, math
from mpmath import iv, mpf, mp

iv.prec = 53
mp.prec = 53
t_start = time.time()
PI = iv.pi


def hi(x):
    return mpf(x._mpi_[1]) if hasattr(x, '_mpi_') else mpf(x)


def lo(x):
    return mpf(x._mpi_[0]) if hasattr(x, '_mpi_') else mpf(x)


def I(a, b=None):
    return iv.mpf([a, a if b is None else b])


class C:
    """complex interval (rectangle)"""
    __slots__ = ('re', 'im')

    def __init__(s, re, im=0):
        s.re = iv.mpf(re); s.im = iv.mpf(im)

    def __add__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.re + o.re, s.im + o.im)
    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.re - o.re, s.im - o.im)

    def __neg__(s):
        return C(-s.re, -s.im)

    def __mul__(s, o):
        if not isinstance(o, C):
            o = iv.mpf(o); return C(s.re * o, s.im * o)
        return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
    __rmul__ = __mul__

    def absh(s):
        """upper bound of |z|"""
        a = max(abs(lo(s.re)), abs(hi(s.re))); b = max(abs(lo(s.im)), abs(hi(s.im)))
        return hi(iv.sqrt(iv.mpf(a) ** 2 + iv.mpf(b) ** 2))


def cexp(z):
    m = iv.exp(z.re); return C(m * iv.cos(z.im), m * iv.sin(z.im))


# ---------------- parameters ----------------
THI = iv.atan2(PI, 6 * iv.log(2))          # theta_i (enclosure)
DTH = mpf('0.001')
TH = iv.mpf([lo(THI) - DTH, hi(THI) + DTH])
COS, SIN = iv.cos(TH), iv.sin(TH)
R_MAX = mpf('0.005')
EPS = mpf('0.02')                          # half-size of the start box B_c
DELTA = mpf('0.4')                         # saddle half-window
X_T = mpf('2.5')                           # horizontal paths certified up to Re x = X_T
PSI0 = iv.mpf(55) * PI / 180               # G+ ray direction
RHO_T = mpf('5')                           # G+ ray certified up to rho = RHO_T
TARGET = mpf('0.10')
MINW = mpf(2) ** -13
LW = C(iv.log(2 * iv.sqrt(2)), 3 * PI / 4)  # log(-2+2i), principal
P8 = PI / 8
XC_RE = -(P8 * iv.cos(THI) / iv.sin(THI))   # xc* real part (interval)
XC_RE = mpf(lo(XC_RE))                      # a fixed float centre; the box B_c has room EPS
BC_RE = iv.mpf([XC_RE - EPS, XC_RE + EPS])
BC_IM = iv.mpf([lo(-P8) - EPS, hi(-P8) + EPS])


def rot(F):            # Re(F e^{-i theta})
    return F.re * COS + F.im * SIN


def imrot(x):          # Im(x e^{-i theta})
    return x.im * COS - x.re * SIN


def li2e(x, sgn):
    """enclosure of Li2(e^{8 sgn x}); requires sgn*Re x <= 0 so |z| <= 1"""
    a = iv.exp(8 * sgn * x.re); ph = 8 * sgn * x.im
    rho = hi(a)
    if rho > 1:
        raise ValueError('|z|>1 in li2e')
    N = 160 if rho > mpf('0.9') else min(160, int(16 / -math.log(float(rho) + 1e-300)) + 2)
    an = iv.mpf(1); sr = iv.mpf(0); si = iv.mpf(0)
    for n in range(1, N + 1):
        an = an * a
        c = an / (n * n)
        sr = sr + c * iv.cos(n * ph); si = si + c * iv.sin(n * ph)
    if rho < 1:
        tl = min(hi(iv.mpf(rho) ** (N + 1) / ((N + 1) ** 2 * (1 - iv.mpf(rho)))), hi(iv.mpf(1) / N))
    else:
        tl = hi(iv.mpf(1) / N)
    e = iv.mpf([-tl, tl])
    return C(sr + e, si + e)


def logabs_h(z):
    """upper bound of |log(1-z)| for |z| <= 1 (principal branch)"""
    m2 = (1 - z.re) ** 2 + z.im ** 2
    if lo(m2) <= 0:
        return mpf('inf')
    lm = iv.log(m2) / 2
    a = max(abs(lo(lm)), abs(hi(lm)))
    zh = z.absh()
    ab = hi(PI / 2 * min(zh, mpf(1)))
    return hi(iv.sqrt(iv.mpf(a) ** 2 + iv.mpf(ab) ** 2))


# ---------------- leading exponents ----------------
def Phi(x):
    return x * LW - x * x - li2e(x, -1) * (iv.mpf(1) / 16) + PI ** 2 / 96


def W_hi(x, n):                 # sup of W_n on the interval x (Re x >= 0)
    return hi(rot(Phi(x) + C(0, PI * n) * x))


def dW_hi(x, n):                # sup |Phi'(x) + i pi n| on the cell x
    z = cexp(C(-8 * x.re, -8 * x.im))
    return hi(iv.mpf((LW + C(0, PI * n) - 2 * x).absh()) + logabs_h(z) / 2)


def candidates(x):
    ms = 4 * imrot(x) / (PI * COS)
    a = int(math.floor(float(lo(ms)))) - 5; b = int(math.ceil(float(hi(ms)))) + 5
    cls = {rr: [m for m in range(a, b + 1) if m % 4 == rr and lo(ms) - 4 <= m <= hi(ms) + 4] for rr in range(4)}
    for rr in range(4):
        if not cls[rr]:       # defensive: keep the two nearest members
            cls[rr] = [m for m in range(a, b + 1) if m % 4 == rr]
    return cls, max(abs(lo(ms)), abs(hi(ms)))


def U_hi(x, n):                 # sup of U_n on the interval x (Re x <= 0)
    base = x * LW - x * x + PI ** 2 * 17 / 96 + li2e(x, 1) * (iv.mpf(1) / 16)
    v = rot(base) - PI * n * imrot(x)
    cls, _ = candidates(x)
    for rr in range(4):
        best = None
        for m in cls[rr]:
            y = x - C(0, PI * m / 4)
            w = hi(rot(y * y) / 2)
            best = w if best is None else max(best, w)
        v = v + iv.mpf(best)
    return hi(v)


def dU_hi(x, n):
    cls, _ = candidates(x)
    sums = {0}
    for rr in range(4):
        sums = {s + m for s in sums for m in cls[rr]}
    z = cexp(C(8 * x.re, 8 * x.im))
    lg = logabs_h(z) / 2
    best = mpf(0)
    for sm in sums:
        g = LW + C(0, PI * n) + 2 * x - C(0, PI * sm / 4)
        best = max(best, g.absh())
    return hi(iv.mpf(best) + iv.mpf(lg))


# ---------------- saddle heights ----------------
y0 = C(iv.log(4 + iv.sqrt(15)) / 4, P8)
FS = Phi(y0) - C(0, PI / 2) * y0
TS = rot(FS)
T_LO = lo(TS); T_HI = hi(TS)
x0 = y0
# exact saddle equations (Phi'(x0) = 0, Phi'(xm) - i pi = 0): real part 0.5*log(8/((4+s15)(1+(4-s15)^2)))
chk = iv.log(8 / ((4 + iv.sqrt(15)) * (1 + (4 - iv.sqrt(15)) ** 2))) / 2
print('theta box (deg) [%.5f, %.5f];  r <= %s' % (lo(TH) * 180 / math.pi, hi(TH) * 180 / math.pi, R_MAX))
print('T_S = W_{-1/2}(y0) in [%.8f, %.8f];  T_LO := min = %.8f' % (lo(TS), hi(TS), T_LO))
chkS = LW - 2 * y0 - C(iv.log(8 * (4 - iv.sqrt(15))) / 2, 0) - C(0, PI / 2)
print("Phi'(y0) - i pi/2 in [%.1e,%.1e] + i[%.1e,%.1e]  (identity: exactly 0)" % (lo(chkS.re), hi(chkS.re), lo(chkS.im), hi(chkS.im)))
print("Re Phi'(x0) = 0.5 log(8/((4+sqrt15)(1+(4-sqrt15)^2))) in [%.2e, %.2e]  (identity: exactly 0)" % (lo(chk), hi(chk)))
sys.stdout.flush()

# ---------------- generic cell certifier ----------------
results = {}


def certify(name, xfun, dxdu, fval, fder, n, u0, u1, ncell=32, target=TARGET):
    dxdu = mpf(dxdu)
    stack = [(u0 + (u1 - u0) * mpf(i) / ncell, u0 + (u1 - u0) * mpf(i + 1) / ncell) for i in range(ncell)]
    worst = mpf(-100); cells = 0; minw = (u1 - u0) * MINW
    while stack:
        a, b = stack.pop()
        uc = (a + b) / 2
        v = fval(xfun(iv.mpf(uc)), n)
        d = fder(xfun(iv.mpf([a, b])), n)
        bound = hi(iv.mpf(v) + iv.mpf(d) * iv.mpf(dxdu) * (iv.mpf(b) - iv.mpf(a)) / 2 - iv.mpf(T_LO))
        cells += 1
        if bound > -target and (b - a) > minw:
            stack += [(a, uc), (uc, b)]
            continue
        worst = max(worst, bound)
    print('%-58s nu=%+.1f cells=%5d  sup - T_LO <= %+.5f' % (name, n, cells, worst), flush=True)
    results[name + ' nu=%+.1f' % n] = worst
    return worst


def certify_box(name, rer, imr, ns, target=TARGET, quiet=False):
    """2-D box, U-branch (Re x <= 0)"""
    out = {}
    for n in ns:
        stack = [(lo(rer), hi(rer), lo(imr), hi(imr))]
        worst = mpf(-100); cells = 0
        while stack:
            a, b, c, d = stack.pop()
            xc = C(iv.mpf((a + b) / 2), iv.mpf((c + d) / 2))
            X = C(iv.mpf([a, b]), iv.mpf([c, d]))
            hd = hi(iv.sqrt(iv.mpf(b - a) ** 2 + iv.mpf(d - c) ** 2) / 2)
            bound = hi(iv.mpf(U_hi(xc, n)) + iv.mpf(dU_hi(X, n)) * iv.mpf(hd) - iv.mpf(T_LO))
            cells += 1
            if bound > -target and (b - a) > MINW:
                m1 = (a + b) / 2; m2 = (c + d) / 2
                stack += [(a, m1, c, m2), (m1, b, c, m2), (a, m1, m2, d), (m1, b, m2, d)]
                continue
            worst = max(worst, bound)
        if not quiet:
            print('%-58s nu=%+.1f cells=%5d  sup - T_LO <= %+.5f' % (name, n, cells, worst), flush=True)
        results[name + ' nu=%+.1f' % n] = worst


# x_c (both branches, all r <= R_MAX, theta in TH) and the G- connector lie in B_c  (PROVED here):
# |x_c| in (pi/8)/sin(theta) +- r;  connector to Im x = -pi/8 has horizontal extent <= |Im x_c + pi/8|/tan(theta/2)
RHO_C = P8 / SIN + iv.mpf([-R_MAX, R_MAX])
XR = -RHO_C * COS; XI = -RHO_C * SIN
SH = iv.mpf(max(abs(lo(XI + P8)), abs(hi(XI + P8)))) / iv.tan(TH / 2)
bc_ok = lo(XR) - hi(SH) >= lo(BC_RE) and hi(XR) + hi(SH) <= hi(BC_RE) and lo(XI) >= lo(BC_IM) and hi(XI) <= hi(BC_IM)
print('x_c in [%.5f,%.5f] + i[%.5f,%.5f], connector shift <= %.5f  => inside B_c: %s' % (lo(XR), hi(XR), lo(XI), hi(XI), hi(SH), bc_ok))

# P1: start box, all three exponents
NUS = [mpf(-0.5), mpf(-1.5), mpf(0.5)]
for nu in NUS:
    certify_box('B_c start box (crossing of the negative s-axis)', BC_RE, BC_IM, [nu])
# P2: Pi_S vertical, Re x in B_c, Im x from -pi/8-EPS to pi/8 (U, nu=-1/2)
y_lo = lo(-P8) - EPS; y_hi = hi(P8)
certify('Pi_S vertical (crosses the negative real x-axis)', lambda u: C(BC_RE, u), 1, U_hi, dU_hi, mpf(-0.5), y_lo, y_hi)
# P3: Pi_S horizontal Im x = pi/8
Y3 = P8
certify('Pi_S horiz Im=pi/8, Re<=0 (reflection bound)', lambda u: C(u, Y3), 1, U_hi, dU_hi, mpf(-0.5), XC_RE - EPS, mpf(0))
x0r_lo = lo(y0.re) - DELTA; x0r_hi = hi(y0.re) + DELTA
certify('Pi_S horiz Im=pi/8, 0<=Re<=y0-DELTA', lambda u: C(u, Y3), 1, W_hi, dW_hi, mpf(-0.5), mpf(0), x0r_lo)
certify('Pi_S horiz Im=pi/8, y0+DELTA<=Re<=X_T', lambda u: C(u, Y3), 1, W_hi, dW_hi, mpf(-0.5), x0r_hi, X_T)
# P4: G- horizontal Im x = -pi/8, nu = -3/2 (remainder R_S-)
Y4 = -P8
certify('G- horiz Im=-pi/8, Re<=0 (reflection bound)', lambda u: C(u, Y4), 1, U_hi, dU_hi, mpf(-1.5), XC_RE - EPS, mpf(0))
certify('G- horiz Im=-pi/8, 0<=Re<=X_T', lambda u: C(u, Y4), 1, W_hi, dW_hi, mpf(-1.5), mpf(0), X_T)
# P5: G+ segment x_c -> i pi/8, nu = +1/2
XCB = C(BC_RE, BC_IM)
DIR5 = C(0, P8) - XCB
NU = 48
w5 = mpf(-100)
for k in range(NU):
    uI = iv.mpf([mpf(k) / NU, mpf(k + 1) / NU])
    Xk = XCB * (1 - uI) + C(0, P8) * uI
    rer = iv.mpf([lo(Xk.re), min(hi(Xk.re), mpf(0))])
    certify_box('_seg', rer, Xk.im, [mpf(0.5)], quiet=True)
    w5 = max(w5, results.pop('_seg nu=+0.5'))
print('%-58s nu=+1/2 boxes=%5d  sup - T_LO <= %+.5f' % ('G+ segment x_c -> i pi/8 (reflection bound, 2-D)', NU, w5), flush=True)
results['G+ segment nu=+1/2'] = w5
E6 = C(iv.cos(PSI0), iv.sin(PSI0))
certify('G+ ray i pi/8 + rho e^{i 55deg}, rho<=RHO_T', lambda u: C(0, P8) + E6 * u, 1, W_hi, dW_hi, mpf(0.5), mpf(0), RHO_T)

# ---------------- saddle disks: strict concavity along the path ----------------
def conc(name, xs):
    worst = mpf(-100); N = 400
    for i in range(N):
        a = -DELTA + 2 * DELTA * i / N; b = -DELTA + 2 * DELTA * (i + 1) / N
        Y = C(xs.re + iv.mpf([a, b]), xs.im)
        z = cexp(C(-8 * Y.re, -8 * Y.im))
        w = C(1 - z.re, -z.im)
        den = w.re ** 2 + w.im ** 2
        q = z * C(w.re, -w.im)                   # z conj(w)
        d2 = C(-2 - 4 * q.re / den, -4 * q.im / den)
        worst = max(worst, hi(rot(d2)))
    print('%-58s sup Re(Phi\'\' e^{-i theta}) <= %+.5f  => W - T_s <= %+.5f u^2' % (name, worst, worst / 2), flush=True)
    results['concavity ' + name] = worst
    return worst


conc('disk |u|<=DELTA around y0 (nu=-1/2)', y0)

# ---------------- kernel bound KAPPA ----------------
a_minus = TH / 2                                   # G-: connector e^{i theta/2}; e^{-i pi/4} and horizontal are steeper
ang5 = iv.atan2(DIR5.im, DIR5.re) - TH            # G+ segment rotated direction
ang6 = PSI0 - TH
a_plus = min(lo(ang5), lo(ang6), lo(PI - ang5), lo(PI - ang6))
amin = min(lo(a_minus), a_plus)
assert lo(ang5) > 0 and hi(ang5) < hi(PI) and lo(ang6) > 0
KAPPA = hi(1 / (1 - iv.exp(-PI / 2 * iv.tan(iv.mpf(amin)))))
print('kernel: min rotated angle alpha\' >= %.4f rad  =>  |1/(1-e^{-+2 pi i s})| <= KAPPA = %.4f on G-+' % (amin, KAPPA))

# ---------------- tails in x ----------------
tau = lambda X: hi(iv.exp(-2 * iv.mpf(X)) / ((1 - iv.exp(-2 * iv.mpf(X))) * COS * (1 - 2 * iv.mpf(R_MAX) * COS)))
SLACK_LOW = mpf('1.72') * R_MAX          # +R_MAX for the factor e^{-+x}


def tail_h(name, y0, n):
    x = C(iv.mpf(X_T), y0)
    val = hi(rot(x * (LW + C(0, PI * n)) - x * x + PI ** 2 / 96)) + tau(X_T) - T_LO
    slope = hi(rot(LW + C(0, PI * n) - C(0, 2 * y0)) - 2 * iv.mpf(X_T) * COS) + SLACK_LOW
    print('%-58s nu=%+.1f  Wt - T_LO <= %+.4f, slope <= %+.4f' % (name, n, val, slope), flush=True)
    results['tail ' + name + ' nu=%+.1f' % n] = val
    return val < 0 and slope < 0


def tail_ray():
    x = C(0, P8) + E6 * RHO_T
    val = hi(rot(x * (LW + C(0, PI / 2)) - x * x + PI ** 2 / 96)) + tau(lo(x.re)) - T_LO
    slope = hi(rot((LW + C(0, PI / 2) - C(0, P8 * 2)) * E6) - iv.mpf(2 * RHO_T) * iv.cos(2 * PSI0 - TH)) + SLACK_LOW
    ok = lo(iv.cos(2 * PSI0 - TH)) > 0
    print('%-58s nu=+1/2  Wt - T_LO <= %+.4f, slope <= %+.4f' % ('tail G+ ray rho>=RHO_T', val, slope), flush=True)
    results['tail G+ ray nu=+1/2'] = val
    return ok and val < 0 and slope < 0


tails_ok = all([tail_h('tail Pi_S Im=pi/8, Re>=X_T', P8, mpf(-0.5)), tail_h('tail G- Im=-pi/8, Re>=X_T', -P8, mpf(-1.5)),
                tail_ray()])

# ---------------- Lemma lem:qi-bounds constants on the paths ----------------
Dcache = {}


def Dlow(a, phi):
    """lower bound of inf_{rho>=0} max(sigma(phi - rho sin th), 1 - e^{-a - rho cos th}),
    sigma(u) = sin(min(dist(u, 2piZ), pi/2)); monotone in a and phi, so rounded down for caching"""
    a = max(mpf(0), mpf(math.floor(float(a) * 100) / 100)); phi = max(mpf(0), mpf(math.floor(float(phi) * 100) / 100))
    key = (float(a), float(phi))
    if key in Dcache:
        return Dcache[key]
    s_hi = hi(SIN); s_lo = lo(SIN); c_lo = lo(COS)
    best = mpf('0.9'); h = mpf('0.005'); rho = mpf(0)
    while True:
        modl = lo(1 - iv.exp(-iv.mpf(a) - iv.mpf(rho) * c_lo))
        if modl >= mpf('0.9'):
            break
        pl = lo(iv.mpf(phi) - iv.mpf(rho + h) * s_hi); ph = hi(iv.mpf(phi) - iv.mpf(rho) * s_lo)
        if pl <= 0 <= ph:
            d = mpf(0)
        else:
            d = min(abs(pl), abs(ph))
        sig = lo(iv.sin(iv.mpf(min(d, lo(PI / 2)))))
        best = min(best, max(sig, modl))
        rho += h
    Dcache[key] = best
    return best


def dist2pi_lo(I_):
    """lower bound of dist(u, 2 pi Z) over the interval I_"""
    tp = 2 * math.pi
    l, h_ = float(lo(I_)), float(hi(I_))
    k = math.floor(l / tp)
    best = 10.0
    for kk in range(k - 1, k + 3):
        c = kk * tp
        if l - 1e-12 <= c <= h_ + 1e-12:
            return mpf(0)
        best = min(best, abs(l - c), abs(h_ - c))
    return mpf(best) - mpf('1e-9')


roots = [0, 1, 2, 3]   # c = e^{i pi j/2}


def D_of(X, refl):
    D = mpf(1)
    for j in roots:
        if not refl:   # w0 = c e^{-2x}
            a = lo(2 * X.re); argI = PI * j / 2 - 2 * X.im
        else:          # w0 = c^{-1} e^{2x}
            a = lo(-2 * X.re); argI = -PI * j / 2 + 2 * X.im
        D = min(D, Dlow(max(a, mpf(0)), dist2pi_lo(argI)))
    return D


# c_l (PROVED bound for |l(t)/t + (1-i)/2|/|t|, |t| <= R_MAX; l(t) = log(1-(1-i)(1-e^{-t})/2))
rr = iv.mpf(R_MAX)
mu = iv.sqrt(2) / 2 * (iv.exp(rr) - 1)
C_L = hi((iv.sqrt(2) / 2 * (iv.exp(rr) - 1 - rr) + mu ** 2 / (2 * (1 - mu))) / rr ** 2)
D_N = Dlow(mpf(0), lo(PI / 2))
K_N = hi(3 * (iv.mpf(1) / 3) * (1 / iv.mpf(D_N) + 1 / (iv.mpf(D_N) ** 2 * COS)) + iv.mpf('4.75') / D_N + iv.mpf(1) / 6) + mpf('0.001')
print('lemma constants: c_l <= %.4f, D_n >= %.4f, K_n <= %.3f' % (C_L, D_N, K_N))

sups = {'Lam_i': mpf(0), 'K_i': mpf(0), 'Lam_ii': mpf(0), 'K_ii': mpf(0), 'Dmin_i': mpf(1), 'Dmin_ii': mpf(1)}


def lemma_scan(xfun, u0, u1, refl, N=40):
    for i in range(N):
        X = xfun(iv.mpf([u0 + (u1 - u0) * mpf(i) / N, u0 + (u1 - u0) * mpf(i + 1) / N]))
        D = D_of(X, refl); ax = X.absh()
        if D <= 0:
            raise ValueError('D = 0 on a path piece')
        cD = iv.mpf(D)
        lg = max(hi(-iv.log(iv.mpf(D))), hi(iv.log(2)))
        if not refl:
            lam = hi(iv.mpf(ax) / iv.sqrt(2) + iv.mpf(lg))
            K = hi(iv.mpf(C_L) * ax + (iv.mpf(4) / 3 + iv.mpf('8.75')) / cD + (iv.mpf(4) / 3) / (cD ** 2 * COS) + K_N)
            sups['Lam_i'] = max(sups['Lam_i'], lam); sups['K_i'] = max(sups['K_i'], K)
            sups['Dmin_i'] = min(sups['Dmin_i'], D)
        else:
            _, Ms = candidates(X)
            lam = hi(iv.mpf(ax) / iv.sqrt(2) + 2 * iv.mpf(ax) + PI * (iv.mpf(Ms) + 4) / 2 + 2 * PI + iv.mpf(lg))
            K = hi(iv.mpf(C_L) * ax + (iv.mpf(4) / 3 + iv.mpf('4.75')) / cD + (iv.mpf(4) / 3) / (cD ** 2 * COS) + iv.mpf('0.75') + K_N)
            sups['Lam_ii'] = max(sups['Lam_ii'], lam); sups['K_ii'] = max(sups['K_ii'], K)
            sups['Dmin_ii'] = min(sups['Dmin_ii'], D)


lemma_scan(lambda u: C(BC_RE, u), y_lo, y_hi, True)                      # B_c and Pi_0 vertical
lemma_scan(lambda u: C(u, Y3), XC_RE - EPS, mpf(0), True)      # Y3 = pi/8 here
lemma_scan(lambda u: C(u, Y3), mpf(0), X_T, False)
lemma_scan(lambda u: C(u, Y4), XC_RE - EPS, mpf(0), True)
lemma_scan(lambda u: C(u, Y4), mpf(0), X_T, False)
lemma_scan(lambda u: XCB * (1 - u) + C(0, P8) * u, mpf(0), mpf(1), True)
lemma_scan(lambda u: C(0, P8) + E6 * u, mpf(0), RHO_T, False)
sv = dict(sups); sups.update({'Lam_i': mpf(0), 'K_i': mpf(0), 'Dmin_i': mpf(1)})
for xs in (y0,):
    lemma_scan(lambda u: C(xs.re + u, xs.im), -DELTA, DELTA, False, N=16)
print('lemma (i) on the saddle windows |x - x_s| <= DELTA: D >= %.4f, Lambda <= %.3f, K <= %.2f  (error <= K|t|)'
      % (sups['Dmin_i'], sups['Lam_i'], sups['K_i']))
sups = sv
print('lemma on the paths: (i)  D >= %.4f, Lambda <= %.3f, K <= %.2f;  (ii) D\' >= %.4f, Lambda\' <= %.3f, K\' <= %.2f'
      % (sups['Dmin_i'], sups['Lam_i'], sups['K_i'], sups['Dmin_ii'], sups['Lam_ii'], sups['K_ii']))

# ---------------- verdict + explicit r0 ----------------
comp = {k: v for k, v in results.items() if not k.startswith('concavity')}
margin = -max(comp.values())
conc_ok = all(results[k] < 0 for k in results if k.startswith('concavity'))
# Each competing piece: log|integrand * ds/dx| <= (T_LO - margin)/r + Lam + 4 log 3.01 + K r + log KAPPA
#   + 1/2 log(2r/pi) + log(1/(2r)).  Total compact length LEN; tails add a factor <= 2 (slope >= 1 per unit).
XMAX = hi(iv.mpf(RHO_T) + P8)   # |x| on the compact paths (factor e^{-+x})
LAM = max(sups['Lam_i'], sups['Lam_ii']) + XMAX; KK = max(sups['K_i'], sups['K_ii'])
LEN = mpf(40)
A = LAM + 4 * math.log(3.01) + math.log(float(KAPPA)) + math.log(float(LEN)) + math.log(2) - 0.5 * math.log(2 * math.pi)


def hfun(r):     # r*(A + K r - 1/2 log r) : bound on r * log(total competing / e^{(T_LO-margin)/r})
    return r * (A + float(KK) * r - 0.5 * math.log(r))


lo_r, hi_r = 1e-12, float(R_MAX)
if hfun(hi_r) <= float(margin) / 2:
    r0 = hi_r
else:
    for _ in range(200):
        mid = math.sqrt(lo_r * hi_r)
        if hfun(mid) <= float(margin) / 2:
            lo_r = mid
        else:
            hi_r = mid
    r0 = lo_r
mono = A + 2 * float(KK) * r0 - 0.5 * math.log(r0) - 0.5 > 0      # h increasing on (0, r0]
print('certified margin (all competing pieces): %.5f ;  explicit r0 = %.3e  (h increasing on (0,r0]: %s)'
      % (margin, r0, mono))
ok = bc_ok and margin > 0 and conc_ok and tails_ok and mono and KAPPA < 10
print('ALL CERTIFIED' if ok else 'FAILED', ' (%.1fs)' % (time.time() - t_start))
sys.exit(0 if ok else 1)
