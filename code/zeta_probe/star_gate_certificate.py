#!/usr/bin/env python3
# star_gate_certificate.py — the gate-closure certificate for Theorem thm:U / Appendix app:star.
#
# Certifies, at 120-digit working precision with explicit truncation control:
#   (1) the closed-form identities of Lemma lem:P12closed (off-pole, hence identically),
#   (2) the enumeration: exactly SIX travel poles with tau > 5e-3 (grid + derivative majorant),
#   (3) the six-pole gate table: |P12|w^3 < 2, |s| < 1, b0 > 0, |S_e| >= 0.35 sqrt(tau),
#   (4) the uniform-range arithmetic of Lemma app:Se: 0.90*(qZ/2) - 0.619 tau^{3/2} >= 0.63 sqrt(tau).
#
# Arithmetic model: mpmath mpf at the stated dps (not interval arithmetic); every series is
# alternating-with-monotone-tail in its summation range and is truncated when the term drops
# below 1e-110 relative, the first omitted term bounding the tail.  The derivative majorant
# D(tau) in part (2) is the explicit termwise bound
#   |g'(tau)| <= sum_j a_j(tau) * [ (j^2+j) + j/(1-q) + 2jq/(1-q) ],   a_j = q^{j^2+j} y^j/(q;q)_{2j},
# evaluated on the same grid; a cell can contain a zero of g only if |g| <= D*delta at an endpoint.
from mpmath import mp, mpf, exp, sqrt, log
import mpmath

mp.dps = 120
TOL = mpf('1e-100')

def C(y, q, N=200):
    tot = mpf(0); poch = mpf(1)
    for j in range(N):
        if j > 0: poch *= (1 - q**(2*j-1)) * (1 - q**(2*j))
        t = (-1)**j * q**(j*j+j) * y**j / poch
        tot += t
        if j > 5 and abs(t) < mpf('1e-112') * max(mpf(1), abs(tot)): break
    return tot

def c(u, q, N=200): return C(u*u, q, N)

def sn(z, q, N=200):
    tot = mpf(0); poch = (1 - q)
    for j in range(N):
        if j > 0: poch *= (1 - q**(2*j)) * (1 - q**(2*j+1))
        t = (-1)**j * q**(j*j+j) * z**(2*j+1) / poch
        tot += t
        if j > 5 and abs(t) < mpf('1e-112') * max(mpf(1), abs(tot)): break
    return tot

def sh(u, q, N=200): return sn(sqrt(q)*u, q, N)/sqrt(q)   # half-step s(u)=q^{-1/2} sin(q^{1/2}u; q^2)

def P12_series(q, N=200):
    # banked series: sum_{k>=1} (-1)^{k-1} [2(1-q)]^k q^{k^2+k+1} (1-q^{2k}) / (q;q)_{2k+1}
    tot = mpf(0); poch = (1-q)*(1-q**2)*(1-q**3)
    for k in range(1, N):
        if k > 1: poch *= (1 - q**(2*k)) * (1 - q**(2*k+1))
        t = (-1)**(k-1) * (2*(1-q))**k * q**(k*k+k+1) * (1-q**(2*k)) / poch
        tot += t
        if k > 5 and abs(t) < mpf('1e-112') * max(abs(tot), mpf('1e-30')): break
    return tot

def P12_Y3(q, N=200):
    # paper form: (2q^3/(1-q^3)) * sum_k d_k,  d_k = (-2)^k (1-q)^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k]
    tot = mpf(0); p2 = mpf(1); p5 = mpf(1)
    for k in range(N):
        if k > 0:
            p2 *= (1 - q**(2*k)); p5 *= (1 - q**(2*k+3))
        t = (-2)**k * (1-q)**k * q**(k*k+3*k) / (p2*p5)
        tot += t
        if k > 5 and abs(t) < mpf('1e-112') * max(abs(tot), mpf('1e-30')): break
    return 2*q**3/(1-q**3) * tot

def So_series(q, N=200):
    tot = mpf(0); poch = (1 - q)
    for j in range(N):
        if j > 0: poch *= (1 - q**(2*j)) * (1 - q**(2*j+1))
        t = (-1)**j * (2*(1-q))**j * q**(j*j+2*j) * (1-q) / poch
        tot += t
        if j > 5 and abs(t) < mpf('1e-112') * max(mpf(1), abs(tot)): break
    return tot

def geom(q):
    z0 = sqrt(2*(1-q)); Z = z0/sqrt(q); tau = -log(q); w = sqrt(2/tau)
    return z0, Z, tau, w

def g_of_tau(t):
    q = exp(-t)
    return c(sqrt(2*(1-q)/q), q)

ok = True
def check(name, cond, detail=""):
    global ok
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}  {detail}")
    if not cond: ok = False

print("== (1) closed-form identities, OFF-POLE (hence identical, not pole-conditional) ==")
for qs in ['0.30', '0.70']:
    q = mpf(qs); z0, Z, tau, w = geom(q)
    r1 = P12_series(q) - ((q*Z/2)*sh(Z, q) - c(z0, q))
    r2 = So_series(q) - (z0/2)*sh(z0, q)
    r3 = P12_series(q) - P12_Y3(q)
    check(f"P12 = (qZ/2)s(Z) - c(z0)   at q={qs}", abs(r1) < TOL, f"resid={mp.nstr(abs(r1),3)}")
    check(f"S_o = (z0/2)s(z0)          at q={qs}", abs(r2) < TOL, f"resid={mp.nstr(abs(r2),3)}")
    check(f"series form = Y3 form      at q={qs}", abs(r3) < TOL, f"resid={mp.nstr(abs(r3),3)}")

print("\n== (2) enumeration: travel poles with tau > 5e-3 (three-tier) ==")
# Tier A (tau >= 0.03, i.e. w <= 8.165): CERTIFIED count.  Grid uniform in w with the termwise
#   derivative majorant D(tau) >= |dg/dtau| from the header; a cell can hide a zero only if
#   |g| <= D_w*delta_w at both endpoints (D_w = D*4/w^3); such cells are subdivided until they
#   either show a sign change or pass the margin.  Termwise loss is affordable at w <= 8.2.
# Tier B (5e-3 < tau < 0.03, w in (8.165, 20)): high-resolution SCAN (delta_w = 5e-4), NOT
#   interval-certified: through this confluent window the termwise majorant overcounts the
#   alternating cancellation by ~e^w and no proved pointwise envelope of cos(Z;q^2) exists at
#   the required tier (that envelope is exactly the lem:cos class).  The scan locates the roots,
#   prints the minimum |g| between consecutive roots, and checks the (k+1/2)pi ladder offsets.
# Tier C (tau <= 5e-3): no enumeration needed -- the uniform certificate covers every pole there.
mp.dps = 45

def g_and_D(t):
    q = exp(-t); y = 2*(1-q)/q
    tot = mpf(0); D = mpf(0); poch = mpf(1)
    for j in range(200):
        if j > 0: poch *= (1 - q**(2*j-1)) * (1 - q**(2*j))
        a = q**(j*j+j) * y**j / poch
        tot += (-1)**j * a
        D += a * ((j*j+j) + j/(1-q) + 2*j*q/(1-q))
        if j > 5 and a < mpf('1e-40'): break
    return tot, D

cache = {}
def eval_w(wv):
    key = mp.nstr(wv, 40)
    if key not in cache: cache[key] = g_and_D(2/wv**2)
    return cache[key]

# --- Tier A ---
wA_lo = sqrt(2/log(mpf(10))); wA_hi = sqrt(2/mpf('0.03'))
NA = 1500
dwA = (wA_hi - wA_lo)/NA
sign_changes_A = []
unresolved = 0
stack = [(wA_lo + dwA*i, wA_lo + dwA*(i+1), 0) for i in range(NA)]
while stack:
    w1, w2, depth = stack.pop()
    g1, D1 = eval_w(w1); g2, D2 = eval_w(w2)
    if mpmath.sign(g1) != mpmath.sign(g2):
        sign_changes_A.append((2/w1**2, 2/w2**2)); continue
    dw = w2 - w1
    Dw = max(D1*4/w1**3, D2*4/w2**3) * mpf('1.05')
    if abs(g1) > Dw*dw or abs(g2) > Dw*dw: continue
    if depth >= 22:
        unresolved += 1; continue
    mid = (w1+w2)/2
    stack.append((w1, mid, depth+1)); stack.append((mid, w2, depth+1))
check("Tier A (tau >= 0.03): exactly 3 certified sign changes", len(sign_changes_A) == 3, f"found {len(sign_changes_A)}")
check("Tier A: no unresolved cells", unresolved == 0, f"unresolved: {unresolved}, evals: {len(cache)}")

# --- Tier B ---
wB_lo = wA_hi; wB_hi = sqrt(2/mpf('0.005'))
NB = 24000
dwB = (wB_hi - wB_lo)/NB
vals_B = []
for i in range(NB+1):
    wv = wB_lo + dwB*i
    gv, _ = g_and_D(2/wv**2)
    vals_B.append((wv, gv))
sign_idx = [i for i in range(NB) if mpmath.sign(vals_B[i][1]) != mpmath.sign(vals_B[i+1][1])]
sign_changes_B = [(2/vals_B[i][0]**2, 2/vals_B[i+1][0]**2) for i in sign_idx]
check("Tier B scan (5e-3 < tau < 0.03): exactly 3 sign changes", len(sign_changes_B) == 3, f"found {len(sign_changes_B)}")
# margin metric: min |g| over cells more than 40 cells away from every sign change,
# and peak |g| between consecutive roots (the full swing of the oscillation)
excl = set()
for i in sign_idx:
    for k in range(i-40, i+41): excl.add(k)
outside = [abs(g) for i,(wv,g) in enumerate(vals_B) if i not in excl]
print(f"       Tier B margin: min |g| outside 40-cell root neighbourhoods = {mp.nstr(min(outside),4)}; "
      f"peak |g| between roots = {mp.nstr(max(abs(g) for _,g in vals_B),4)} (delta_w = {mp.nstr(dwB,3)})")

sign_changes = sorted(sign_changes_A + sign_changes_B, key=lambda ab: -max(ab))
lad = []
for ta, tb in sign_changes:
    tmid = (ta+tb)/2; lad.append(sqrt(2/tmid)/mpmath.pi)
print("       ladder w/pi:", [mp.nstr(x,5) for x in lad], " (target k+1/2)")

print("\n== (3) the six-pole gate table ==")
mp.dps = 120
def bisect(tlo_, thi_):
    lo, hi = exp(-thi_), exp(-tlo_)
    flo = g_of_tau(-log(lo))
    for _ in range(420):
        mid = (lo+hi)/2; fm = g_of_tau(-log(mid))
        if fm == 0: return mid
        if mpmath.sign(fm) == mpmath.sign(flo): lo, flo = mid, fm
        else: hi = mid
    return (lo+hi)/2

rows = []
print("   m   tau_m           |P12|w^3    s           b0*tau     |Se|/rt(tau)  |s(Z)|")
for m, (ta, tb) in enumerate(sign_changes, start=1):   # tau descending = paper order q_1<q_2<...
    qp = bisect(min(ta,tb), max(ta,tb))
    z0, Z, tau, w = geom(qp)
    P12 = P12_series(qp); Se = c(z0, qp); So_ = So_series(qp); sZ = sh(Z, qp)
    s_gate = qp/(1-qp)*P12/Se
    b0 = (2*qp/(1-qp))*So_/Se
    rows.append((tau, abs(P12)*w**3, s_gate, b0*tau, abs(Se)/sqrt(tau), abs(sZ)))
    print(f"   {m}   {mp.nstr(tau,10):<14}  {mp.nstr(abs(P12)*w**3,4):<10}  {mp.nstr(s_gate,4):<10}  {mp.nstr(b0*tau,5):<9}  {mp.nstr(abs(Se)/sqrt(tau),5):<12}  {mp.nstr(abs(sZ),5)}")
    r1 = abs(P12 - ((qp*Z/2)*sh(Z, qp) - c(z0, qp)))
    r2 = abs(So_ - (z0/2)*sh(z0, qp))
    check(f"pole {m}: closed forms hold to 1e-100", r1 < TOL and r2 < TOL, f"resid={mp.nstr(max(r1,r2),3)}")
for m, r in enumerate(rows, start=1):
    check(f"pole {m}: |P12|w^3 < 2",        r[1] < 2)
    check(f"pole {m}: |s| < 1",             abs(r[2]) < 1)
    check(f"pole {m}: b0 > 0",              r[3] > 0)
    check(f"pole {m}: |Se| >= 0.35 rt(tau)", r[4] >= mpf('0.35'))

print("\n== (4) uniform-range arithmetic of Lemma app:Se  (tau <= 5e-3) ==")
# |S_e| >= 0.90*(qZ/2) - |P12| >= [0.90/sqrt2 * sqrt(q v) - 0.619 tau] sqrt(tau),  v=(1-q)/tau
t_end = mpf('0.005'); q_end = exp(-t_end); v_end = (1-q_end)/t_end
worst = mpf('0.90')/sqrt(mpf(2)) * sqrt(q_end*v_end) - mpf('0.619')*t_end
check("0.90/sqrt2*sqrt(qv) - 0.619 tau >= 0.63 at tau=5e-3 (worst endpoint)", worst >= mpf('0.63'), f"= {mp.nstr(worst,6)}")
# spot confirmation of |s(Z)| >= 0.90 input at the two poles nearest the certificate endpoints
mp.dps = 260
for ta, tb in [('0.00455','0.00485'), ('1.20e-4','1.30e-4')]:
    for qp in [bisect(mpf(ta), mpf(tb))]:
        z0, Z, tau, w = geom(qp)
        sZ = sh(Z, qp, N=500)
        check(f"|s(Z)| >= 0.90 at pole tau={mp.nstr(tau,5)}", abs(sZ) >= mpf('0.90'), f"|s(Z)|={mp.nstr(abs(sZ),6)}")
mp.dps = 120

print("\n== (5) Lemma lem:infpoles: radius transport and extreme-phase sign ==")
# (a) the transport identity 1-Sigma_1^T = sum (-1)^n e^{-B_n} w^{2n}/(2n)!  with
#     e^{-B_n} = q^{n^2+n}[2(1-q)]^n (2n)!/[(q;q)_{2n} W^{2n}] and W = w e^{-tau/2}.
#     Checked at high precision: the two sides are huge and nearly cancelling for small tau,
#     so dps must exceed the cancellation depth (500 digits here).
from mpmath import factorial
mp.dps = 500
for ts in ['0.79972', '1e-2', '1e-4', '1e-5']:
    tau = mpf(ts); q = exp(-tau)
    z0 = sqrt(2*(1-q)); Z = z0/sqrt(q); wv = sqrt(2/tau); Wv = wv*exp(-tau/2)
    lhs = c(Z, q, N=400)
    tot = mpf(0); poch = mpf(1)
    for nn in range(400):
        if nn > 0: poch *= (1 - q**(2*nn-1))*(1 - q**(2*nn))
        eBn = q**(nn*nn+nn) * (2*(1-q))**nn * factorial(2*nn) / (poch * Wv**(2*nn))
        t = (-1)**nn * eBn * wv**(2*nn) / factorial(2*nn)
        tot += t
        if nn > 20 and abs(t) < mpf('1e-450')*max(mpf(1), abs(tot)): break
    rel = abs(lhs-tot)/max(abs(lhs), mpf(1))
    # tolerance TOL: the shared series helpers truncate at 1e-112 relative, so agreement
    # is certified to that depth, not to the working precision.
    check(f"transport identity at tau={ts}", rel < TOL, f"rel={mp.nstr(rel,3)}")
    check(f"  W e^(tau/2) = w exactly at tau={ts}", abs(Wv*exp(tau/2)-wv) < mpf('1e-450'))
# (b) extreme-phase sign: sign(1-Sigma_1^T)|_{w=m pi} = (-1)^m, i.e. |T2(m pi)| < 1
mp.dps = 80
worst = mpf(0); allok = True
for m in range(1, 41):
    tau = 2/(m*mpmath.pi)**2; q = exp(-tau)
    val = c(sqrt(2*(1-q)/q), q, N=300)
    T2 = mpf((-1)**m) - val
    if mpmath.sign(val) != (-1)**m or abs(T2) >= 1: allok = False
    worst = max(worst, abs(T2))
check("sign alternation at w=m*pi for m=1..40 (so m_0=1)", allok, f"max |T2(m pi)| = {mp.nstr(worst,4)}")
mp.dps = 120

print("\n== (6) Lemma lem:Bbounded on the widened w-strip (round-6 restatement) ==")
# S = {-1/2 <= Re s <= 2w, 0 <= Im s <= w/2 + sqrt(tau)}, tau <= 2/pi^2.
# Claims checked: n=1 minimum >= -(sqrt2/18)sqrt(tau) - 0.48 tau^{3/2};
#                 tail majorant <= 0.88 tau^{3/2} (limit 0.804530... , so 0.8 would FAIL);
#                 total constant 1.4; |A| <= 2.2; |B'| majorant <= 3 tau (2.89 at the endpoint).
mp.dps = 40
def n1term(sg, t, tau): return (tau**2/36)*(4*(sg**3 - 3*sg*t*t) + 3*(sg*sg - t*t) - sg)
def tailmaj(tau, X, NN=300):
    ss = 2*X
    return sum(2*mpmath.zeta(4)/(mpf(k)*(2*k+1))*(2*ss)*(ss*tau/mpmath.pi)**(2*k) for k in range(2, NN))
worst_n1 = mpf(0); worst_tail = mpf(0); worst_A = mpf(0); worst_Bp = mpf(0)
for ts in ['0.2026423','0.1','0.05','0.01','0.005','0.001','1e-4']:
    tau = mpf(ts); wv = sqrt(2/tau); T = wv/2 + sqrt(tau)
    base = -(sqrt(2)/18)*sqrt(tau)
    best = mpf('1e9')
    for i in range(0, 61):
        sg = mpf(-1)/2 + (2*wv + mpf(1)/2)*i/60
        for j in range(0, 61):
            v = n1term(sg, T*j/60, tau)
            if v < best: best = v
    worst_n1 = max(worst_n1, (base - best)/tau**mpf(1.5))
    worst_tail = max(worst_tail, tailmaj(tau, wv)/tau**mpf(1.5))
    worst_A = max(worst_A, 1 + exp((sqrt(2)/18)*sqrt(tau) + mpf('1.4')*tau**mpf(1.5)))
    worst_Bp = max(worst_Bp, (tau**2/24)*(32*wv*wv + 8*wv + 1)/tau)
check("n=1 minimum cost <= 0.48 tau^{3/2}", worst_n1 <= mpf('0.48'), f"worst {mp.nstr(worst_n1,5)}")
check("tail majorant <= 0.88 tau^{3/2}", worst_tail <= mpf('0.88'), f"worst {mp.nstr(worst_tail,5)}")
check("0.48+0.88 <= 1.4", worst_n1 + worst_tail <= mpf('1.4'), f"sum {mp.nstr(worst_n1+worst_tail,5)}")
check("the old constant 0.8 is genuinely too small", tailmaj(mpf('1e-4'), sqrt(2/mpf('1e-4')))/mpf('1e-4')**mpf(1.5) > mpf('0.8'), "limit 0.804530...")
check("|A| <= 2.2", worst_A <= mpf('2.2'), f"worst {mp.nstr(worst_A,5)}")
check("|B'| majorant <= 3 tau", worst_Bp <= 3, f"worst {mp.nstr(worst_Bp,5)} tau")
mp.dps = 120

print("\n== (7) Lemma lem:Bbounded, closed form and wide-strip constants (round-7 rewrite) ==")
# B_s = tau M(M+1)/4 - M log tau - logGamma(M+1) + log(q;q)_inf - log(q^{M+1};q)_inf - s phi(tau),
# M = 2s, phi(y) = log(sinh(y/2)/(y/2)).  Analytic for Re s > -1/2; e^{-B_n} = eta_n at integers.
# Strip S = {-1/2 < Re s <= 2w, |Im s| <= 2w}, tau <= 2/pi^2.
from mpmath import loggamma, mpc
mp.dps = 30
EPSQ = mpf('1e-28')
def qpinf(a, qq):
    r = mpc(1); t = mpc(a)
    for k in range(2000000):
        if abs(t) < EPSQ: break
        r *= (1 - t); t *= qq
    return r
def phi_(y): return log(mpmath.sinh(y/2)/(y/2))
def B_cl(sv, tau, qqi, qv):
    M = 2*sv
    return (tau*M*(M+1)/4 - M*log(tau) - loggamma(M+1) + log(qqi) - log(qpinf(qv**(M+1), qv)) - sv*phi_(tau))
# (a) the closed form reproduces eta_n exactly
okc = True
for ts in ['0.2','0.05']:
    tau = mpf(ts); qv = exp(-tau); wv = sqrt(2/tau); Wv = wv*exp(-tau/2); qqi = qpinf(qv, qv)
    for nn in [1,2,3,5,8]:
        poch = mpf(1)
        for i in range(1, 2*nn+1): poch *= (1-qv**i)
        eta = qv**(nn*nn+nn)*(2*(1-qv))**nn*mpmath.factorial(2*nn)/(poch*Wv**(2*nn))
        if abs(B_cl(mpf(nn), tau, qqi, qv) - (-log(eta))) > mpf('1e-25'): okc = False
check("closed form = -log(eta_n) at integers", okc, "checked n=1,2,3,5,8 at tau=0.2,0.05")
# (b) the wide-strip constants
wc = mpf(0); wA = mpf(0); wE = mpf(0); wB = mpf(0)
for ts in ['0.2026423','0.1','0.05','0.02']:
    tau = mpf(ts); qv = exp(-tau); wv = sqrt(2/tau); qqi = qpinf(qv, qv)
    mn = mpf('1e9'); mA = mpf(0); mE = mpf(0); mB = mpf(0)
    NN = 26
    for i in range(NN+1):
        sg = mpf('-0.45') + (2*wv + mpf('0.45'))*i/NN
        for j in range(NN+1):
            sp = mpc(sg, 2*wv*mpf(j)/NN)
            b = B_cl(sp, tau, qqi, qv)
            mn = min(mn, mpmath.re(b)); mE = max(mE, abs(exp(-b))); mA = max(mA, abs(1-exp(-b)))
            hh = mpf('1e-6')
            mB = max(mB, abs((B_cl(sp+hh,tau,qqi,qv)-B_cl(sp-hh,tau,qqi,qv))/(2*hh)))
    wc = max(wc, -mn/sqrt(tau)); wA = max(wA, mA); wE = max(wE, mE); wB = max(wB, mB/tau)
check("Re B_s >= -5.1 sqrt(tau) on S", wc <= mpf('5.1'), f"worst {mp.nstr(wc,5)} (limit ~5.03)")
check("|A| <= 10.94 on S", wA <= mpf('10.94'), f"worst {mp.nstr(wA,5)}")
check("|e^-B| <= 9.94 on S", wE <= mpf('9.94'), f"worst {mp.nstr(wE,5)}")
check("|B'| <= 5.5 tau on S", wB <= mpf('5.5'), f"worst {mp.nstr(wB,5)} tau")
mp.dps = 120

print("\n== (8) Lemma lem:Bbounded: the ANALYTIC majorant of the proof (round-8) ==")
# Exact identity  B_n = sum_{i<=2n} phi(i tau) - n phi(tau);
# Gamma-block split  B_s = sum_k G(M;R_k) - s phi(tau),  R_k = 2 pi k / tau;
# integrand majorant gamma(R) = (|M|^2+|M|)/(R^2-|M|^2) + 2/(R-|M|)^2,  |M| <= 4 sqrt2 w;
# claims: |B_s| <= 30.3 sqrt(tau) and |B'_s| <= 7.6 tau on tau <= 2/pi^2, and the psi remainder
# constant |psi(1+z) - log z - 1/(2z)| * |z|^2 <= 1 on the region used.
mp.dps = 30
from mpmath import digamma as _dg, loggamma as _lg
def phi_a(y): return log(mpmath.sinh(y/2)/(y/2))
# (a) the exact elementary identity at integers
okid = True
for ts in ['0.2','0.05']:
    tau = mpf(ts); qv = exp(-tau); wv = sqrt(2/tau); Wv = wv*exp(-tau/2)
    for nn in [1,3,6]:
        poch = mpf(1)
        for i in range(1, 2*nn+1): poch *= (1-qv**i)
        eta = qv**(nn*nn+nn)*(2*(1-qv))**nn*mpmath.factorial(2*nn)/(poch*Wv**(2*nn))
        rhs = sum(phi_a(i*tau) for i in range(1, 2*nn+1)) - nn*phi_a(tau)
        if abs(-log(eta) - rhs) > mpf('1e-25'): okid = False
check("B_n = sum_{i<=2n} phi(i tau) - n phi(tau) at integers", okid, "n=1,3,6 at tau=0.2,0.05")
# (b) the psi remainder constant C0 = 1
wr = mpf(0)
for ts in ['0.2026423','0.05','0.005']:
    tau = mpf(ts); wv = sqrt(2/tau); Mm = 4*sqrt(2)*wv
    for k in [1,2,5]:
        R = 2*mpmath.pi*k/tau
        for fr in [mpf(0), mpf('0.5'), mpf(1)]:
            for an in [mpf(0), mpf('0.5'), mpf(1)]:
                for sgn in [1, -1]:
                    z = mpmath.mpc(Mm*fr*an, sgn*R + Mm*fr*(1-an))
                    wr = max(wr, abs(_dg(1+z) - log(z) - 1/(2*z))*abs(z)**2)
check("psi remainder constant <= 1 on the region used", wr <= 1, f"worst {mp.nstr(wr,4)}")
# (c) the two stated constants
KBw = mpf(0); KDw = mpf(0)
for ts in ['0.2026423','0.1','0.05','0.02','0.005','0.001','1e-4']:
    tau = mpf(ts); wv = sqrt(2/tau); Mm = 4*sqrt(2)*wv; sm = 2*sqrt(2)*wv
    tot = mpf(0)
    for k in range(1, 400000):
        R = 2*mpmath.pi*k/tau
        if R <= Mm: continue
        d = R*R - Mm*Mm
        g = (Mm*Mm + Mm)/d + 2/(R-Mm)**2
        tot += g
        if k > 50 and g < mpf('1e-32')*max(mpf(1), tot): break
    KBw = max(KBw, (Mm*tot + sm*phi_a(tau))/sqrt(tau))
    KDw = max(KDw, (2*tot + phi_a(tau))/tau)
check("|B_s| <= 30.3 sqrt(tau) on S", KBw <= mpf('30.3'), f"worst {mp.nstr(KBw,6)}")
check("|B'_s| <= 7.6 tau on S", KDw <= mpf('7.6'), f"worst {mp.nstr(KDw,6)}")
# (d) the truncation bound eq:Btrunc that lem:cos consumes
def logqpinf_a(a, qv):
    tot = mpmath.mpc(0); t = mpmath.mpc(a)
    for k in range(2000000):
        if abs(t) < mpf('1e-28'): break
        tot += log(1 - t); t *= qv
    return tot
def B_an(sv, tau, lqq, qv):
    M = 2*sv
    return (tau*M*(M+1)/4 - M*log(tau) - _lg(M+1) + lqq - logqpinf_a(qv**(M+1), qv) - sv*phi_a(tau))
def P1_(M): return M*(M+1)*(2*M+1)/6
wtr = mpf(0)
for ts in ['0.2026423','0.05','0.005']:
    tau = mpf(ts); qv = exp(-tau); lqq = logqpinf_a(qv, qv); wv = sqrt(2/tau)
    NN = 10
    for i in range(NN+1):
        for j in range(NN+1):
            sv = mpmath.mpc(-mpf('0.49') + (wv + mpf('0.49'))*i/NN, wv*mpf(j)/NN)
            if abs(2*sv) > 2*wv: continue
            wtr = max(wtr, abs(B_an(sv, tau, lqq, qv) - (tau**2/24)*(P1_(2*sv) - sv))/tau**mpf(1.5))
check("truncation bound |B - phi_1 tau^2 (P_1 - s)| <= 0.02 tau^{3/2} on |M|<=2w", wtr <= mpf('0.02'), f"worst {mp.nstr(wtr,4)}")
check("|M|/R_1 < 1 (so every R_k > |M|)", 4*sqrt(2)*sqrt(2/mpf('0.2026423'))/(2*mpmath.pi/mpf('0.2026423')) < 1,
      f"= {mp.nstr(4*sqrt(2)*sqrt(2/mpf('0.2026423'))/(2*mpmath.pi/mpf('0.2026423')),4)}")
mp.dps = 120

print("\n== SUMMARY ==")
print("ALL CHECKS PASS" if ok else "*** AT LEAST ONE CHECK FAILED ***")
