# P2_cert.py -- rigorous (Arb ball arithmetic, python-flint) winding-number certificates for B(zeta e^{-t}).
#   B(q) = sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k},  q = zeta e^{-t},  zeta = e(a/N).
# The terms b_k are huge compared with B near zeta (Gauss-sum cancellation: max|b_k|/|B| up to e^{60} and more), so
# naive ball evaluation over a t-ball is useless.  We use Taylor models:
#   on a piece |t - tc| <= rho we write B = P_n0(h) + E_trunc + E_tail, h = t - tc, where
#   * P_n0 = Taylor polynomial of S_K = sum_{k<=K} b_k at the exact point tc, computed with acb_series
#     (log b_k = k(log2 + i pi + Log(1-q)) + k^2(2 pi i a/N - t) - sum_{j<=2k} Log(1-q^j); Re(1-q^j)>0, principal Log);
#   * |E_trunc| <= M (rho/R)^{n0+1}/(1-rho/R) by Cauchy with R = 8 rho, M = sum_{k<=K} sup_{|h|<=R} |b_k| (ball bound, no cancellation needed);
#   * |E_tail| <= sup|b_K| rho_K/(1-rho_K), rho_K = |c_t|_sup Q^{2K+1}/((1-Q^{2K+1})(1-Q^{2K+2})) < 1/2, Q = sup|q| on |h|<=R
#     (the ratio |b_{k+1}/b_k| <= rho_k and rho_k decreases in k).
# Winding: circle |t-t0| = R0 cut into M arcs; arc i lies in the disc of radius rho = 2 R0 sin(pi/(2M)) about its midpoint.
#   Each image enclosure D_i must satisfy 0 notin D_i and rad(D_i) < 0.5|mid(D_i)|; then two consecutive images (which
#   meet) lie in a sector of opening < pi and the principal differences of the midpoint arguments add up to 2 pi * winding.
# Any failed condition prints FAIL and exits with status 1.
# usage: python3 P2_cert.py circle a N t0re t0im R0 M [n0] [prec]
import sys, math
from flint import acb, arb, acb_series, ctx

def sup_abs(z):  # upper bound for |z|
    v = abs(z); return v.mid() + v.rad()

def piece(a, N, tc, rho, n0):
    R = 8*rho
    ctx.cap = n0+1
    tpi = acb.pi()*2
    one = acb(1)
    tcA = acb(tc.real, tc.imag)                       # exact binary point
    h = acb_series([0, 1])
    Lz = acb(0, 1)*tpi*a/N
    Lq_c = Lz - tcA
    q_c = Lq_c.exp()
    ser_Lq = acb_series([Lq_c, -1])                   # Log q(tc+h) = Lz - tc - h
    ser_q = acb_series([q_c])*(-h).exp()
    ser_Lct = acb_series([acb(2).log() + acb(0, 1)*acb.pi()]) + (acb_series([one]) - ser_q).log()
    # disc ball for majorants
    Tdisc = acb(arb(tc.real, R), arb(tc.imag, R))
    Lq_d = Lz - Tdisc; q_d = Lq_d.exp()
    Lct_d = acb(2).log() + acb(0, 1)*acb.pi() + (one - q_d).log()
    Q = sup_abs(q_d); ctsup = sup_abs(acb(2)*(one - q_d))
    S = acb_series([one]); cum = acb_series([0]); cum_d = acb(0)
    M = arb(1); k = 0; mxlog = -1e300
    while True:
        k += 1
        for j in (2*k-1, 2*k):
            r = (a*j) % N
            if r == 0:
                c0 = -((-tcA*j).expm1()); e0 = (-tcA*j).exp()
                v = acb_series([c0]) - acb_series([e0])*((-h*j).exp() - 1)
                vd = -((-Tdisc*j).expm1())
            else:
                qj = (acb(0, 1)*tpi*r/N - tcA*j).exp()
                v = acb_series([one]) - acb_series([qj])*(-h*j).exp()
                vd = one - (acb(0, 1)*tpi*r/N - Tdisc*j).exp()
            cum = cum + v.log(); cum_d += vd.log()
        lb = ser_Lct*k + ser_Lq*(k*k) - cum
        S = S + lb.exp()
        lbd = Lct_d*k + Lq_d*(k*k) - cum_d          # ball for log b_k on the disc
        ub = lbd.real.mid() + lbd.real.rad()
        bsup = ub.exp()
        M += bsup
        lr = float(lbd.real.mid()); mxlog = max(mxlog, lr)
        if k > 5 and lr < mxlog - 80:
            Qk = Q**(2*k+1)
            rk = ctsup*Qk/((1-Qk)*(1-Qk*Q))
            if rk < 0.5:
                tail = bsup*rk/(1-rk)
                break
        if k > 3_000_000: raise RuntimeError('no convergence')
    coeffs = S.coeffs()
    # evaluate the Taylor polynomial on the ball |h| <= rho (Horner in ball arithmetic)
    H = acb(arb(0, rho), arb(0, rho))
    P = acb(0)
    for cf in reversed(coeffs): P = P*H + cf
    x = rho/R
    trunc = M*arb(x)**(n0+1)/(1-arb(x))
    err = trunc + tail
    P = P + acb(arb(0, err), arb(0, err))
    return P, k, float(M.mid()), float(err.mid())

def circle(a, N, t0, R0, M_, n0):
    tot = 0.0; prev = None; first = None; worst = 0.0; kmax = 0; errmax = 0.0; Mmax = 0.0
    rho = 2*R0*math.sin(math.pi/(2*M_))*1.0001
    for i in range(M_):
        ph = 2*math.pi*(i+0.5)/M_
        c = t0 + R0*complex(math.cos(ph), math.sin(ph))
        D, k, Mb, err = piece(a, N, c, rho, n0); kmax = max(kmax, k); errmax = max(errmax, err); Mmax = max(Mmax, Mb)
        m = complex(float(D.real.mid()), float(D.imag.mid()))
        r = float(D.real.rad()) + float(D.imag.rad())
        if not (abs(m) > 0 and r < 0.5*abs(m)):
            print('FAIL: piece %d  |mid|=%.3e rad=%.3e' % (i, abs(m), r)); sys.exit(1)
        worst = max(worst, r/abs(m))
        am = math.atan2(m.imag, m.real)
        if prev is None: first = am
        else:
            d = am - prev
            while d > math.pi: d -= 2*math.pi
            while d < -math.pi: d += 2*math.pi
            tot += d
        prev = am
    d = first - prev
    while d > math.pi: d -= 2*math.pi
    while d < -math.pi: d += 2*math.pi
    tot += d
    return tot/(2*math.pi), worst, kmax, errmax, Mmax

def pieces(a, N, t0, R0, M_, n0, i0, i1):
    """checkpointed variant: certify pieces i0..i1-1 and print their midpoint arguments (to be combined by 'combine')."""
    rho = 2*R0*math.sin(math.pi/(2*M_))*1.0001
    for i in range(i0, min(i1, M_)):
        ph = 2*math.pi*(i+0.5)/M_
        c = t0 + R0*complex(math.cos(ph), math.sin(ph))
        D, k, Mb, err = piece(a, N, c, rho, n0)
        m = complex(float(D.real.mid()), float(D.imag.mid())); r = float(D.real.rad()) + float(D.imag.rad())
        ok = abs(m) > 0 and r < 0.5*abs(m)
        print('PIECE %d %s arg=%.17g ratio=%.4f K=%d maj=%.3e err=%.3e' % (i, 'OK' if ok else 'FAIL', math.atan2(m.imag, m.real), r/abs(m) if abs(m) > 0 else 1e9, k, Mb, err), flush=True)
        if not ok: sys.exit(1)

def combine(fname, M_):
    args = {}
    for line in open(fname):
        if line.startswith('PIECE'):
            f = line.split(); i = int(f[1])
            if f[2] != 'OK': print('FAIL: piece %d' % i); sys.exit(1)
            args[i] = float(f[3].split('=')[1])
    if sorted(args) != list(range(M_)): print('FAIL: missing pieces', sorted(set(range(M_))-set(args))); sys.exit(1)
    tot = 0.0
    for i in range(M_):
        d = args[(i+1) % M_] - args[i]
        while d > math.pi: d -= 2*math.pi
        while d < -math.pi: d += 2*math.pi
        tot += d
    return tot/(2*math.pi)

if __name__ == '__main__':
    if sys.argv[1] == 'pieces':
        a, N = int(sys.argv[2]), int(sys.argv[3]); t0 = complex(float(sys.argv[4]), float(sys.argv[5]))
        R0, M_, n0 = float(sys.argv[6]), int(sys.argv[7]), int(sys.argv[8]); ctx.prec = int(sys.argv[9])
        pieces(a, N, t0, R0, M_, n0, int(sys.argv[10]), int(sys.argv[11]))
    if sys.argv[1] == 'combine':
        w = combine(sys.argv[2], int(sys.argv[3]))
        if abs(w - round(w)) > 1e-9: print('FAIL: non-integer winding %r' % w); sys.exit(1)
        print('CERTIFIED (checkpointed, %s): winding number of B = %d' % (sys.argv[2], round(w)))
    if sys.argv[1] == 'circle':
        a, N = int(sys.argv[2]), int(sys.argv[3]); t0 = complex(float(sys.argv[4]), float(sys.argv[5]))
        R0, M_ = float(sys.argv[6]), int(sys.argv[7])
        n0 = int(sys.argv[8]) if len(sys.argv) > 8 else 30
        ctx.prec = int(sys.argv[9]) if len(sys.argv) > 9 else 300
        w, worst, kmax, errmax, Mmax = circle(a, N, t0, R0, M_, n0)
        if abs(w - round(w)) > 1e-9: print('FAIL: non-integer winding %r' % w); sys.exit(1)
        print('CERTIFIED %d/%d: |t-(%.12e%+.12ej)| = %.3e, M=%d pieces, n0=%d, prec=%d: winding number of B = %d '
              '(max rad/|mid| %.3f, max K %d, max majorant %.2e, max err %.2e)' % (a, N, t0.real, t0.imag, R0, M_, n0, ctx.prec, round(w), worst, kmax, Mmax, errmax))
