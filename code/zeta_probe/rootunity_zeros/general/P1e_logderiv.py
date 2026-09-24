# P1e_logderiv.py -- Level-q quantities that the induction needs, computed in Arb (python-flint) via the EXACT finite formula
# (Lemma Zk of P1e_lemma.tex)     Z_q(p/q) = sum_{k mod q} gamma_k exp(Phi_q(zeta0^k)),
#   f(t) = sum_k gamma_k exp(Phi_q(zeta0^k e(-t))) ,  f(0) = Z_q .
# Phi_q is truncated at n <= M; the tail is enclosed rigorously (|tail| <= (q/4) sum_{n>M}|u|^n/n), so |Z_q| etc. are
# genuine enclosures (VERIFIED-rigorous at the listed points; used only as data, not as part of a proof).
# Reports |Z_q|, the triangle loss Lam = sum_k |gamma_k||e^{Phi_k}| / |Z_q|, and the moment ratios
#   D1 = |f'(0)|/(2 pi q |f(0)|),   D2 = |f''(0)|/((2 pi q)^2 |f(0)|)     (same normalisation as P1b's D1, D2).
# Modes:  fam j n0 theta q1 q2 ...   (seeds p/q with n0 p - j q = theta: the drift family at j/n0)
#         scan QMIN QMAX [ell_min]
import sys
from math import gcd, log, sin, pi
from flint import arb, acb, ctx
ctx.prec = 200
PI = arb.pi(); I = acb(0, 1)
def e(y): return (2*PI*I*y).exp()
def data(p, q, M=None):
    for pr in (200, 400, 800, 1600, 3200):
        ctx.prec = pr
        r = data1(p, q, M)
        if bool(r[0] > 0) and r[0].rad() < 1e-6*r[0].mid() and r[2].is_finite(): return r
    return r
def data1(p, q, M=None):
    z0 = e(arb(p)/q); c0 = -2*(1 - z0)
    l = float(arb(c0.abs_lower()).log().mid())
    lX = q*arb(c0.abs_lower()).log()
    if bool(lX < 600):
        X = c0**q; B = 2 + X; w = 2/(B*(1 + (1 - 4/(B*B)).sqrt()))
        u = ((1 - w).log()*2/q).exp()/c0
    else:
        u = 1/c0     # |w| <= 2 e^{-600}: lambda^2 = 1 + O(e^{-600}); enclosed below by widening
        eps = arb(2)*(-lX).exp()*3/q
        u = u*(1 + acb(arb(0, eps.upper()), arb(0, eps.upper())))
    ua = arb(u.abs_upper())
    if M is None: M = int(45/(-float(ua.log().mid()))) + 5
    ET = [e(arb(j)/q) for j in range(q)]
    if q % 2 == 1:
        g0 = sum((e(arb((-p*v*v) % q)/q) for v in range(q)), acb(0))/q
        inv4 = pow(4, -1, q); gam = [g0*ET[(p*inv4*k*k) % q] for k in range(q)]
    else:
        gam = [sum((e(arb((-p*(v*v + k*v)) % q)/q) for v in range(q)), acb(0))/q for k in range(q)]
    ET = [e(arb(j)/q) for j in range(q)]
    Ph = [acb(0)]*q; P1 = [acb(0)]*q; P2 = [acb(0)]*q
    un = acb(1)
    for n in range(1, M+1):
        un = un*u
        if n % q == 0: continue
        cn = un/(n*(1 - ET[(-n*p) % q]))
        np_ = (n*p) % q
        for k in range(q):
            t = cn*ET[(k*np_) % q]     # table lookup: no repeated rotation (avoids the rectangular wrapping effect)
            Ph[k] = Ph[k] + t; P1[k] = P1[k] + t*n; P2[k] = P2[k] + t*n*n
    tail = arb(q)/4*ua**(M+1)/((M+1)*(1 - ua))
    rt = acb(arb(0, tail.upper()), arb(0, tail.upper()))
    b = [(ph + rt).exp() for ph in Ph]
    f0 = sum((g*x for g, x in zip(gam, b)), acb(0))
    f1 = sum((g*x*a1 for g, x, a1 in zip(gam, b, P1)), acb(0))
    f2 = sum((g*x*(a1*a1 - a2) for g, x, a1, a2 in zip(gam, b, P1, P2)), acb(0))
    env = sum((arb(g.abs_upper())*arb(x.abs_upper()) for g, x in zip(gam, b)), arb(0))
    F = arb(f0.abs_lower())
    return F, env/F, arb(f1.abs_upper())/(q*F), arb(f2.abs_upper())/(q*q*F), l
def s(x): return x.str(4, radius=False)
if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'fam':
        j, n0, th = int(a[1]), int(a[2]), int(a[3])
        for qs in a[4:]:
            q = int(float(qs))
            while (j*q + th) % n0 or gcd((j*q + th)//n0, q) != 1: q += 1
            p = (j*q + th)//n0
            Z, Lam, D1, D2, l = data(p, q)
            print('%d/%d (theta=%+d at %d/%d): |Z_q|>=%s  Lam<=%s  D1<=%s  D2<=%s' % (p, q, th, j, n0, s(Z), s(Lam), s(D1), s(D2)), flush=True)
    else:
        Q0, QM = int(a[1]), int(a[2]); lmin = float(a[3]) if len(a) > 3 else 0.02
        mx = [arb(0)]*3; arg = [None]*3; mnZ = None
        for q in range(Q0, QM+1):
            for p in range(1, q):
                if gcd(p, q) != 1 or log(4*sin(pi*p/q)) < lmin: continue
                try: Z, Lam, D1, D2, l = data(p, q)
                except Exception: print('skip (degenerate w)', p, q); continue
                if not Z.is_finite() or not bool(Z > 0): print('skip', p, q); continue
                for i, v in enumerate((D1, D2, Lam)):
                    if bool(v > mx[i]): mx[i] = v; arg[i] = (p, q)
                mnZ = Z if mnZ is None else mnZ.min(Z)
            print('q<=%d  maxD1<=%s %s  maxD2<=%s %s  maxLam<=%s %s  min|Z|>=%s' % (q, s(mx[0]), arg[0], s(mx[1]), arg[1], s(mx[2]), arg[2], s(mnZ)), flush=True)
