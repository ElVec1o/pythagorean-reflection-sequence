# P1f_landscape_check.py -- VERIFIED (floating, sampled; NOT a certificate): sanity check of the analytic landscape
# inequalities of P1f_lemma.tex (Lemma LS) with the exact exponent  W_mu(x) = Re((Phi(x) + 2 pi i mu x/N) e^{-i theta}),
# Phi(x) = x L - x^2 - Li2(e^{-2Nx})/N^2 + pi^2/(6N^2), on the central tie ray theta*.
# Explicit modes: every surviving mu with |mu| <= 2N+1 (N odd) resp. |mu| <= 4N+1 (N even; mu = 2 nu, Section dec),
# on the paths [x_A, x_mu] U x_mu + e^{i theta/2}[0,3]; remainder rays gamma_-+ (directions theta -+ pi/8) with the
# remainder modes mu_-+ = nu_-+ N/N' of Section dec.
# Two checks per a/N:
#   B  : mode set M, dominant pair {n, n+s}, reference height T                       (Lemma LS, Theorem asym)
#   S+-: N even only: mode set M+1, single dominant mode n+1, reference height T' = T + pi^2 cos(theta*)/N^2
#        (Lemma LS', Theorem C(i)); the amplitude factor e^{-+x} is O(1) and not part of the exponent.
# Reports max over non-dominant pieces of W - Tref (must be < 0), dominant max of (W-Tref)/sigma^2 (must be < 0),
# remainder max of W - Tref (must be < 0), and head bound H_head of Lemma head (must be < T).
# Floating double precision (numpy/scipy); Li2(z) = spence(1-z). Memory guard: aborts if peak RSS > 3000 MB.
import sys, resource
from math import gcd
import numpy as np
from scipy.special import spence

CAP_MB = 3000
def guard():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20  # bytes on darwin
    if rss > CAP_MB:
        print('MEMORY GUARD: peak RSS %.0f MB > %d MB, abort' % (rss, CAP_MB), flush=True); sys.exit(2)

def Li2(z): return spence(1 - z)

def run(a, N, samples=120):
    z = np.exp(2j*np.pi*a/N); c = -2*(1-z); L = np.log(c); ell = L.real; phi = L.imag
    X = c**N; Bq = 2+X; w = 2/(Bq*(1+np.sqrt(1-4/(Bq*Bq)))); xi = np.log(1-w)/N
    even = (N % 2 == 0)
    s = 2 if even else 1
    if not even: surv = lambda m: True
    elif N % 4 == 0: surv = lambda m: m % 2 == 0
    else: surv = lambda m: m % 2 == 1
    Mmax = 4*N+1 if even else 2*N+1
    n = min((m for m in range(-Mmax, Mmax+1) if surv(m)), key=lambda m: abs(phi + 2*np.pi*(m + s/2)/N))
    th = np.arctan((phi + 2*np.pi*(n + s/2)/N)/ell); E = np.exp(-1j*th)
    def W(x, mu):
        Om = x*L - x*x - Li2(np.exp(-2*N*x))/N**2 + np.pi**2/(6*N*N) + 2j*np.pi*mu*x/N
        return (Om*E).real
    xm = lambda mu: (L + 2j*np.pi*mu/N)/2 - xi
    T = W(xm(n), n)
    # remainder modes (Section dec): N odd nu_-=-2N, nu_+=2N+1, mu=nu; N even mu=2 nu with
    # eps=+1: nu_-=-2N, nu_+=2N+1;  eps=-1: nu_-=-2N-1/2, nu_+=2N+1/2.
    def rem_modes(eps):
        if not even: return (-2*N, 2*N+1)
        return (-4*N, 4*N+2) if eps == 1 else (-4*N-1, 4*N+1)
    eps_B = -1 if N % 4 == 2 else 1
    cases = [('B', surv, (n, n+s), T, rem_modes(eps_B))]
    if even:
        survS = lambda m: not surv(m)               # mu -+ a in M  <=>  mu in M+1 (a odd)
        Tp = W(xm(n+1), n+1)
        cases.append(('S', survS, (n+1,), Tp, rem_modes(-eps_B)))   # eps flips for S_+-
    delta = 1.0/(8*N)
    sg = np.arange(samples+1)/samples
    vv = 3*np.arange(1, samples+1)/samples
    rr = 4*np.arange(samples+1)/samples
    out = []
    for name, sv, dom_set, Tref, (mlo, mhi) in cases:
        worst_nd = worst_dom = worst_rem = -1e9
        for xA_abs in (delta/2, delta, 2*delta):
            xA = xA_abs*np.exp(1j*th)
            for mu in range(-Mmax, Mmax+1):
                if not sv(mu): continue
                X0 = xm(mu)
                vseg = W(X0 - sg*(X0 - xA), mu) - Tref
                vray = W(X0 + vv*np.exp(1j*th/2), mu) - Tref
                if mu in dom_set:
                    worst_dom = max(worst_dom, np.max(vseg[1:]/sg[1:]**2), np.max(vray/vv**2))
                else:
                    worst_nd = max(worst_nd, vseg.max(), vray.max())
            for sgn, mu in ((-1, mlo), (1, mhi)):
                assert sv(mu), (name, N, mu)
                worst_rem = max(worst_rem, np.max(W(xA + rr*np.exp(1j*(th + sgn*np.pi/8)), mu) - Tref))
        out.append((name, float(Tref), float(worst_nd), float(worst_dom), float(worst_rem)))
        guard()
    head = delta*(ell + 0.0837) + (2*delta/N)*(1 + np.log(1/(1.8*delta)))
    return float(th*180/np.pi), float(T), out, float(head)

if __name__ == '__main__':
    Ns = [int(v) for v in sys.argv[1:]]
    if len(Ns) == 2 and Ns[0] < 0: Ns = list(range(-Ns[0], Ns[1]+1))   # "-16 40" = range 16..40
    nviol = ncase = 0
    for N in Ns:
        for a in range(1, N):
            if gcd(a, N) != 1 or not (N <= 5*a <= 4*N): continue
            th, T, out, hd = run(a, N)
            line = '%d/%d th*=%.2f head=%.4f' % (a, N, th, hd)
            ok = hd < T
            for name, Tr, nd, dom, rem in out:
                good = nd < 0 and dom < 0 and rem < 0
                ok = ok and good
                line += ' | %s Tref=%.4f nondom=%.5f dom/sig^2=%.4f rem=%.4f' % (name, Tr, nd, dom, rem)
            line += '  ' + ('OK' if ok else 'VIOLATION')
            ncase += 1; nviol += (not ok)
            print(line, flush=True)
    print('SUMMARY: %d cases, %d violations' % (ncase, nviol), flush=True)
    sys.exit(1 if nviol else 0)
