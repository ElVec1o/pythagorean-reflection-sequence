# P2_zeros.py -- VERIFIED numerics (MPFR via p2scan meval): two-exponential model at zeta=e(a/N), N odd, ell<0.
#   B(zeta e^{-t}) ~ A1 e^{V/t} + A2 e^{-V/t},  V = V_* (small saddle, P1f Lemma saddle with the root w of (1-w)^2=c^N w).
# Estimates A1, A2 from B off the tie ray, predicts zeros 1/t_j = (log(-A2/A1) + 2 pi i j)/(2V), refines them by secant.
# usage: python3 P2_zeros.py a N r_probe j1 j2 ...
import sys, subprocess, cmath, math
from mpmath import mp, exp, pi, log, sqrt, polylog
BIN = 'p2scan/target/release/p2scan'
def logB(a, N, t):
    o = subprocess.run([BIN, 'meval', str(a), str(N), repr(t.real), repr(t.imag)], capture_output=True, text=True, timeout=280).stdout
    d = dict(x.split('=') for x in o.split()); return complex(float(d['log|B|']), float(d['argB']))
def Vstar(a, N):
    mp.dps = 30; z = exp(2j*pi*a/N); c = -2*(1-z); L = log(c); cN = c**N
    best = None
    for w in (1+cN/2+sqrt(cN+cN**2/4), 1+cN/2-sqrt(cN+cN**2/4)):
        xi = log(1-w)/N; Ew = pi**2/(6*N**2)-xi**2-polylog(2, w)/N**2
        for m in range(-3*N, 3*N):
            x = (L+2j*pi*m/N)/2-xi; V = (L+2j*pi*m/N)**2/4+Ew
            if best is None or abs(x) < abs(best[0]): best = (complex(x), complex(V), complex(w), m)
    return best
a, N = int(sys.argv[1]), int(sys.argv[2]); rp = float(sys.argv[3]); js = [int(v) for v in sys.argv[4:]]
x, V, w, m = Vstar(a, N)
if rp < 0: rp = -rp*abs(V)
if V.real < 0: V = -V
ths = math.atan2(V.imag, V.real)  # tie ray: Re(V e^{-i th}) = 0  -> th = arg V +- pi/2
tie = [th for th in (ths+math.pi/2, ths-math.pi/2) if abs(th) < math.pi/2][0]
print('a/N=%d/%d  V*=%.10e%+.10ei  |V|*N^2/|c|^{N/2}=%.6f  x*=%s  w=%s  tie ray theta*=%.6f rad' % (a, N, V.real, V.imag, abs(V)*N*N/abs(complex(-2*(1-cmath.exp(2j*math.pi*a/N))))**(N/2), x, w, tie))
# A1: dominant e^{V/t} side (Re(V e^{-i th})>0), A2: the other side
def amp(th, sgn):
    t = rp*cmath.exp(1j*th); lb = logB(a, N, t); return lb - sgn*V/t
dA = 0.35
side1 = tie - dA if (V*cmath.exp(-1j*(tie-dA))).real > 0 else tie + dA
side2 = 2*tie - side1
lA1 = amp(side1, 1); lA2 = amp(side2, -1)
lA1b = amp(side1, 1) if False else logB(a, N, rp/2*cmath.exp(1j*side1)) - V/(rp/2*cmath.exp(1j*side1))
print('log A1 = %s (r) %s (r/2);  log A2 = %s' % (lA1, lA1b, lA2))
print('|A1|=%.6f |A2|=%.6f' % (math.exp(lA1.real), math.exp(lA2.real)))
# zeros: 2V/t = log(-A2/A1) + 2 pi i j  (mod the 2pi ambiguity of the measured args)
base = lA2 - lA1 + 1j*math.pi
for j in js:
    # choose integer j so that t lies near radius ~ given
    u = (base + 2j*math.pi*j)/(2*V); t0 = 1/u
    if t0.real < 0: print('j=%d: t0 in left half' % j); continue
    f = lambda t: cmath.exp(logB(a, N, t) - V/t)   # = A1 + A2 e^{-2V/t} + ...
    t1 = t0*(1+1e-6); f0, f1 = f(t0), f(t1)
    for it in range(40):
        t2 = t1 - f1*(t1-t0)/(f1-f0); t0, f0 = t1, f1; t1 = t2; f1 = f(t1)
        if abs(t1-t0) < 1e-13*abs(t1): break
    print('j=%d  predicted t=%.10e%+.10ei |t|=%.3e arg=%.5f   zero t*=%.10e%+.10ei  |f(t*)|=%.1e  rel.dev=%.2e' % (j, (1/u).real, (1/u).imag, abs(1/u), cmath.phase(1/u), t1.real, t1.imag, abs(f1), abs(t1-1/u)/abs(t1)))
