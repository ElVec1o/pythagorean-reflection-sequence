# P2_fitV.py -- VERIFIED numerics: fit B(zeta e^{-t}) ~ A e^{V/t} from |B| on two radii at theta=+-th0,
# and compare with the saddle values V_m = L_m^2/4 + E_w (P1f Lemma saddle) for both roots w.
# usage: python3 P2_fitV.py a N r1 r2 th0
import sys, subprocess, cmath, math
from mpmath import mp, mpf, exp, pi, log, sqrt, polylog, nstr, mpc
BIN = 'p2scan/target/release/p2scan'
def lgB(a, N, t):
    o = subprocess.run([BIN, 'meval', str(a), str(N), repr(t.real), repr(t.imag)], capture_output=True, text=True, timeout=280).stdout
    d = dict(x.split('=') for x in o.split())
    return float(d['log|B|']), float(d['argB']), float(d['lost_bits'])
a, N = int(sys.argv[1]), int(sys.argv[2]); r1, r2, th0 = map(float, sys.argv[3:6])
res = {}
for th in (th0, -th0, 0.0):
    l1 = lgB(a, N, r1*cmath.exp(1j*th)); l2 = lgB(a, N, r2*cmath.exp(1j*th))
    res[th] = ((l1[0]-l2[0])/(1/r1-1/r2), l1, l2)   # = Re(V e^{-i th})
    print('th=%+.3f  Re(V e^{-ith}) fit=%.10e   log|B|(r1)=%.6f log|B|(r2)=%.6f lostbits=%.0f' % (th, res[th][0], l1[0], l2[0], l2[2]))
hp, hm = res[th0][0], res[-th0][0]
# Re(V e^{-i th}) = Vr cos th + Vi sin th
Vr = (hp+hm)/(2*math.cos(th0)); Vi = (hp-hm)/(2*math.sin(th0))
print('fitted V = %.10e %+.10e i' % (Vr, Vi))
mp.dps = 30
z = exp(2j*pi*a/N); c = -2*(1-z); L = log(c); cN = c**N
print('ell=%.6f |c|^N=%.6g  c^N=%s' % (float(L.real), float(abs(cN)), nstr(cN, 6)))
best = []
for w in (1+cN/2+sqrt(cN+cN**2/4), 1+cN/2-sqrt(cN+cN**2/4)):
    xi = log(1-w)/N; Ew = pi**2/(6*N**2)-xi**2-polylog(2, w)/N**2
    for m in range(-3*N, 3*N):
        V = (L+2j*pi*m/N)**2/4+Ew; x = (L+2j*pi*m/N)/2-xi
        best.append((abs(complex(V)-complex(Vr, Vi)), m, w, V, x))
best.sort(key=lambda v: v[0])
for d, m, w, V, x in best[:3]:
    print('  closest saddle: m=%d |w|=%s w=%s V=%s x_m=%s dist=%.2e' % (m, nstr(abs(w), 8), nstr(w, 6), nstr(V, 10), nstr(x, 6), d))
