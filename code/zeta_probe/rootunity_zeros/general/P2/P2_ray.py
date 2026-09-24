# P2_ray.py -- VERIFIED numerics: log|B(zeta e^{-t})| - Re(V*/t) along theta at fixed r, to detect a second exponential.
# usage: python3 P2_ray.py a N r Vre Vim th_start th_end nsteps
import sys, subprocess, cmath, math
BIN = 'p2scan/target/release/p2scan'
a, N = sys.argv[1], sys.argv[2]; r, Vr, Vi, t0, t1 = map(float, sys.argv[3:8]); n = int(sys.argv[8])
V = complex(Vr, Vi)
for i in range(n+1):
    th = t0+(t1-t0)*i/n; t = r*cmath.exp(1j*th)
    o = subprocess.run([BIN, 'meval', a, N, repr(t.real), repr(t.imag)], capture_output=True, text=True, timeout=280).stdout
    d = dict(x.split('=') for x in o.split())
    lg = float(d['log|B|']); print('th=%.4f log|B|=%.6f  Re(V/t)=%.6f  resid=%.6f argB=%s lostbits=%s k=%s' % (th, lg, (V/t).real, lg-(V/t).real, d['argB'], d['lost_bits'], d['k']), flush=True)
