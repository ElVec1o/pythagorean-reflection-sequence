# P2_landscape.py -- saddle landscape at zeta=e(a/N) when ell<=0 (VERIFIED numerics of PROVED algebra, mpmath 40 digits).
# For each root w of (1-w)^2 = c^N w and each mode m, x_m = L_m/2 - Log(1-w)/N, V_m = L_m^2/4 + E_w (P1f Lemma saddle).
# Prints: the small saddle x_* (min |x|), its partner (-x_*, the other root, mode m' = m +- 1), |V_*+V'|,
#         V_* versus the leading term s/N^2 (s = c^{N/2}), which member of the pair has G*(m) != 0 (parity rule),
#         and the tie ray arg t = arg V_* +- pi/2 when both members are admissible.
# usage: python3 P2_landscape.py a N [a N ...]
import sys
from mpmath import mp, exp, pi, log, sqrt, polylog, nstr, fabs, atan2, mpf
mp.dps = 40
def admissible(m, N):
    if N % 2: return True
    return (m % 2 == 0) if N % 4 == 0 else (m % 2 == 1)
def run(a, N):
    z = exp(2j*pi*a/N); c = -2*(1-z); L = log(c); cN = c**N; ell = L.real
    S = []
    for w in (1+cN/2+sqrt(cN+cN**2/4), 1+cN/2-sqrt(cN+cN**2/4)):
        xi = log(1-w)/N; Ew = pi**2/(6*N**2)-xi**2-polylog(2, w)/N**2
        for m in range(-3*N, 3*N):
            Lm = L+2j*pi*m/N; S.append((abs((Lm/2-xi)), m, w, Lm/2-xi, Lm**2/4+Ew))
    S.sort(key=lambda v: v[0])
    _, m1, w1, x1, V1 = S[0]
    part = min((v for v in S if abs(v[2]-w1) > 1e-20), key=lambda v: abs(v[3]+x1))
    _, m2, w2, x2, V2 = part
    s = sqrt(cN) if N % 2 else c**(N//2)
    lead = min((s/N**2, -s/N**2), key=lambda v: abs(v-V1))
    reg = ('|w|=1 (c^N in [-4,0))' if abs(abs(w1)-1) < mpf(10)**-30 else ('w real' if abs(w1.imag) < mpf(10)**-30 else 'w generic'))
    print('%d/%d  ell=%+.5f  N ell=%+.3f  |c|^N=%.3e  %s' % (a, N, float(ell), float(N*ell), float(abs(cN)), reg))
    print('   small saddle m=%d  x*=%s  V*=%s   partner m=%d  |x*+x_p|=%.1e  |V*+V_p|=%.1e' % (m1, nstr(x1, 6), nstr(V1, 10), m2, float(abs(x1+x2)), float(abs(V1+V2))))
    print('   V*/(+-c^{N/2}/N^2) - 1 = %s   (delta=|c|^{N/2}=%.3e)' % (nstr(V1/lead-1, 4), float(abs(cN)**0.5)))
    ad1, ad2 = admissible(m1, N), admissible(m2, N)
    print('   G* != 0 : small saddle %s, partner %s' % (ad1, ad2))
    if ad1 and ad2:
        th = float(atan2(V1.imag, V1.real)); tie = [x for x in (th+float(pi)/2, th-float(pi)/2) if abs(x) < float(pi)/2]
        print('   BOTH admissible -> two exponentials +-V*, tie ray arg t = %s rad (%s deg)' % (nstr(tie[0], 6), nstr(tie[0]*180/float(pi), 5)))
    else:
        live = (V1 if ad1 else V2)
        print('   ONE admissible -> single exponential e^{V/t}, V=%s' % nstr(live, 10))
args = sys.argv[1:]
for i in range(0, len(args), 2): run(int(args[i]), int(args[i+1]))
