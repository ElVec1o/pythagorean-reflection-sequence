import mpmath as mp
from c1_complex import B
mp.mp.dps = 30
roots = []
import itertools
for r in [0.6,0.68,0.75,0.8,0.84,0.87,0.9,0.92,0.94]:
    for j in range(72):
        q0 = mp.mpf(r)*mp.expjpi(mp.mpf(j)/36)
        try:
            q = mp.findroot(B, q0, tol=1e-22, maxsteps=40)
        except Exception:
            continue
        if abs(q) < 0.945 and mp.im(q) >= 0 and all(abs(q-x) > 1e-10 for x in roots):
            roots.append(q)
roots.sort(key=lambda q: abs(q))
print(len(roots), "zeros with Im>=0, |q|<0.945")
for q in roots:
    ang = mp.arg(q)/(2*mp.pi)
    print(f" q={mp.nstr(q,10)} |q|={mp.nstr(abs(q),6)} arg/2pi={mp.nstr(ang,6)}")
