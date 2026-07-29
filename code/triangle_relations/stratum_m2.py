# m=2 stratum (right angle at the apex): exact rational BFS vs the Coxeter
# reference W_2, two leg samples, depth 12. Closes the audited gap: the
# (d*, delta) = (10, 8) row now has an in-folder certificate.
from fractions import Fraction as Fr
import sympy as sp
t = sp.symbols('t')
def abstract(m, N):
    Dm = (1+t)*sum(t**i for i in range(m)); inv = 1 - 3/(1+t) + 1/Dm
    W = sp.cancel(1/(inv.subs(t, 1/t))); ser = sp.series(W, t, 0, N+1).removeO()
    return [int(sp.expand(ser).coeff(t, k)) for k in range(N+1)]
def probe(a, b, dmax=12):
    O, I = Fr(0), Fr(1)
    def refl(p0, d):
        L = d[0]*d[0] + d[1]*d[1]
        m11 = (d[0]*d[0] - d[1]*d[1])/L; m12 = 2*d[0]*d[1]/L
        return (m11, m12, m12, -m11,
                p0[0] - (m11*p0[0] + m12*p0[1]), p0[1] - (m12*p0[0] - m11*p0[1]))
    V0 = (Fr(a), O); V1 = (O, Fr(b))          # legs on the axes: apex angle pi/2
    gens = [(I, O, O, -I, O, O),              # x-axis mirror
            (-I, O, O, I, O, O),              # y-axis mirror
            refl(V0, (V1[0]-V0[0], V1[1]-V0[1]))]
    idm = (I, O, O, I, O, O)
    seen = {idm}; front = [idm]; seq = [1]
    for d in range(1, dmax+1):
        new = []
        for M in front:
            for g in gens:
                N = (g[0]*M[0]+g[1]*M[2], g[0]*M[1]+g[1]*M[3],
                     g[2]*M[0]+g[3]*M[2], g[2]*M[1]+g[3]*M[3],
                     g[0]*M[4]+g[1]*M[5]+g[4], g[2]*M[4]+g[3]*M[5]+g[5])
                if N not in seen: seen.add(N); new.append(N)
        front = new; seq.append(len(new))
    return seq
am = abstract(2, 12)
print("W_2 spheres:", am)
for legs in [(1, 2), (2, 3), (1, 3)]:
    r = probe(*legs)
    dev = next((d for d in range(13) if r[d] != am[d]), None)
    print(f"legs {legs}: first deficit d={dev}, deficits "
          f"{[am[d]-r[d] for d in range(dev, 13)] if dev is not None else 'NONE'}")
