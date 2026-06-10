# Symbolic model of the side-reflection group of the (a,b) right triangle,
# coordinates scaled by 1/a. Every element is (eps, delta, k, P) acting as
#   w  |->  eps * zeta^k * (w if delta==0 else conj(w)) + P(zeta)
# with P an integer Laurent polynomial in t (t = zeta), zeta=(a+bi)/(a-bi).
# Generators:
#   Rx (leg on x-axis):  w -> conj(w)            = (+1, 1, 0, 0)
#   Ry (leg on y-axis):  w -> -conj(w)           = (-1, 1, 0, 0)
#   Rh (hypotenuse):     w -> z^-1 conj(w) + 1 - t^-1   = (+1, 1, -1, {0:1,-1:-1})
# Composition g o h (apply h first):
#   delta_g=0: (eg*eh, dh, kg+kh, eg*t^kg*Ph + Pg)
#   delta_g=1: (eg*eh, 1-dh, kg-kh, eg*t^kg*Ph(t^-1) + Pg)
import sys
from collections import defaultdict

def pmul_tk(P, k, s):   # s * t^k * P
    return {e+k: s*c for e,c in P.items()}
def pinv(P):            # P(t^-1)
    return {-e: c for e,c in P.items()}
def padd(P, Q):
    R = dict(P)
    for e,c in Q.items():
        R[e] = R.get(e,0)+c
        if R[e]==0: del R[e]
    return R
def freeze(P): return tuple(sorted(P.items()))

GENS = [ (1,1,0,{}), (-1,1,0,{}), (1,1,-1,{0:1,-1:-1}) ]

def compose(g,h):
    eg,dg,kg,Pg = g; eh,dh,kh,Ph = h
    if dg==0:
        return (eg*eh, dh, kg+kh, padd(pmul_tk(Ph,kg,eg), Pg))
    else:
        return (eg*eh, 1-dh, kg-kh, padd(pmul_tk(pinv(Ph),kg,eg), Pg))

def key(el): return (el[0],el[1],el[2],freeze(el[3]))

def bfs(maxd):
    ident=(1,0,0,{})
    seen={key(ident):ident}
    frontier=[ident]; layers=[[ident]]
    for d in range(maxd):
        nxt=[]
        for el in frontier:
            for g in GENS:
                ne=compose(g,el)
                k=key(ne)
                if k not in seen:
                    seen[k]=ne; nxt.append(ne)
        layers.append(nxt); frontier=nxt
    return layers

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 16
layers=bfs(maxd)
counts=[len(L) for L in layers]
print("layer counts :", counts)
print("expected     : 1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683 ...")

# Height growth of translation parts
print("\nd  maxcoef  maxdeg_span")
for d,L in enumerate(layers):
    h=0; span=0
    for el in L:
        for e,c in el[3].items():
            h=max(h,abs(c))
        if el[3]:
            es=[e for e in el[3]]
            span=max(span,max(es)-min(es))
    print(f"{d:2d}  {h:6d}  {span:4d}")
