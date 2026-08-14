#!/usr/bin/env python3
"""
SEAM #3 -- THE decisive computation: does the cycle-corrected bulk block have its OWN
denominator with a NEW pole family, or does y enter only the numerator (so the bulk poles
are the SAME y-free 1-S_1 family)?

We compare two denominators built from the deposit transfer (catalytic state = current
deposit half-size s>=1):

(A) RELAXED catalytic recursion (validated; reproduces 0,2,2,6,2,18,...):
       F_s = 2q^s + 2q^s sum_{s'>=s}F q^{s'} + 2q^{2s} sum_{s'<s}F.
    Telescoped denominator: 1 - S_1(q),  S_k=sum_j alpha_{k+2j} prod gamma_{k+2i}.
    Zeros (bulk poles): 0.6096, 0.9202, 0.9690,... -> 1 (cosine family).

(B) GAP-BRIDGE transfer with explicit cycle marker y:  deposits couple via
       K(a,b;y) = q^{max(a,b)} + q^{a+b} * Phi(q,y),  Phi = q y/(1-q y).
    Build M(q,y)[b,a] = edgefac(b) * K(a,b;y); block = sum (I-M)^{-1} E.
    Denominator = det(I - M(q,y)).

QUESTION 1: do the zeros of det(I-M(q,y)) MOVE with y?  If they do NOT (the y-dependence
factors out of the determinant's vanishing locus), then the corrected bulk denominator is
y-FREE: the cycle correction does NOT create a new pole family -- the bulk poles are shared.

QUESTION 2: at y=1 do det(I-M) zeros coincide with the 1-S_1 bulk poles?  (kernel validity)

We compute det(I-M(q,y)) zeros for y=1, y=q (true), and a few y values, and tabulate.
"""
import mpmath as mp
mp.mp.dps=40

# ---- relaxed bulk denominator 1 - S_1 (telescoped) ----
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-50) and j>40: break
    return tot

# ---- gap-bridge transfer denominator det(I-M(q,y)) ----
def detIM(q,y,Smax=70,edgefac=None):
    if edgefac is None: edgefac=lambda b: 2*q**b
    g=(q*y)/(1-q*y)
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    M=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            K=q**max(a,b)+q**(a+b)*g
            M[idx[b],idx[a]]=edgefac(b)*K
    return mp.det(mp.eye(n)-M)

def find_zeros(f, nmax, wlo=2.0, whi=200, step=0.04):
    """find zeros of f(q) in (0,1) via the w=sqrt(2/tau) cosine-aligned scan."""
    roots=[]; prev=None; pq=None; w=mp.mpf(wlo)
    while len(roots)<nmax and w<whi:
        q=mp.e**(-2/w**2); val=f(q)
        if prev is not None and mp.sign(val)!=mp.sign(prev) and prev!=0:
            try:
                r=mp.findroot(f,(pq+q)/2)
                if 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-15)):
                    roots.append(r)
            except Exception: pass
        prev=val; pq=q; w+=step
    return sorted(roots)

if __name__=="__main__":
    print("=== (A) relaxed bulk poles: zeros of 1-S_1(q) ===")
    polesA=find_zeros(lambda q: S(1,q)-1, 6)
    print("  ", [mp.nstr(r,10) for r in polesA])
    print()
    print("=== (B) gap-bridge det(I-M(q,y)) zeros, for several y ===")
    for ylabel, yf in [("y=1 (relaxed)", lambda q: mp.mpf(1)),
                       ("y=q  (TRUE)",   lambda q: q),
                       ("y=q^2",         lambda q: q**2),
                       ("y=0.3 const",   lambda q: mp.mpf('0.3'))]:
        zr=find_zeros(lambda q: detIM(q, yf(q)), 6)
        print(f"  {ylabel:16}: {[mp.nstr(r,10) for r in zr]}")
    print()
    print("If the det(I-M) zeros are the SAME for all y => bulk denominator is y-FREE")
    print("=> cycle correction does NOT create a new pole family (numerator-only effect).")
