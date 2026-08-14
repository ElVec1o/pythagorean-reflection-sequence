#!/usr/bin/env python3
"""
Is the bulk block G0(q) = S0(q)/(1-S1(q)) a HERGLOTZ/STIELTJES-type function?
Signature (from bulk_pole_signs.py): all residues same sign (negative), 21/21 poles.
Necessary condition for Herglotz on (0,1): between consecutive real poles, G0 is strictly
MONOTONE INCREASING, sweeping -inf (just right of a pole) to +inf (just left of next pole),
i.e. G0'(q) > 0 everywhere finite on (0,1).  Test G0' sign on a dense grid + each inter-pole
interval.  If clean, the conjecture 'G0 is Herglotz' is strongly supported -> (with lem:cos
giving infinitely many zeros of 1-S1) every bulk pole is uncancelled => G0 transcendental.
"""
import mpmath as mp
mp.mp.dps=50

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=3000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>30: break
    return tot
def G0(q): return Sb(0,q)/(1-Sb(1,q))
def dG0(q):
    h=mp.mpf(10)**(-20)
    return (G0(q+h)-G0(q-h))/(2*h)

# locate bulk poles to know interval boundaries
def bisect(f,a,b,it=300):
    fa=f(a); fb=f(b)
    if mp.sign(fa)==mp.sign(fb): return None
    for _ in range(it):
        m=(a+b)/2; fm=f(m)
        if mp.sign(fm)==mp.sign(fa): a,fa=m,fm
        else: b,fb=m,fm
    return (a+b)/2
def bulk_poles(nmax):
    roots=[]; w=mp.mpf(2.0); prev=None; prevq=None; g=lambda qq: Sb(1,qq)-1
    while len(roots)<nmax and w<200:
        q=mp.e**(-2/w**2); val=g(q)
        if prev is not None and mp.sign(val)!=mp.sign(prev):
            r=bisect(g,prevq,q)
            if r and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-14)): roots.append(r)
        prev=val; prevq=q; w+=mp.mpf('0.04')
    return roots

if __name__=="__main__":
    bp=bulk_poles(8)
    print("first bulk poles:", [mp.nstr(r,8) for r in bp])
    print("\n(1) Global monotonicity: sign of G0'(q) on a dense grid avoiding poles")
    bad=0; tested=0
    q=mp.mpf('0.05')
    while q<mp.mpf('0.95'):
        nearpole=any(abs(q-r)<mp.mpf('0.002') for r in bp)
        if not nearpole:
            d=dG0(q); tested+=1
            if d<=0: bad+=1; print(f"   G0'({mp.nstr(q,4)}) = {mp.nstr(d,5)}  <=0  !!")
        q+=mp.mpf('0.01')
    print(f"   tested {tested} points, {bad} with G0'<=0  ->  {'MONOTONE INCREASING (Herglotz-consistent)' if bad==0 else 'NOT monotone'}")

    print("\n(2) Inter-pole sweep: does G0 go -inf -> +inf across each interval (q_b, q_{b+1})?")
    for i in range(len(bp)-1):
        a=bp[i]+mp.mpf('0.0005'); b=bp[i+1]-mp.mpf('0.0005')
        Ga=G0(a); Gb=G0(b)
        print(f"   ({mp.nstr(bp[i],6)},{mp.nstr(bp[i+1],6)}): G0(left+)= {mp.nstr(Ga,6):>12}  G0(right-)= {mp.nstr(Gb,6):>12}  sweep {'-inf->+inf OK' if Ga<0 and Gb>0 else 'NO'}")

    print("\n(3) y-marked bulk block U_bulk also nonneg-coeff => same Herglotz signature expected.")
    print("    (the y=q numerator differs but the denominator 1-S1 is y-free; residue signs")
    print("     are governed by the SAME nonneg-coefficient continuation argument.)")
