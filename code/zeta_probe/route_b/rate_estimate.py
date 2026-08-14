#!/usr/bin/env python3
"""
Oscillation-aware growth-rate estimation for the relaxed sequence v_n.

The ratios r_n = v_{n+1}/v_n converge to r = lim v_{n+1}/v_n with an O(1/n)
correction carrying a PERIOD-4 oscillation (defeats naive Aitken/Shanks/Wynn).
We use estimators built for exactly this asymptotic:

  (1) period-4 block average  g_n = (r_n+r_{n+1}+r_{n+2}+r_{n+3})/4, which kills
      the oscillation, then Richardson extrapolation of g_n in 1/n.
  (2) full least-squares fit r_n = R + sum_k c_k * phi_k(n) over a tail window,
      with phi = {1/n, (-1)^n/n, cos(pi n/2)/n, sin(pi n/2)/n, 1/n^2, ...}.
  (3) repeated Richardson on the deoscillated g_n.

Outputs R with an error bar (spread across windows/orders) and tests r=3/2.
"""
import sys, mpmath as mp
mp.mp.dps=50

def load_seq(path):
    txt=open(path).read()
    import re
    m=re.search(r"v_n\s*=\s*\[([^\]]*)\]",txt)
    if not m: raise SystemExit("no v_n in "+path)
    return [int(x) for x in m.group(1).replace(',',' ').split()]

def ratios(v):
    return [mp.mpf(v[i+1])/mp.mpf(v[i]) for i in range(len(v)-1)]

def block4(r):
    return [(r[i]+r[i+1]+r[i+2]+r[i+3])/4 for i in range(len(r)-3)]

def richardson(seq, xs, order):
    """Iterated Richardson: seq[i] ~ R + a1*xs[i] + a2*xs[i]^2 + ...
    Repeatedly eliminate the leading 1/n term assuming xs ~ 1/n_i geometric-ish.
    We use polynomial (Neville) extrapolation to xs->0 on the last (order+1) pts."""
    n=len(seq)
    pts=list(range(n-(order+1),n))
    X=[xs[i] for i in pts]; Y=[seq[i] for i in pts]
    # Neville extrapolation to x=0
    P=Y[:]
    for k in range(1,len(P)):
        for i in range(len(P)-k):
            P[i]=(P[i]*(0-X[i+k])-P[i+1]*(0-X[i]))/(X[i]-X[i+k])
    return P[0]

def lsq_fit(r, window, basis_funcs):
    """Least squares r_n = sum_j c_j phi_j(n) over the last `window` ratios.
    n index: r[i] uses n=i+1.  Returns the constant-term coefficient (R)."""
    L=len(r); idxs=list(range(L-window,L))
    rows=[]; rhs=[]
    for i in idxs:
        n=mp.mpf(i+1)
        rows.append([f(n) for f in basis_funcs]); rhs.append(r[i])
    A=mp.matrix(rows); b=mp.matrix(rhs)
    AtA=A.T*A; Atb=A.T*b
    x=mp.lu_solve(AtA,Atb)
    return x[0]  # constant term = R

def main(path):
    v=load_seq(path)
    print(f"loaded {len(v)} terms; v_last = {v[-1]}")
    r=ratios(v)
    print("\nlast 12 raw ratios r_n=v_{n+1}/v_n:")
    for i in range(max(0,len(r)-12),len(r)):
        print(f"  n={i+1:3d}: {mp.nstr(r[i],12)}")

    print("\n=== (1) period-4 block average + Neville(1/n) extrapolation ===")
    g=block4(r)
    # x-coordinate for g[i]: centered n = (i+1)+1.5
    xs=[mp.mpf(1)/( (i+1)+mp.mpf('1.5') ) for i in range(len(g))]
    for order in (2,3,4,5):
        if len(g)>order+1:
            R=richardson(g,xs,order)
            print(f"  Neville order {order}: R = {mp.nstr(R,14)}")

    print("\n=== (2) least-squares oscillation-aware fits ===")
    bases={
     '5p: 1,1/n,(-1)^n/n,cos/n,sin/n':[
        lambda n:mp.mpf(1), lambda n:1/n, lambda n:((-1)**int(n))/n,
        lambda n:mp.cos(mp.pi*n/2)/n, lambda n:mp.sin(mp.pi*n/2)/n],
     '6p: +1/n^2':[
        lambda n:mp.mpf(1), lambda n:1/n, lambda n:((-1)**int(n))/n,
        lambda n:mp.cos(mp.pi*n/2)/n, lambda n:mp.sin(mp.pi*n/2)/n,
        lambda n:1/n**2],
     '8p: +osc/n^2':[
        lambda n:mp.mpf(1), lambda n:1/n, lambda n:((-1)**int(n))/n,
        lambda n:mp.cos(mp.pi*n/2)/n, lambda n:mp.sin(mp.pi*n/2)/n,
        lambda n:1/n**2, lambda n:((-1)**int(n))/n**2,
        lambda n:mp.cos(mp.pi*n/2)/n**2],
    }
    Rs=[]
    for name,bf in bases.items():
        print(f"  basis {name}")
        for w in (16,20,24,28,32,40):
            if w<=len(r) and w>=len(bf)+2:
                R=lsq_fit(r,w,bf)
                print(f"     window {w:2d}: R = {mp.nstr(R,14)}")
                if w>=24: Rs.append(R)

    print("\n=== (3) deoscillated Neville at multiple orders (consensus) ===")
    cons=[]
    for order in (3,4,5,6):
        if len(g)>order+1:
            R=richardson(g,xs,order); cons.append(R)
    if cons:
        mn=min(cons); mx=max(cons); mid=(mn+mx)/2
        print(f"  consensus R in [{mp.nstr(mn,12)}, {mp.nstr(mx,12)}], mid {mp.nstr(mid,12)}")

    print("\n=== test r = 3/2 ===")
    if Rs:
        allR=Rs+cons
        mn=min(allR); mx=max(allR)
        print(f"  pooled R range: [{mp.nstr(mn,12)}, {mp.nstr(mx,12)}]")
        print(f"  3/2 = 1.5  -- {'INSIDE' if mn<=mp.mpf('1.5')<=mx else 'OUTSIDE'} pooled range")
    # PSLQ / identify on the best central estimate
    return v,r,g

if __name__=="__main__":
    path=sys.argv[1] if len(sys.argv)>1 else "/tmp/fr_n64.out"
    main(path)
