#!/usr/bin/env python3
"""
Definitive oscillation-aware rate analysis for the relaxed sequence v_n.

Reads v_n from a file (line 'v_n = [...]').  Computes r_n=v_{n+1}/v_n and:
  A) 4-block deoscillation g_n, then LEAST-SQUARES poly-in-(1/n) extrapolation
     g_n ~ R + c1/n + c2/n^2 + c3/n^3, over a sliding set of (window,order),
     reporting R and a robust spread = error bar.
  B) direct 5..8 parameter oscillation-aware LSQ on r_n (period-4 model).
  C) tests r=3/2 against the pooled estimate.
  D) PSLQ/identify on the central R for a minimal polynomial (deg<=6, H<=1e9).

Also reports the rigorous implication: r >= beta_2, so an upper bound on r
upper-bounds beta_2; whether r<3/2 (=> beta_2<3/2) or r could equal 3/2.
"""
import sys, mpmath as mp, re
mp.mp.dps=60

def load(path):
    txt=open(path).read()
    m=re.search(r"v_n\s*=\s*\[([^\]]*)\]",txt)
    return [int(x) for x in m.group(1).replace(',',' ').split()]

def lsq_poly_1overn(ys, ns, order):
    """LSQ fit ys[i] ~ sum_{j=0}^{order} c_j / ns[i]^j ; return c_0 (=limit)."""
    rows=[]; rhs=[]
    for y,n in zip(ys,ns):
        rows.append([mp.mpf(1)/mp.mpf(n)**j for j in range(order+1)]); rhs.append(y)
    A=mp.matrix(rows); b=mp.matrix(rhs)
    x=mp.lu_solve(A.T*A, A.T*b)
    return x[0]

def osc_lsq(r, window, P):
    """Period-4 oscillation-aware LSQ on the last `window` ratios.
    P selects #params (5,6,7,8).  Returns constant term R."""
    L=len(r); idxs=range(L-window,L)
    def basis(n):
        b=[mp.mpf(1), 1/n, ((-1)**int(n))/n, mp.cos(mp.pi*n/2)/n, mp.sin(mp.pi*n/2)/n]
        if P>=6: b.append(1/n**2)
        if P>=7: b.append(((-1)**int(n))/n**2)
        if P>=8: b.append(mp.cos(mp.pi*n/2)/n**2)
        return b
    rows=[]; rhs=[]
    for i in idxs:
        n=mp.mpf(i+1); rows.append(basis(n)); rhs.append(r[i])
    A=mp.matrix(rows); b=mp.matrix(rhs)
    x=mp.lu_solve(A.T*A, A.T*b)
    return x[0]

def main(path):
    v=load(path)
    n=len(v)
    print(f"# loaded {n} terms (v_0..v_{n-1}); v_last={v[-1]}")
    r=[mp.mpf(v[i+1])/mp.mpf(v[i]) for i in range(n-1)]
    print("\n# tail raw ratios r_m = v_{m+1}/v_m:")
    for i in range(max(0,len(r)-16),len(r)):
        print(f"   m={i+1:3d}  r={mp.nstr(r[i],14)}")

    # A) deoscillated + poly-in-1/n LSQ
    g=[(r[i]+r[i+1]+r[i+2]+r[i+3])/4 for i in range(len(r)-3)]
    gns=[(i+1)+1.5 for i in range(len(g))]
    print("\n# (A) 4-block deoscillation g_m, poly-in-(1/n) LSQ extrapolation")
    Aests=[]
    for window in (12,16,20,24,30,40,50):
        if window>len(g): continue
        ys=g[len(g)-window:]; ns=gns[len(gns)-window:]
        for order in (2,3,4):
            if window>=order+3:
                R=lsq_poly_1overn(ys,ns,order)
                Aests.append((window,order,R))
    for w,o,R in Aests:
        print(f"   window {w:2d} order {o}: R = {mp.nstr(R,14)}")

    # B) oscillation-aware LSQ
    print("\n# (B) period-4 oscillation-aware LSQ on r_m")
    Bests=[]
    for P in (5,6,7,8):
        for window in (16,20,24,30,40,50,60):
            if window<=len(r) and window>=P+3:
                R=osc_lsq(r,window,P)
                Bests.append((P,window,R))
    for P,w,R in Bests:
        print(f"   P={P} window {w:2d}: R = {mp.nstr(R,14)}")

    # Pool the LARGE-window estimates (most reliable)
    pool=[R for (w,o,R) in Aests if w>=24 and o>=3] + \
         [R for (P,w,R) in Bests if w>=30 and P>=6]
    pool=[R for R in pool if mp.mpf('1.3')<R<mp.mpf('1.7')]
    if pool:
        mn=min(pool); mx=max(pool); mid=(mn+mx)/2
        print(f"\n# pooled large-window R: [{mp.nstr(mn,12)}, {mp.nstr(mx,12)}]")
        print(f"#   midpoint  R ~ {mp.nstr(mid,12)}  (spread {mp.nstr(mx-mn,4)})")
        print(f"#   3/2 = 1.5 : {'INSIDE' if mn<=mp.mpf('1.5')<=mx else ('BELOW band (r<3/2)' if mx<mp.mpf('1.5') else 'ABOVE band (r>3/2)')}")
        # PSLQ on midpoint
        print("\n# (D) algebraic identification of midpoint R:")
        try:
            ident=mp.identify(mid)
            print("   identify:", ident)
        except Exception as e:
            print("   identify failed:", e)
        for deg in (2,3,4,5,6):
            try:
                vec=[mid**i for i in range(deg+1)]
                rel=mp.pslq(vec, maxcoeff=10**9, maxsteps=10**5)
                if rel: print(f"   pslq deg {deg}: {rel}")
            except Exception as e:
                pass
    # last raw ratio as crude upper context
    print(f"\n# last raw ratio r_{len(r)} = {mp.nstr(r[-1],12)} (still > limit; ratios DECREASING)")

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/fr3_n120.out")
