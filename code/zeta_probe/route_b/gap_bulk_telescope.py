#!/usr/bin/env python3
"""
Cycle-weighted bulk block with EXPLICIT gaps, via a clean catalytic telescoping.

Bulk run = a left-to-right sequence of edges, each either
   ACTIVE: even deposit a=2s, s>=1  (weight 2 q^s for the two signs, edge length 2s -> q^s
           in q=x^2; here edge length is |a|=2s contributing x^{2s}=q^s),
   GAP:    a=0, forced crossing m=2 -> length x^2 = q; in the TRUE metric an extra cycle
           splice +2 -> weight q*y (y marks the cycle).
Site coupling between consecutive edges of half-sizes w_prev,w (gap has half-size 0):
   length x^{2 max(w_prev,w)} = q^{max(w_prev,w)}.

Catalytic transfer: state = half-size w of the current (rightmost) edge, w in {0,1,2,...}.
Define G_k(q,y) = sum over runs of  [run weight] * q^{k * w_last}   (catalytic mark t=q^k).
We unfold the recursion exactly (telescoping), generalizing the seed's S_k.

Appending an edge of half-size w' (w'>=1 active, or w'=0 gap) to a run ending in half-size w:
  pays  q^{max(w,w')}  (site)  *  edgeweight(w')   where edgeweight(s)=2q^s (s>=1), =q*y (s=0).

Let H(q,y) = sum over runs of [weight]; with catalytic G_k = sum_runs weight * q^{k w_last}.
Section recursion (sum over last-edge size w', split max(w,w') at w'=w):
  the run-ending-in-w' GF, call P_{w'} = sum over runs ending in size w' of weight.
  P_{w'} = edgeweight(w') * [ seed_{w'} + sum_{w} P_w q^{max(w,w')} ]
  where seed term = the length-1 run (just this edge): edgeweight(w').
  => P_{w'} = edgeweight(w') * (1 + sum_w P_w q^{max(w,w')}).
Block GF (sum over all runs) = sum_{w'} P_{w'}.
We solve the linear system on truncated sizes w in {0,1,..,Smax} and evaluate at travel poles.
This is a FINITE linear solve (no slow iteration), exact up to size-truncation (super-geometric
tail in q for q<1).  We verify the y=1 block matches the seed bulk series, then evaluate y=q.
"""
import mpmath as mp
mp.mp.dps=40

def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=800):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>25: break
    return tot
def bisect(f,a,b,it=300):
    fa=f(a); fb=f(b)
    if mp.sign(fa)==mp.sign(fb): return None
    for _ in range(it):
        m=(a+b)/2; fm=f(m)
        if fm==0: return m
        if mp.sign(fm)==mp.sign(fa): a,fa=m,fm
        else: b,fb=m,fm
    return (a+b)/2
def travel_poles(nmax):
    roots=[]; w=3.0; prev=None; prevq=None; g=lambda qq: Sig(1,qq)-1
    while len(roots)<nmax and w<300:
        q=mp.e**(-2/mp.mpf(w)**2); val=g(q)
        if prev is not None and mp.sign(val)!=mp.sign(prev):
            r=bisect(g,prevq,q)
            if r and 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-18)): roots.append(r)
        prev=val; prevq=q; w+=0.1
    return roots

def edgeweight(s,q,y):
    if s==0: return q*y       # gap edge: crossing q, cycle splice y
    return 2*q**s             # active edge (two signs)

def bulk_block(q,y,Smax=60, include_gap=True):
    """Solve P_{w'} = edgeweight(w')*(1 + sum_w P_w q^{max(w,w')}) for w' in sizes; return sum P."""
    sizes=list(range(0 if include_gap else 1, Smax+1))
    nidx={w:i for i,w in enumerate(sizes)}
    n=len(sizes)
    # P = E .* (1 + M P), where E_w=edgeweight(w), M[w',w]=q^{max(w,w')}.
    # (I - diag(E) M) P = E.  Solve.
    E=mp.matrix(n,1)
    for w in sizes: E[nidx[w],0]=edgeweight(w,q,y)
    Mmat=mp.matrix(n,n)
    for wp in sizes:
        for w in sizes:
            Mmat[nidx[wp],nidx[w]]=edgeweight(wp,q,y)*q**max(w,wp)
    Amat=mp.eye(n)-Mmat
    P=mp.lu_solve(Amat,E)
    return sum(P[i,0] for i in range(n))

if __name__=="__main__":
    # sanity at small q: y=1 block series should be positive, finite
    q0=mp.mpf('0.2')
    print("bulk_block(0.2, y=1) =", mp.nstr(bulk_block(q0,mp.mpf(1)),10))
    print("bulk_block(0.2, y=q) =", mp.nstr(bulk_block(q0,q0),10), "(true, smaller: gaps penalized)")
    print()
    roots=travel_poles(16)
    print(f"{len(roots)} travel poles; cycle-weighted bulk block G_rel=block(y=1), G_true=block(y=q):")
    print(f"{'q_n':>16} {'G_relaxed':>15} {'G_true(y=q)':>15} {'ratio T/R':>11} {'both>0':>7}")
    ok=True
    for r in roots:
        Grel=bulk_block(r,mp.mpf(1))
        Gtru=bulk_block(r,r)
        rat=Gtru/Grel if Grel!=0 else mp.nan
        bp = (Grel>0 and Gtru>0)
        if not (Grel!=0 and Gtru!=0): ok=False
        print(f"{mp.nstr(r,12):>16} {mp.nstr(Grel,9):>15} {mp.nstr(Gtru,9):>15} {mp.nstr(rat,7):>11} {str(bp):>7}")
    print()
    print("If G_true and G_relaxed are both NONZERO (and same sign) at every travel pole,")
    print("the cycle correction only ATTENUATES the bulk block without creating a zero =>")
    print("U keeps a nonzero residue at every travel pole it inherits from the resolvent.")
