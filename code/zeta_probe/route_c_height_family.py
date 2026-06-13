import sys, io, contextlib
sys.path.insert(0, "/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe")
sys.argv = ['lamp_formula','0']
with contextlib.redirect_stdout(io.StringIO()):
    from lamp_formula import formula_len
import sympy as sp, mpmath as mp
mp.mp.dps = 40
t = sp.symbols('t')

def mu_from_beta(beta_expr):
    I = sp.I
    zeta = sp.simplify((1 + I*beta_expr)/(1 - I*beta_expr))
    poly = sp.Poly(sp.minimal_polynomial(zeta, t), t, domain='QQ')
    coeffs = poly.all_coeffs()
    L=1
    for c in coeffs: L=sp.ilcm(L, sp.Rational(c).q)
    intc=[int(sp.Rational(c)*L) for c in coeffs]
    g=0
    for c in intc: g=sp.igcd(g,c)
    intc=[c//g for c in intc]
    if intc[0]<0: intc=[-c for c in intc]
    return intc

def polymul(a,b):
    r={}
    for i,ci in a.items():
        for j,cj in b.items(): r[i+j]=r.get(i+j,0)+ci*cj
    return {k:v for k,v in r.items() if v!=0}

def kernel_poly(mu,f):
    n=len(mu)-1
    md={n-i:mu[i] for i in range(n+1) if mu[i]}
    P=polymul({1:1,0:-1},md); P=polymul(P,f)
    return {k:2*v for k,v in P.items()}

def Llen(P): return formula_len(1,0,0,tuple(sorted(P.items())))

def f_catalog(maxdeg=4):
    base=[{0:1}]
    for d in range(1,maxdeg+1): base.append({0:1,d:1}); base.append({0:1,d:-1})
    for s in (1,-1):
        base.append({0:1,1:2*s,2:1}); base.append({0:1,1:3*s,2:3,3:s})
    base+= [{0:1,1:1,2:1},{0:1,1:-1,2:1},{0:1,1:1,2:-1},{0:1,1:-1,2:-1}]
    for s in (1,-1): base.append({0:1,2:s}); base.append({0:1,4:s})
    seen=set(); out=[]
    for f in base:
        k=tuple(sorted(f.items()))
        if k in seen: continue
        seen.add(k); out.append(f)
    return out

def best_L(mu,maxdeg=4,maxshift=10):
    best=None;bestf=None
    for f0 in f_catalog(maxdeg):
        for shift in range(-maxshift,maxshift+1):
            f={k+shift:v for k,v in f0.items()}
            L=Llen(kernel_poly(mu,f))
            if L is None: continue
            if best is None or L<best: best=L; bestf=(tuple(sorted(f0.items())),shift)
    return best,bestf

def l1_height(mu): return sum(abs(v) for v in kernel_poly(mu,{0:1}).values())

def mahler(mu):
    P=kernel_poly(mu,{0:1})
    degs=sorted(P.keys())
    coeffs=[P.get(d,0) for d in range(degs[0],degs[-1]+1)]
    hi=list(reversed(coeffs))
    lead=abs(hi[0])
    roots=mp.polyroots([mp.mpf(c) for c in hi],maxsteps=300,extraprec=300)
    M=mp.mpf(lead)
    for r in roots:
        if abs(r)>1: M*=abs(r)
    return M

shapes=[]
for beta in [2,3,4,5,6,7]:
    shapes.append((f"beta={beta}", mu_from_beta(sp.Integer(beta))))

print("RATIONAL SHAPES", flush=True)
print(f"{'shape':10} {'mu':18} {'L1':>4} {'Mahler':>9} {'L':>5} {'n':>4}  c", flush=True)
for name,mu in shapes:
    L,f=best_L(mu)
    h1=l1_height(mu); M=float(mahler(mu)); n=-(-int(L)//2)
    c=mu[0]
    mustr=f"{mu[0]}t^2+{mu[1]}t+{mu[2]}"
    print(f"{name:10} {mustr:18} {h1:>4} {M:>9.4f} {int(L):>5} {n:>4}  c={c}", flush=True)
