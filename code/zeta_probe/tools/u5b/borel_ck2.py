import sympy as sp
import sys, json
from sympy import Rational as Q, Integer as Z, factorial, binomial, bernoulli

# Fast c_k generator using manual truncated power-series (lists of Rationals in tau).
# Avoids sympy.series overhead.

NPAIR = int(sys.argv[1]) if len(sys.argv) > 1 else 6
# PMAX = number of correction orders (in tau).  Decoupled from NPAIR.
PMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2 * NPAIR
PS = list(range(2, PMAX + 1, 2))
ORD = PMAX + 3                  # keep tau^0 .. tau^{ORD-1}
maxk = 3 * (PMAX // 2) + 2

# ---- power series as list of length ORD, coeffs of tau^0..tau^{ORD-1} ----
def smul(a, b):
    r = [Z(0)] * ORD
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j >= ORD:
                break
            if bj != 0:
                r[i + j] += ai * bj
    return r

def sscal(a, c):
    return [c * x for x in a]

# exp(-a tau) coeffs:  (-a)^n / n!
def s_q(a):
    return [Q((-a) ** n, factorial(n)) for n in range(ORD)]

# 1/(1-exp(-m tau)) = 1/(m tau) * (m tau)/(1-e^{-m tau}).
# (x)/(1-e^{-x}) = sum_{n>=0} B_n^+ x^n / n!  with B_1^+ = +1/2.
# So 1/(1-e^{-m tau}) = (1/(m tau)) * sum_n c_n (m tau)^n, c_n = B_n^+/n!.
# = sum_{n>=0} (B_n^+/n!) m^{n-1} tau^{n-1}.  Lowest power tau^{-1}.
# We need it multiplied into things that vanish — but here it appears as inv1mq(2k+2) etc.
# In rho, inv1mq always multiplies q(positive)*... The product 2 q(1) inv1mq(2k+2) prod:
# the tau^{-1} pole cancels against the overall (tau/2)^{k+1}? Let's just carry a
# Laurent series with one negative power. Represent as (pole_coeff for tau^{-1}, list tau^0..).
# Simpler: multiply everything by tau^{numpoles} implicitly — but poles differ per factor.
# Cleanest: build inv1mq as Laurent with index offset -1.

def s_inv1mq(m):
    # returns Laurent: dict power->coeff, powers -1..ORD-2
    Bplus = lambda n: bernoulli(n) if n != 1 else Q(1, 2)
    d = {}
    for n in range(ORD + 1):
        p = n - 1
        if p > ORD - 1:
            break
        d[p] = Q(Bplus(n), factorial(n)) * Z(m) ** (n - 1)
    return d

# To avoid Laurent bookkeeping across many multiplications, note structure of rho:
#   pr = prod_{j<k} fac(j),  fac(j)=2 q(2j+4) inv1mq(2j+3) - 2 q(2j+3) inv1mq(2j+2)
#   term = 2 q(1) inv1mq(2k+2) * pr
#   rho(k) = term * (-1)^k (2k+2)! (tau/2)^{k+1}
# Each fac(j): inv1mq has a simple pole tau^{-1}; q(.) starts at tau^0 with value 1.
# fac(j) = 2[q(2j+4)inv1mq(2j+3) - q(2j+3)inv1mq(2j+2)].
# Leading pole: 2[1/( (2j+3)tau ) - 1/((2j+2)tau)] = 2/tau [1/(2j+3)-1/(2j+2)] = O(1/tau).
# So fac(j) ~ C/tau. prod_{j<k} fac(j) ~ tau^{-k}. times inv1mq(2k+2)~tau^{-1} => tau^{-(k+1)}.
# times (tau/2)^{k+1} => tau^0.  Good, rho(k) is a regular power series.
# Implement Laurent properly but compactly.

class Laur:
    __slots__=('lo','c')   # c[i] = coeff of tau^{lo+i}
    def __init__(self, lo, c):
        self.lo=lo; self.c=c
    @staticmethod
    def from_taylor(lst):
        return Laur(0, list(lst))
    def trim_to(self, hi):  # keep up to tau^{hi}
        pass

def laur_q(a):
    return Laur(0, [Q((-a)**n, factorial(n)) for n in range(ORD)])

def laur_inv1mq(m):
    Bplus = lambda n: bernoulli(n) if n != 1 else Q(1,2)
    c=[]
    for n in range(ORD+2):
        c.append(Q(Bplus(n), factorial(n)) * Z(m)**(n-1))
    return Laur(-1, c)

HItop = ORD - 1   # highest tau power we ultimately need (rho is tau^0..; we need up to PMAX)

def laur_mul(A, B):
    lo = A.lo + B.lo
    # we only ever need powers up to HItop; cap length
    maxlen = HItop - lo + 1
    if maxlen <= 0:
        return Laur(lo, [Z(0)])
    r=[Z(0)]*maxlen
    for i,ai in enumerate(A.c):
        if ai==0: continue
        pa=A.lo+i
        for j,bj in enumerate(B.c):
            if bj==0: continue
            p=pa+B.lo+j
            idx=p-lo
            if idx<0: continue
            if idx>=maxlen: break
            r[idx]+=ai*bj
    return Laur(lo, r)

def laur_sub(A,B):
    lo=min(A.lo,B.lo); hi=max(A.lo+len(A.c)-1, B.lo+len(B.c)-1)
    hi=min(hi, HItop)
    r=[Z(0)]*(hi-lo+1)
    for i,ai in enumerate(A.c):
        p=A.lo+i
        if p>hi: break
        r[p-lo]+=ai
    for i,bi in enumerate(B.c):
        p=B.lo+i
        if p>hi: break
        r[p-lo]-=bi
    return Laur(lo, r)

def laur_scal(A,c):
    return Laur(A.lo,[c*x for x in A.c])

def laur_shift(A,k):   # multiply by tau^k
    return Laur(A.lo+k, list(A.c))

def fac_l(j):
    t1=laur_mul(laur_q(2*j+4), laur_inv1mq(2*j+3))
    t2=laur_mul(laur_q(2*j+3), laur_inv1mq(2*j+2))
    return laur_scal(laur_sub(t1,t2), Z(2))

def rho_l(k):
    pr=Laur(0,[Z(1)])
    for j in range(k):
        pr=laur_mul(pr, fac_l(j))
    term=laur_mul(laur_scal(laur_q(1),Z(2)), laur_inv1mq(2*k+2))
    term=laur_mul(term, pr)
    # * (-1)^k (2k+2)! * (1/2)^{k+1} * tau^{k+1}
    c=Z(-1)**k * factorial(2*k+2) * Q(1, Z(2)**(k+1))
    term=laur_scal(term, c)
    term=laur_shift(term, k+1)
    # now should be Laurent with lo>=0; extract tau^p
    return term

def coeff_of(L, p):
    idx=p-L.lo
    if idx<0 or idx>=len(L.c): return Z(0)
    return L.c[idx]

print("building rho(k) k=0..%d (ORD=%d) ..."%(maxk,ORD), flush=True)
allrho=[rho_l(k) for k in range(maxk+1)]
print("rho done", flush=True)

kk=sp.symbols('kk'); polys={}
for p in PS:
    deg=3*(p//2); n=deg+1
    if n>maxk+1: n=maxk+1
    ys=[coeff_of(allrho[k],p) for k in range(n)]
    M=sp.Matrix([[Z(kx)**d for d in range(n)] for kx in range(n)])
    coef=M.solve(sp.Matrix(ys))
    polys[p]=sp.expand(sum(coef[d]*kk**d for d in range(n)))
    if n<=maxk:
        chk=sp.simplify(polys[p].subs(kk,n)-coeff_of(allrho[n],p))
        ok=(chk==0)
    else: ok='n/a'
    print('c_%d deg %d check=%s'%(p,sp.Poly(polys[p],kk).degree(),ok),flush=True)

w,s=sp.symbols('w s',positive=True)
theta=lambda f: Q(1,2)*w*sp.diff(f,w)
thm1=lambda f: sp.expand(theta(f)-f)
base=1-sp.cos(w)
def apply_cp(poly):
    pol=sp.Poly(poly,kk); cur=base; pw=[cur]
    for d in range(1,pol.degree()+1):
        cur=thm1(cur); pw.append(cur)
    return sp.expand(sum(pol.coeff_monomial(kk**d)*pw[d] for d in range(pol.degree()+1)))
print("assembling ...",flush=True)
tau=sp.symbols('tau',positive=True)
corr=sum(tau**p*apply_cp(polys[p]) for p in PS)
om=sp.expand(sp.cos(w)-corr)
Ccos=om.coeff(sp.cos(w)); Csin=om.coeff(sp.sin(w))
NS=2*NPAIR+2
Cc=sp.series(sp.expand(Ccos.subs([(w,sp.sqrt(2)/s),(tau,s**2)])),s,0,NS).removeO()
Cs=sp.series(sp.expand(Csin.subs([(w,sp.sqrt(2)/s),(tau,s**2)])),s,0,NS).removeO()
X=sp.series(-Cs/Cc,s,0,NS).removeO()
dev=sp.series(sp.atan(X),s,0,NS).removeO()
P=sp.Poly(sp.expand(dev),s)
known={1:Q(1,18),2:Q(-41,600),3:Q(-1915,7056),4:Q(-18617,51840),5:Q(-942829,29272320)}
cks=[]
print("\n--- c_k ---",flush=True)
for k in range(1,NPAIR+1):
    e=2*k-1
    val=sp.nsimplify(P.coeff_monomial(s**e)*Z(2)**Q(e,2)); val=sp.simplify(val)
    cks.append(val); chk=''
    if k in known: chk='  match=%s'%(sp.simplify(val-known[k])==0)
    print('c_%d = %s%s'%(k,val,chk),flush=True)
with open('/Users/vico/Documents/elvec1o/u5b/cks.json','w') as f:
    json.dump([str(c) for c in cks],f)
print("\nwrote %d coeffs"%len(cks),flush=True)
