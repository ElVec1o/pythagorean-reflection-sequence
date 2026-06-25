import sympy as sp
tau,w,s=sp.symbols('tau w s',positive=True)
ORD=14
def q(a): return sp.series(sp.exp(-a*tau),tau,0,ORD+1).removeO()
def inv1mq(m): return sp.series(1/(1-sp.exp(-m*tau)),tau,0,ORD+1).removeO()
def fac(j): return sp.expand(2*q(2*j+4)*inv1mq(2*j+3)-2*q(2*j+3)*inv1mq(2*j+2))
def rho(k):
    pr=sp.Integer(1)
    for j in range(k): pr=sp.expand(sp.series(pr*fac(j),tau,0,ORD).removeO())
    term=sp.expand(sp.series(2*q(1)*inv1mq(2*k+2)*pr,tau,0,ORD).removeO())
    return sp.expand(sp.series(term*sp.Integer(-1)**k*sp.factorial(2*k+2)*(tau/2)**(k+1),tau,0,ORD).removeO())
PS=[2,4,6,8,10]; maxk=16; cp={p:[] for p in PS}
for k in range(maxk+1):
    P=sp.Poly(rho(k),tau)
    for p in PS: cp[p].append(sp.nsimplify(P.coeff_monomial(tau**p)))
kk=sp.symbols('kk'); polys={}
for p in PS:
    ys=cp[p]; n=len(ys)
    coef=sp.Matrix([[sp.Integer(kx)**d for d in range(n)] for kx in range(n)]).solve(sp.Matrix(ys))
    polys[p]=sp.expand(sum(coef[d]*kk**d for d in range(n)))
    print('c_%d deg %d'%(p,sp.Poly(polys[p],kk).degree()),flush=True)
def theta(f): return sp.Rational(1,2)*w*sp.diff(f,w)
def thm1(f): return sp.expand(theta(f)-f)
base=1-sp.cos(w)
def apply_cp(poly):
    pol=sp.Poly(poly,kk); cur=base; pw=[cur]
    for d in range(1,pol.degree()+1): cur=thm1(cur); pw.append(cur)
    return sp.expand(sum(pol.coeff_monomial(kk**d)*pw[d] for d in range(pol.degree()+1)))
corr=sum(tau**p*apply_cp(polys[p]) for p in PS)
om=sp.expand(sp.cos(w)-corr)
Ccos=om.coeff(sp.cos(w)); Csin=om.coeff(sp.sin(w))
NS=9
Cc=sp.series(sp.expand(Ccos.subs([(w,sp.sqrt(2)/s),(tau,s**2)])),s,0,NS).removeO()
Cs=sp.series(sp.expand(Csin.subs([(w,sp.sqrt(2)/s),(tau,s**2)])),s,0,NS).removeO()
X=sp.series(-Cs/Cc,s,0,NS).removeO()
dev=sp.series(sp.atan(X),s,0,NS).removeO()
P=sp.Poly(sp.expand(dev),s)
c1=sp.nsimplify(P.coeff_monomial(s**1)*sp.sqrt(2))
c2=sp.nsimplify(P.coeff_monomial(s**3)*2*sp.sqrt(2))
c3=sp.nsimplify(P.coeff_monomial(s**5)*4*sp.sqrt(2))
c4=sp.nsimplify(P.coeff_monomial(s**7)*8*sp.sqrt(2))
print('c1 =',c1,' match',c1==sp.Rational(1,18),flush=True)
print('c2 =',c2,' match',c2==sp.Rational(-41,600),flush=True)
print('c3 =',c3,' match',c3==sp.Rational(-1915,7056),flush=True)
print('c4 =',c4,' match',c4==sp.Rational(-18617,51840),flush=True)
