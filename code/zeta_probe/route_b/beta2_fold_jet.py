#!/usr/bin/env python3
"""v2.12.7: THE FOLD ATTACK -- first-jet web, jet ledger, certified constants.

FOLD (230 digits, in fold_coords_230 block below; residuals 1e-237):
  q_c = -0.554578610146579707339013210674541937045408130005979924118454435580369...
  z_c =  2.523952520441710290811777674571007634597671751043036920442281828524482...
CERTIFIED: neither q_c nor z_c satisfies an integer polynomial of degree <= 8, height <= 10^14;
no bilinear joint relation (PSLQ, 230 digits, tol 1e-200). TRAP DOCUMENTED: at 120 digits PSLQ
returned degree-8 "relations" (height ~1e12) for BOTH constants -- exposed as spurious by
re-evaluation at 230 digits (residuals 1e-101/1e-98 instead of 1e-200). Always re-certify PSLQ
hits above half working precision.

FOLD-LAW CONSTANT IN CLOSED FORM: |c_n| n^{3/2} |q_c|^n -> |C~| sqrt|q_c| / (2 sqrt(pi))
  = 0.78630831355357658885...,  C~^2 = 2 G_q / (-G_zz) at the fold.
(The old reading 0.7690 from n<=120 was PREASYMPTOTIC: sequence at n=100..299 climbs
0.77668 -> 0.78295 with clean 1/n tail extrapolating to 0.78621.)

MIRROR EQUATION (error #17, self-caught by numeric check): H does NOT solve L.
The second solution is z^{1/2} H, so H solves the MIRROR   H(z) - a(z)H(Qz) + q H(Q^2 z) = 0
(outer q moves to the far end), and L~(thH) = -qz H(Qz). Naive L(H)=0 fails by 0.77.

FIRST-JET WEB AT THE FOLD: six unknowns A=G(Qz_c), B=thG(Qz_c), h=H(z_c), h1=H(Qz_c),
eta=thH(z_c), eta1=thH(Qz_c). Exactly TWO finite-height relations:
  W:  A h = 1 - q_c          (Casoratian at z_c; G(z_c)=0)
  tW: B h = -A eta           (theta-derivative of Casoratian; thG(z_c)=0)
both verified to 236 digits.

INCREMENT LAW (new, clean): for mixed jet-Casoratians C_{u,v}(z) = q u(z)v(Qz) - u(Qz)v(z)
with L(u) = f and L~(v) = g~, the a-terms cancel COMPLETELY:
  C(Qz) - C(z) = g~(z) u(Qz) - f(z) v(Qz).
Telescoping the two mixed Casoratians reproves tW; telescoping the theta-theta one gives the
THIRD exact relation  B eta = sum_{m>=0} q Q^m z_c [G thH - H thG](Q^{m+1} z_c)
(verified 1e-121) -- but its coefficient is an infinite rational series: HEIGHT-INFINITE.

JET LEDGER (the fold no-go): every telescoped first-jet bilinear closes back onto a Casoratian
(the algebra is closed); each additional theta- or delta-jet level adds >= 3 unknowns and exactly
1 finite-height relation; vanishings are the only deficit reducers and the plane maxes out at 2
(no cusps: codim 3 > dim 2). Fold deficit = 4 (minimum over all points; generic zero = 5).
POINT EVALUATION ALONE CANNOT CLOSE A RATIONALITY REDUCTIO ANYWHERE ON THE (q,z)-PLANE.
"""
from mpmath import mp, mpf, matrix, lu_solve, pslq, sqrt, pi
mp.dps=235
def G_terms(q,z,K=62):
    terms=[mp.mpf(1)]
    for k in range(1,K):
        terms.append(terms[-1]*(-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))))
    return terms
def H_terms(q,z,K=62):
    terms=[mp.mpf(1)]
    for k in range(1,K):
        terms.append(terms[-1]*(-q**(2*k-1)*z/((1-q**(2*k))*(1-q**(2*k+1)))))
    return terms
def G(q,z): return sum(G_terms(q,z))
def thG(q,z):
    t=G_terms(q,z); return sum(k*t[k] for k in range(len(t)))
def Gz(q,z):
    t=G_terms(q,z); return sum(k*t[k] for k in range(len(t)))/z
def Gzz(q,z):
    t=G_terms(q,z); return sum(k*(k-1)*t[k] for k in range(len(t)))/z/z
def logderivq(q,k):
    """d/dq log [ q^{k(k-1)}/(q;q)_{2k} ] = k(k-1)/q + sum_{i<=2k} i q^{i-1}/(1-q^i)"""
    s=k*(k-1)/q
    for i in range(1,2*k+1): s+=i*q**(i-1)/(1-q**i)
    return s
def Gq(q,z):
    t=G_terms(q,z); return sum(t[k]*logderivq(q,k) for k in range(len(t)))
def Gzq(q,z):
    t=G_terms(q,z); return sum(k*t[k]*logderivq(q,k) for k in range(len(t)))/z
def H(q,z): return sum(H_terms(q,z))
def thH(q,z):
    t=H_terms(q,z); return sum(k*t[k] for k in range(len(t)))
# --- refine fold to 230 digits ---
q,z=[mpf(l.strip()) for l in open("fold_coords.txt")]
for it in range(6):
    J=matrix([[Gq(q,z),Gz(q,z)],[Gzq(q,z),Gzz(q,z)]])
    d=lu_solve(J,matrix([G(q,z),Gz(q,z)]))
    q-=d[0]; z-=d[1]
print("residuals @235dps:",mp.nstr(abs(G(q,z)),3),mp.nstr(abs(Gz(q,z)),3))
with open("fold_coords_230.txt","w") as f: f.write(mp.nstr(q,232)+"\n"+mp.nstr(z,232)+"\n")
# --- recheck the two degree-8 'relations' from the 120-digit run ---
c_q=[-736185043797,-662274793959,1166981868144,100834134717,38807696764,-545244982078,-429819746866,-52618083157,734092186809]
c_z=[941818953972,-497089940487,732245314637,240141838444,1680398822568,1350681529418,-274776088986,747686206960,-383503818683]
vq=sum(c_q[i]*q**i for i in range(9)); vz=sum(c_z[i]*z**i for i in range(9))
print("deg-8 candidate at q_c evaluates to:",mp.nstr(abs(vq),3)," (spurious if >> 1e-200)")
print("deg-8 candidate at z_c evaluates to:",mp.nstr(abs(vz),3))
# --- certified re-run at tol 1e-200 ---
for name,x in [("q_c",q),("z_c",z)]:
    r=pslq([x**i for i in range(9)],tol=mpf(10)**-200,maxcoeff=10**14,maxsteps=2*10**6)
    print(f"{name} degree 8 @ tol 1e-200: {'RELATION '+str(r) if r else 'none (height 10^14) -- CERTIFIED'}")
# --- first-jet web ---
Q=q*q
A=G(q,Q*z); B=thG(q,Q*z); h=H(q,z); h1=H(q,Q*z); eta=thH(q,z); eta1=thH(q,Q*z)
print()
print("six unknowns (30 digits):")
for nm,v in [("A",A),("B",B),("h",h),("h1",h1),("eta",eta),("eta1",eta1)]:
    print(f"  {nm} = {mp.nstr(v,30)}")
print("control W:  |A*h-(1-q)| =",mp.nstr(abs(A*h-(1-q)),3))
print("control tW: |B*h+A*eta| =",mp.nstr(abs(B*h+A*eta),3))
# --- telescoped Casoratian identities ---
def a_(zz): return q+1-q*zz
def CasGH(zz):  return q*G(q,zz)*H(q,Q*zz)-G(q,Q*zz)*H(q,zz)
def CasTT(zz):  return q*thG(q,zz)*thH(q,Q*zz)-thG(q,Q*zz)*thH(q,zz)
def CasGT(zz):  return q*G(q,zz)*thH(q,Q*zz)-G(q,Q*zz)*thH(q,zz)
def CasTH(zz):  return q*thG(q,zz)*H(q,Q*zz)-thG(q,Q*zz)*H(q,zz)
# general source formula: for u,v with L(u)=f, L(v)=g:
# C(Qz)-C(z) = q g u(Qz) - f v(Qz) + a(q-1) u(Qz)v(Qz) - (q^2-1) u(Qz)v(z)
ztest=mpf('0.7')
lhs=CasTT(Q*ztest)-CasTT(ztest)
f=-q*ztest*G(q,Q*ztest); g=-q*ztest*H(q,Q*ztest)
rhs=q*g*thG(q,Q*ztest)-f*thH(q,Q*ztest)+a_(ztest)*(q-1)*thG(q,Q*ztest)*thH(q,Q*ztest)-(q*q-1)*thG(q,Q*ztest)*thH(q,ztest)
print("source formula check (generic z): |lhs-rhs| =",mp.nstr(abs(lhs-rhs),3))
# telescope: C(z_c) = -sum_{m>=0} [C(Q^{m+1}z_c)-C(Q^m z_c)];  C(z_c) = -B*eta
tot=mp.mpf(0); zz=z
for m in range(300):
    tot+=CasTT(Q*zz)-CasTT(zz)
    zz*=Q
    if abs(zz)<mpf(10)**-120: break
print("theta-theta telescope: |C(z_c)+sum| = |(-B*eta)+sum| =",mp.nstr(abs(CasTT(z)+ -1*(-tot) if False else CasTT(z)-(-tot)),3))
print("  [C(z_c) =",mp.nstr(CasTT(z),20),", telescoped sum ->",mp.nstr(-tot,20),"]")
# --- fold-law constant in closed form ---
Ctilde=sqrt(2*Gq(q,z)/(-Gzz(q,z)))
pred=abs(Ctilde)*sqrt(abs(q))/(2*sqrt(pi))
print()
print("fold sqrt coefficient C~ =",mp.nstr(Ctilde,25))
print("predicted fold-law constant |C~|sqrt|q_c|/(2 sqrt pi) =",mp.nstr(pred,15)," (measured 0.7690)")
# ===== corrected mirror-equation verification + third relation + fold-law convergence =====
from mpmath import mp, mpf, sqrt, pi
mp.dps=120
def G_terms(q,z,K=52):
    t=[mp.mpf(1)]
    for k in range(1,K): t.append(t[-1]*(-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))))
    return t
def H_terms(q,z,K=52):
    t=[mp.mpf(1)]
    for k in range(1,K): t.append(t[-1]*(-q**(2*k-1)*z/((1-q**(2*k))*(1-q**(2*k+1)))))
    return t
G=lambda q,z: sum(G_terms(q,z))
thG=lambda q,z: sum(k*t for k,t in enumerate(G_terms(q,z)))
H=lambda q,z: sum(H_terms(q,z))
thH=lambda q,z: sum(k*t for k,t in enumerate(H_terms(q,z)))
q,z=[mpf(l.strip()) for l in open("fold_coords_230.txt")]
mp.dps=120
Q=q*q
a=lambda zz: q+1-q*zz
zt=mpf('0.7')
print("MIRROR equation L~(H) = H(z)-a H(Qz)+q H(Q^2 z):",mp.nstr(abs(H(q,zt)-a(zt)*H(q,Q*zt)+q*H(q,Q*Q*zt)),3))
print("L~(thH)+qzH(Qz):",mp.nstr(abs(thH(q,zt)+q*zt*H(q,Q*zt)-a(zt)*thH(q,Q*zt)+q*thH(q,Q*Q*zt)),3))
CTT=lambda zz: q*thG(q,zz)*thH(q,Q*zz)-thG(q,Q*zz)*thH(q,zz)
S=lambda zz: q*zz*(G(q,Q*zz)*thH(q,Q*zz)-H(q,Q*zz)*thG(q,Q*zz))
print("increment law C(Qz)-C(z)-S(z) (generic):",mp.nstr(abs(CTT(Q*zt)-CTT(zt)-S(zt)),3))
# telescope at the fold: B*eta = sum_m S(Q^m z_c)
B=thG(q,Q*z); eta=thH(q,z)
tot=mp.mpf(0); zz=z
for m in range(200):
    tot+=S(zz); zz*=Q
    if abs(zz)<mpf(10)**-115: break
print("THIRD RELATION |B*eta - sum_m S(Q^m z_c)| =",mp.nstr(abs(B*eta-tot),3))
print("   [B*eta =",mp.nstr(B*eta,25),"]")
# fold-law constant: closed form vs 300-coefficient measurement
import json
u1=json.load(open("ulattice_300.json"))["1"]
def logderivq(q,k):
    s=k*(k-1)/q
    for i in range(1,2*k+1): s+=i*q**(i-1)/(1-q**i)
    return s
Gq=lambda qq,zz: sum(t*logderivq(qq,k) for k,t in enumerate(G_terms(qq,zz)))
Gzz_=lambda qq,zz: sum(k*(k-1)*t for k,t in enumerate(G_terms(qq,zz)))/zz/zz
Ct=sqrt(2*Gq(q,z)/(-Gzz_(q,z)))
pred=abs(Ct)*sqrt(abs(q))/(2*sqrt(pi))
print()
print("fold-law constant closed form:",mp.nstr(pred,20))
for n in (100,150,200,250,299):
    print(f"  |c_n| n^1.5 |q_c|^n at n={n}: {mp.nstr(abs(u1[n])*mpf(n)**mpf(1.5)*abs(q)**n,12)}")
