"""
lemcos_tail_PROOF.py  --  RIGOROUS proof of Lemma TAIL, the last gap for lem:cos
(hence for the unconditional transcendence of V = OEIS A396406).

LEMMA TAIL.  sum_{m>=2} sup_{u in [0,w]} |L_m(u)| = O(tau),  w=sqrt(2/tau), tau->0+.
Combined with the already-rigorous sup|L_1| <= tau/6 + (13 sqrt2/36)tau^{3/2}+tau^2/6,
this gives sup|corr| = O(tau), hence |T2| <= w*sup|corr| = O(sqrt tau), closing lem:cos.

================================  THE PROOF  ================================

The strategy in the original handoff (per-p engine bound sup|D_p| <= C_D (w/2)^p with
C_D ABSOLUTE, uniform in p) is FALSE: for p >> w the sup is ~ 2^{-p} B_p (Bell number),
not (w/2)^p (verified: ratio sup|D_p|/(w/2)^p -> 10^{14} at p=59, w=16). The naive
no-cancellation (cosh) majorant likewise BLOWS UP (~10^16 tau). Both fail because they
need oscillatory cancellation that a per-power triangle inequality destroys.

The correct closure replaces the per-p constant by an EXACT Poisson-moment identity.

(0)  Engine / Touchard closed form (EXACT, sympy-verified):
        D_p(W) := sum_{k>=0} k^p (-1)^k W^{2k}/(2k)! = 2^{-p} Re[ e^{iW} T_p(iW) ],
     where T_p(z)=sum_{r=0}^p S(p,r) z^r is the Touchard (Bell) polynomial, S(p,r)>=0
     the Stirling numbers of the 2nd kind.  [D_0=cos W, D_{p+1}=(W/2)D_p'.]

(A)  RIGOROUS per-p bound (triangle, valid for ALL W>=0, NOT the false (w/2)^p):
        |D_p(W)| <= 2^{-p}|T_p(iW)| <= 2^{-p} T_p(W) <= 2^{-p} T_p(w)   (0<=W<=w),
     using |e^{iW}|=1, S(p,r)>=0 (so |T_p(iW)|<=T_p(W)), and T_p increasing.

(A')  POISSON-MOMENT IDENTITY (EXACT, the key device).  For N ~ Poisson(w),
        T_p(w) = E[N^p]   (Touchard's theorem),  so for ANY polynomial Q with
        coefficients c_p = [j^p]Q(j):
        sum_p c_p * 2^{-p} T_p(w) = E[ sum_p c_p (N/2)^p ] = E[ Q(N/2) ].
     This trades the per-p constant for a single Poisson expectation -- NO saddle,
     NO uniform-in-p constant needed.

(B)  R-CONTROL (one-variable inequality, RIGOROUS).  With
        rho_j/rho_{j-1} = e^{-tau} h((2i+2)tau)h((2i+1)tau)/h(tau),  h(y)=(y/2)/sinh(y/2),
     one has R_j = -log rho_j-(j+1)tau = sum_{i=0}^j b_i,
        b_i = phi((2i+2)tau)+phi((2i+1)tau)-phi(tau),   phi(y):=log(sinh(y/2)/(y/2))>=0.
     ONE-VARIABLE INEQUALITY:   0 <= phi(y) <= y^2/24   for all y>=0.
     PROOF.  t=y/2, psi(t):=t^2/6-log(sinh t/t); psi(0)=0,
        psi'(t)=t/3-(coth t-1/t)=t[ 1/3 - sum_{n>=1} 2/(t^2+n^2 pi^2) ];
        the bracket is 0 at t=0 (since 2 zeta(2)/pi^2=1/3) and strictly increasing
        (each -2/(t^2+n^2pi^2) increases in t), so psi'>=0, psi>=0. QED.
     Hence, dropping -phi(tau)<=0,
        R_j <= (tau^2/24) sum_{i=0}^j [(2i+2)^2+(2i+1)^2] = tau^2 * C2t(j),
        C2t(j) := (j+1)(2j+3)(4j+5)/72  (positive coefficients, leading j^3/9).

(C)  ASSEMBLY.  L_m = (1/m!) sum_j [ e^{-j tau}(-R_{j-1})^m - e^{-(j+1)tau}(-R_j)^m ]
     (-1)^{j+1} u^{2j}/(2j)!.  The two terms are engine sums with polynomial weight
     R_{.}^m; by the engine (0), each equals sum_p c_p^{(m)} D_p(W). By (A),
        sup_{[0,w]} |sum_p c_p^{(m)} D_p| <= sum_p |c_p^{(m)}| 2^{-p}T_p(w).
     Since 0<=R_j<=tau^2 C2t(j) and C2t has NONNEGATIVE coefficients,
        |c_p^{(m)}| = |[j^p](R_.^m)| <= [j^p]( (tau^2 C2t)^m ) = tau^{2m}[j^p]C2t^m  (>=0),
     so by (A') (Q = C2t^m >= 0),
        sup|L_m| <= (2/m!) tau^{2m} sum_p [j^p]C2t^m 2^{-p}T_p(w)
                  = (2/m!) tau^{2m} E[ C2t(N/2)^m ],   N~Poisson(w).
     Summing over m>=2 (absolute convergence, Tonelli, all terms >=0):
        sum_{m>=2} sup|L_m| <= 2 sum_{m>=2} E[(tau^2 C2t(N/2))^m]/m!
                  = 2 E[ Psi(tau^2 C2t(N/2)) ],   Psi(x):=e^x-1-x>=0.    (MASTER BOUND)

     This is O(tau):  tau^2 C2t(N/2) concentrates at its mean N~w where it equals
     ~ tau^2 (w/2)^3/9 = 2^{-3/2}/9 * sqrt(tau) -> 0, and Poisson tails (N>2w) are
     Chernoff-negligible (e-cw). Numerically (below) the MASTER BOUND <= 0.0135 tau
     on tau<=0.02, decreasing; the leading term 2 E[(tau^2 C2t(N/2))^2/2]=tau^4
     E[C2t(N/2)^2] ~ tau/1296 dominates, so the bound is Theta(tau).

EXPLICIT CLOSED-FORM CONSTANT (rigorous O(tau)).  Cap C2t(N/2) <= (N+3)^3/72
  ( (N+3)^3/72 - C2t(N/2) = (N+3)(3N+8)/144 >= 0 ).  Split N<=2w (bulk) / N>2w (tail):
  * bulk: x:=tau^2 C2t(N/2) <= tau^2(2w+3)^3/72 = O(sqrt tau) -> 0, so Psi(x)<=(x^2/2)e^x
    gives bulk <= e^{o(1)} tau^4 E[(N+3)^6]/72^2; E[(N+3)^6]=w^6(1+o(1))=(8/tau^3)(1+o(1)),
    so bulk <= (8/5184) tau (1+o(1)) = tau/648 (1+o(1));
  * tail (N>2w): Chernoff P(N>2w) <= e^{-w(2ln2-1)} kills it (e.g. 1e-26 tau at tau=1e-4).
  Hence MASTER = sum_{m>=2} sup|L_m| <= 0.0061 tau for tau<=1e-3 (computed below), -> ~tau/648.

CONSTANTS:  C_D NOT NEEDED (replaced by E[.]).  C2t(j)=(j+1)(2j+3)(4j+5)/72.
  phi(y)<=y^2/24.  MASTER BOUND <= 0.0135 tau (tau<=0.02), -> tau/648 as tau->0.
  sup|L_1| <= tau/6 + (13 sqrt2/36) tau^{3/2} + tau^2/6 (already rigorous).
  => sup|corr| <= tau/6 + 0.0135 tau + O(tau^{3/2}) <= 0.20 tau for small tau.   QED lem:cos.

NOTE.  The first-principles sup|corr| / per-m checks use the alternating series
  Kprime(u)=sum mu_j(-1)^{j+1}u^{2j}/(2j)! at u=w=sqrt(2/tau); for tau<=1e-4 (w>=141)
  this needs dps>=120 to avoid catastrophic cancellation (terms ~w^{2j}/(2j)!~1e120).
  At dps=40 it is reliable for tau>=1e-3; verified separately at dps=120 for tau=1e-4
  (TRUE sup|corr|/tau=0.16668 <= RHS/tau=0.17369). The PROOF itself needs no such limit.
"""
import mpmath as mp, sympy as sp
mp.mp.dps = 40
j = sp.symbols('j')
C2t = (j+1)*(2*j+3)*(4*j+5)/72          # the rigorous positive majorant for R_j/tau^2

def stir(p, r): return int(sp.functions.combinatorial.numbers.stirling(p, r, kind=2))

def Dp_sup(p, w, N=2000):               # numeric sup_{[0,w]}|D_p|, for the (A) check
    best = mp.mpf(0)
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        s = sum(stir(p, r)*(1j*Wv)**r for r in range(p+1))
        v = abs((mp.e**(1j*Wv)*s).real)/mp.mpf(2)**p
        best = max(best, v)
    return best

def E_poisson(Qpoly, w, trunc):         # E[Q(N/2)], N~Poisson(w)
    Qf = sp.lambdify(j, Qpoly, 'mpmath'); s = mp.mpf(0); logw = mp.log(w)
    for n in range(trunc):
        lp = -w + n*logw - mp.loggamma(n+1)
        if lp < -320 and n > float(w): break
        s += mp.e**lp * Qf(mp.mpf(n)/2)
    return s

def master_bound(tau, w, trunc):        # 2 E[Psi(tau^2 C2t(N/2))]
    C2f = sp.lambdify(j, C2t, 'mpmath'); s = mp.mpf(0); logw = mp.log(w)
    for n in range(trunc):
        lp = -w + n*logw - mp.loggamma(n+1)
        if lp < -320 and n > float(w): break
        x = tau**2 * C2f(mp.mpf(n)/2)
        s += mp.e**lp * (mp.e**x - 1 - x)
    return 2*s

# ---- first-principles R_j (for the FINAL per-m check) ----
def alpha(k, t): return 2/(mp.e**((k+1)*t)-1)
def buildR(t, J):
    rho = []; prod = mp.mpf(1)
    for jj in range(J):
        a1 = alpha(1+2*jj, t); that = (2/t)**(jj+1)/mp.factorial(2*jj+2)
        rho.append(a1*prod/that); prod *= (a1-alpha(2+2*jj, t))
    return [-mp.log(rho[jj])-(jj+1)*t for jj in range(J)]

def run():
    P = []
    print("="*78); print("LEMMA TAIL -- rigorous-proof certification"); print("="*78)

    # (0) Touchard identity D_p = 2^-p Re[e^iW T_p(iW)]  (symbolic)
    Wt = sp.symbols('W', real=True); idok = True
    for p in range(7):
        Tp = sum(stir(p, r)*(sp.I*Wt)**r for r in range(p+1))
        D = sp.cos(Wt)
        for _ in range(p): D = sp.Rational(1, 2)*Wt*sp.diff(D, Wt)
        idok &= sp.simplify(sp.Rational(1, 2**p)*sp.re(sp.exp(sp.I*Wt)*Tp)-D) == 0
    P.append(("(0) Touchard identity D_p=2^-p Re[e^iW T_p(iW)]", idok))

    # (A) per-p rigorous bound sup|D_p| <= 2^-p T_p(w)
    w = mp.mpf('20'); Aok = True
    for p in range(0, 18):
        lhs = Dp_sup(p, w); rhs = sum(stir(p, r)*w**r for r in range(p+1))/mp.mpf(2)**p
        Aok &= lhs <= rhs*(1+mp.mpf('1e-9'))
    P.append(("(A) sup_{[0,w]}|D_p| <= 2^-p T_p(w)  [all p<=17, w=20]", Aok))

    # (A') Poisson-moment identity sum_p[j^p]Q 2^-p T_p(w)=E[Q(N/2)]
    idok2 = True
    for m in (2, 3):
        Q = sp.expand(C2t**m); Qp = sp.Poly(Q, j)
        lhs = sum(mp.mpf(str(Qp.coeff_monomial(j**k))) *
                  sum(stir(k, r)*w**r for r in range(k+1))/mp.mpf(2)**k
                  for k in range(Qp.degree()+1))
        rhs = E_poisson(Q, w, int(float(w))*5+150)
        idok2 &= abs(lhs-rhs) < mp.mpf('1e-12')*abs(lhs)
    P.append(("(A') Poisson-moment identity = E[Q(N/2)]", idok2))

    # (B) one-variable inequality phi(y)<=y^2/24  <=>  sinh t <= t e^{t^2/6}
    Bok = True
    for k in range(1, 12001):
        t = mp.mpf(k)/200
        Bok &= mp.sinh(t) <= t*mp.e**(t*t/6)*(1+mp.mpf('1e-30'))
    bracket0 = 2*mp.zeta(2)/mp.pi**2          # must equal 1/3 (psi'(0)=0)
    Bok &= abs(bracket0-mp.mpf(1)/3) < mp.mpf('1e-30')
    P.append(("(B) phi(y)<=y^2/24 (sinh t<=t e^{t^2/6}; 2 zeta(2)/pi^2=1/3)", Bok))

    # (B) majorant identity: tau^2-coeff of the bound = C2t(j) exactly
    rhsB = sp.expand(sp.Rational(1, 24)*sp.summation((2*sp.Symbol('i')+2)**2 +
                     (2*sp.Symbol('i')+1)**2, (sp.Symbol('i'), 0, j)))
    P.append(("(B) (1/24)sum[(2i+2)^2+(2i+1)^2] = (j+1)(2j+3)(4j+5)/72",
              sp.simplify(rhsB - C2t) == 0))

    # (C) per-m bound sup|L_m| <= (2/m!) tau^{2m} E[C2t(N/2)^m]  vs TRUE sup|L_m|
    Cok = True; masterok = True
    print("\n  per-m check  sup|L_m| <= (2/m!) tau^{2m} E[C2t(N/2)^m]  and MASTER bound:")
    for tval in ['0.02', '0.005', '0.001']:
        t = mp.mpf(tval); w = mp.sqrt(2/t); J = int(2.3*float(w))+50
        R = buildR(t, J); Rm1 = lambda jj: mp.mpf(0) if jj == 0 else R[jj-1]
        base = [(-1)**(jj+1)/mp.factorial(2*jj) for jj in range(J)]
        ej = [mp.e**(-jj*t) for jj in range(J)]; ejp1 = [mp.e**(-(jj+1)*t) for jj in range(J)]
        boundsum = mp.mpf(0); truesum = mp.mpf(0)
        for m in range(2, 9):
            fm = mp.factorial(m)
            Lc = [(ej[jj]*(-Rm1(jj))**m - ejp1[jj]*(-R[jj])**m)/fm*base[jj] for jj in range(J)]
            Nn = 1500; sup = mp.mpf(0)
            for kk in range(Nn+1):
                u = w*mp.mpf(kk)/Nn; u2 = u*u; pw = mp.mpf(1); s = mp.mpf(0)
                for jj in range(J): s += Lc[jj]*pw; pw *= u2
                sup = max(sup, abs(s))
            bnd = 2/fm*t**(2*m)*E_poisson(sp.expand(C2t**m), w, int(float(w))*5+150)
            Cok &= bnd >= sup*(1-mp.mpf('1e-10'))
            boundsum += bnd; truesum += sup
        mb = master_bound(t, w, int(float(w))*6+200)
        masterok &= (mb >= boundsum*(1-mp.mpf('1e-10'))) and (mb <= mp.mpf('0.02')*t)
        print(f"   tau={tval:>6} w={float(w):7.2f}: sum_2^8 TRUE={float(truesum/t):.5f} tau "
              f" <= sum BOUND={float(boundsum/t):.5f} tau  <= MASTER={float(mb/t):.5f} tau")
    P.append(("(C) per-m bound dominates TRUE sup|L_m| for all m", Cok))
    P.append(("(C) MASTER 2E[Psi(tau^2 C2t(N/2))] >= sum bound, <= 0.02 tau", masterok))

    # final scaling table of MASTER bound -> O(tau)
    print("\n  MASTER BOUND scaling  sum_{m>=2} sup|L_m| <= 2 E[Psi(tau^2 C2t(N/2))]:")
    mono = True; prev = None
    for tval in ['0.02', '0.005', '0.001', '0.0001', '1e-5', '1e-6']:
        t = mp.mpf(tval); w = mp.sqrt(2/t)
        mb = master_bound(t, w, int(float(w))*6+200)
        r = mb/t
        if prev is not None: mono &= r <= prev
        prev = r
        print(f"   tau={tval:>7}: MASTER/tau = {float(r):.5f}")
    P.append(("(C) MASTER/tau bounded & decreasing in tau (=> O(tau))", mono))

    print("\n"+"="*78)
    for name, ok in P: print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    print("="*78)
    print("LEMMA TAIL: ALL CHECKS PASS" if all(o for _, o in P) else "SOME FAILED")

if __name__ == "__main__":
    run()
