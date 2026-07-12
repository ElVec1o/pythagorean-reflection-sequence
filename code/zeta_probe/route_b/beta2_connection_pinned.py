import mpmath as mp
mp.mp.dps=60
def build(qv):
    q=mp.mpf(qv); Q=q*q
    def theta_q(x,N=90):
        return sum(q**(mp.mpf(n)*(n-1)/2)*mp.mpc(x)**n for n in range(-N,N+1))
    def theta_Q(x,N=90):
        return sum(Q**(mp.mpf(n)*(n-1)/2)*mp.mpc(x)**n for n in range(-N,N+1))
    KB=140
    bs=[mp.mpf(1)]
    for k in range(1,KB):
        bs.append((-(q+1)*Q*bs[k-1]-(Q**(3-k)*bs[k-2] if k>=2 else 0))/(q*(Q**k-1)))
    beta=[bs[k]*q**(mp.mpf(k)*(k+1)/2) for k in range(KB)]
    def Bhat(xi):
        return sum(beta[k]*mp.mpc(xi)**(-k) for k in range(KB))
    def f1s(z,lam,M=70,Mneg=45):
        vals={0:Bhat(lam),1:Bhat(lam*q)}
        for m in range(0,M+1):
            xi=lam*q**m
            vals[m+2]=(vals[m]+((q+1)/xi)*vals[m+1])/(1-1/xi**2)
        num=mp.mpf(0)
        for m in range(-Mneg,M+1):
            Bv=vals[m] if m>=0 else Bhat(lam*q**m)
            num+=q**(mp.mpf(m)*(m-1)/2)*(lam/mp.mpc(z))**m*Bv
        return theta_Q(-mp.mpc(z))*num/theta_q(lam/mp.mpc(z))
    def G(z,K=300):
        t=mp.mpf(0); poch=mp.mpf(1)
        for k in range(K):
            if k>0: poch*=(1-q**(2*k-1))*(1-q**(2*k))
            term=mp.mpf((-1)**k)*q**(k*(k-1))*mp.mpc(z)**k/poch
            t+=term
            if k>10 and abs(term)<mp.mpf(10)**-70: break
        return t
    CSl=[mp.mpf(1), ((q+1)/q)*Q**2/(Q-1)]
    for m in range(0,170):
        CSl.append((q*CSl[m]+((q+1)/q)*Q**(-m-1)*CSl[m+1])/(Q**(-m-2)*(1-Q**(-m-2))))
    def f2(z):
        hh=sum(CSl[k]*mp.mpc(z)**(-k) for k in range(len(CSl)))
        return hh/theta_Q(-mp.mpc(z)/q)
    def Cas(u,v,z): return u(z)*v(Q*z)-u(Q*z)*v(z)
    def conn(z,lam):
        F1=lambda w: f1s(w,lam)
        d=Cas(F1,f2,z)
        return Cas(G,f2,z)/d, Cas(F1,G,z)/d
    def L(f,z): return q*f(z)-(q+1-q*z)*f(Q*z)+f(Q*Q*z)
    return dict(q=q,Q=Q,G=G,f1s=f1s,f2=f2,conn=conn,L=L,theta_q=theta_q,theta_Q=theta_Q)


# ============================================================================
# THE PINNED CONNECTION (paper2 prop:pinned). Reproduces:
#  * acid tests: L f1^{[lam]} ~ 1e-61 (the resummed slope-1 solution is exact);
#  * ellipticity of C1, C2 (1e-60); C1 constant in z AND lambda (Stokes-invariant);
#  * dressing-product formula C1 = 1/[(Q;Q)inf prod z_k Q^{k-1}] (59 digits);
#  * the pinned zero condition at (q*, z*):
#        C2^{[lam]}(z*) = -C1 f1^{[lam]}(z*)/f2(z*) = 0.011592994120624266...
# Kernel normalization was validated on convergent input (34 digits, lambda-independent).
# CLOSED FORMS (v2.5.0 soundness pass; supersede the ladder): b_k = q^{k-k(k-1)/2}/(q;q)_k,
# hence by Euler Bhat(xi) = 1/(q^2/xi;q)_inf -- poles EXACTLY on xi in q^{2+N0}; the
# functional equation holds identically for the product form; singular q-Laplace classes =
# the single class [lambda] in q^Z (positive-real lattice class, near which G's zeros lie).
# CORRECTION: an earlier header claimed poles on +q^{-N} via a 0*inf fallacy at xi=1 (the
# vanishing prefactor multiplies a genuine pole of Bhat(q^2 xi)); B(-1)=(q+1)B(-q) holds.
# ============================================================================
if __name__ == "__main__":
    import mpmath as mp
    # generic q: structure checks
    S = build('0.3')
    q, Q = S['q'], S['Q']
    lam = mp.mpf('2.0')
    F = lambda w: S['f1s'](w, lam)
    print("[q=0.3] acid |L f1^[2.0]|(1.7) =", mp.nstr(abs(S['L'](F, mp.mpf('1.7'))), 4))
    C1a, C2a = S['conn'](mp.mpf('1.3'), lam)
    C1b, C2b = S['conn'](Q*mp.mpf('1.3'), lam)
    print("[q=0.3] ellipticity:", mp.nstr(abs(C1b/C1a-1), 4), mp.nstr(abs(C2b/C2a-1), 4))
    C1c, _ = S['conn'](mp.mpf('2.7'), mp.mpf('1.4'))
    print("[q=0.3] C1 lambda-invariance:", mp.nstr(abs(C1c/C1a-1), 4))
    # dressing product
    def bisect(f, a, b, iters=210):
        fa = f(a)
        for _ in range(iters):
            m = (a+b)/2; fm = f(m)
            if fa*fm <= 0: b = m
            else: a = m; fa = fm
        return (a+b)/2
    g = lambda z: S['G'](z).real
    brackets = [(mp.mpf('0.3'), mp.mpf('0.8'))] + \
        [((1/Q**k)*mp.mpf('0.85'), (1/Q**k)*mp.mpf('1.04')) for k in range(1, 10)]
    zs = [bisect(g, a, b) for a, b in brackets]
    prod = mp.mpf(1)
    for k, zk in enumerate(zs): prod *= zk*Q**k
    pinf = mp.mpf(1); x = Q
    while x > mp.mpf(10)**-58: pinf *= (1-x); x *= Q
    print("[q=0.3] dressing formula rel err:",
          mp.nstr(abs(1/(pinf*prod)-C1a.real)/abs(C1a.real), 4))
    # the beta_2 point
    S = build('0.449453630558948046125545825396')
    q, Q = S['q'], S['Q']; zstar = 2*q*(1-q); lam = mp.mpf('1.5')
    C1, _ = S['conn'](mp.mpf('1.9'), lam)
    _, C2z = S['conn'](zstar, lam)
    F = lambda w: S['f1s'](w, lam)
    print("[q=q*] C1 =", mp.nstr(C1.real, 22))
    print("[q=q*] pinned zero condition: C2(z*) =", mp.nstr(C2z.real, 22),
          " vs -C1 f1(z*)/f2(z*) =", mp.nstr((-C1*F(zstar)/S['f2'](zstar)).real, 22))


# ============================================================================
# THEOREM (paper2 thm:zeroproduct), discovered by PSLQ on the computed C1 and
# then proved by the coefficient-ratio + Hadamard-product argument:
#     C1 = 1/(q;q)_inf          (the connection constant is MODULAR), and
#     prod_{k>=1} z_k(q) Q^{k-1} = (q;q^2)_inf      (zero product of the
#     Hahn-Exton q-cosine = explicit modular product);  similarly for H:
#     prod_{k>=1} w_k(q) q Q^{k-1} = (q^3;q^2)_inf.
# Verified: C1 identity at q=0.3 (41 digits), q=0.42 (23), q=q* (26);
# zero product at q=0.3 (58 digits); the split at q*:
#     prod_{k>=2} z_k Q^{k-1} = (q;q^2)_inf / z* = 0.988299884628746...  (30 digits).
# CONSEQUENCE: the modular sector of the beta_2 problem is fully explicit; ALL
# unknown arithmetic is confined to the tail dressing product == the q-Stokes
# cocycle C2^{[lambda]}. beta_2 rational would force the modular (q;q^2)_inf to
# equal rational * tail -- unreachable without a new theorem about the tail.
# ============================================================================
def verify_zeroproduct(qs='0.3'):
    import mpmath as mp
    S = build(qs); q, Q = S['q'], S['Q']
    def poch_inf(a0, base):
        r = mp.mpf(1); x = mp.mpf(a0)
        while x > mp.mpf(10)**-58: r *= (1-x); x *= base
        return r
    def bisect(f, a, b, iters=210):
        fa = f(a)
        for _ in range(iters):
            m = (a+b)/2; fm = f(m)
            if fa*fm <= 0: b = m
            else: a = m; fa = fm
        return (a+b)/2
    g = lambda z: S['G'](z).real
    brackets = [(mp.mpf('0.2'), mp.mpf('0.9'))] + \
        [((1/Q**k)*mp.mpf('0.80'), (1/Q**k)*mp.mpf('1.05')) for k in range(1, 10)]
    zs = [bisect(g, a, b) for a, b in brackets]
    prod = mp.mpf(1)
    for k, zk in enumerate(zs): prod *= zk*Q**k
    print(f"[q={qs}] prod z_k Q^(k-1) = {mp.nstr(prod, 25)}  vs (q;q^2)inf = {mp.nstr(poch_inf(q, Q), 25)}")


# ============================================================================
# THE q-STOKES COCYCLE, EXPLICIT (paper2 rem:zeroproduct-dioph, final form):
#   C2^{[lam]}(z) = theta_Q(-z/q) * [g(z)G(Qz)+z^{-1}g(Qz)G(z)]
#                                / [-(z/q)g(z)h(Qz)+z^{-1}g(Qz)h(z)]
# (g = resummed series f1^{[lam]}/theta_Q(-z); h = f2*theta_Q(-z/q)).
# Verified vs Casoratian computation: 1e-61. DIVISOR fully described:
#  - EXPLICIT zero lattice z in q^{-1} Q^Z (theta factor) -- computed zero at
#    z = 1/q exact to 1e-63 (the "mystery zero near 3.4" was exactly 10/3);
#  - direction-dependent zero at z = lambda^2 from the RESUMMATION RESONANCE
#    g(l^2)G(Ql^2) + l^{-2} g(Ql^2) G(l^2) = 0 (1e-62) -- a structural identity
#    of theta-kernel summation at its own direction;
#  - poles at the h-bracket zeros.
# FINAL FORM OF THE OPEN PROBLEM: at z*, after cancelling the theta factor, the
# beta_2 question is ONE relation between two modular values (theta_Q(-z*),
# (q;q)_inf) and five non-modular (g,h)-orbit values. Cracking it = one of three
# research programs (non-modular Nesterenko / rho<1/2 criterion / adelic rigidity).
# ============================================================================
def verify_C2_formula(qs='0.3', lam_='2.0'):
    import mpmath as mp
    S = build(qs); q, Q = S['q'], S['Q']; lam = mp.mpf(lam_)
    th = S['theta_Q']
    gres = lambda z: S['f1s'](z, lam)/th(-mp.mpc(z))
    hser = lambda z: S['f2'](z)*th(-mp.mpc(z)/q)
    G = S['G']
    def C2f(z):
        z = mp.mpc(z)
        return th(-z/q)*(gres(z)*G(Q*z)+gres(Q*z)*G(z)/z) / \
               (-(z/q)*gres(z)*hser(Q*z)+gres(Q*z)*hser(z)/z)
    d = S['conn'](mp.mpf('1.3'), lam)[1]
    print("C2 formula vs Casoratian:", mp.nstr(abs(d-C2f(mp.mpf('1.3')))/abs(d), 4))
    print("zero at 1/q:", mp.nstr(abs(S['conn'](1/q, lam)[1]), 4),
          "| resonance at lam^2:", mp.nstr(abs(gres(lam**2)*G(Q*lam**2)+gres(Q*lam**2)*G(lam**2)/lam**2), 4))


# ============================================================================
# THE DEFORMATION MODULE (paper2 prop:deformation) -- foundation of the
# non-modular-Nesterenko program. With theta = z d/dz, delta = q d/dq (acting
# on Q=q^2 too: delta sigma = sigma delta + 2 sigma theta):
#     L(theta G) = -qz sigma G
#     L(delta G) = -qG + q(1+3z) sigma G + 4q theta G - 2a sigma theta G
# => the Q(q,z)<sigma>-module generated by {G, theta G, delta G} has rank <= 6:
# the (sigma, delta)-structure is FINITELY GENERATED. Differentiating the pinned
# zero relation along z*=2q(1-q) gives a closed quasi-linear q-system for the
# non-modular values: the PRECONDITION for a Nesterenko-type method; the missing
# half is the zero estimate for this (sigma,delta)-ring at (q*,z*). Verified 51 digits.
# ============================================================================
def verify_deformation(qs='0.31'):
    import mpmath as mp
    q = mp.mpf(qs); Q = q*q
    def qqn(n):
        p = mp.mpf(1)
        for i in range(1, n+1): p *= (1-q**i)
        return p
    gk = lambda k: mp.mpf((-1)**k)*q**(k*(k-1))/qqn(2*k)
    K = 140
    G = lambda z: sum(gk(k)*mp.mpc(z)**k for k in range(K))
    tG = lambda z: sum(k*gk(k)*mp.mpc(z)**k for k in range(K))
    def dgk(k):
        s = mp.mpf(k*(k-1))
        for i in range(1, 2*k+1): s += i*q**i/(1-q**i)
        return gk(k)*s
    dG = lambda z: sum(dgk(k)*mp.mpc(z)**k for k in range(K))
    L = lambda f, z: q*f(z)-(q+1-q*z)*f(Q*z)+f(Q*Q*z)
    z = mp.mpf('0.85'); a = q+1-q*z
    print("euler identity:", mp.nstr(abs(L(tG, z)+q*z*G(Q*z)), 4))
    print("deformation identity:",
          mp.nstr(abs(L(dG, z)-(-q*G(z)+q*(1+3*z)*G(Q*z)+4*q*tG(z)-2*a*tG(Q*z))), 4))


# ============================================================================
# CLOSED FORMS + FULL-PROOF INGREDIENTS (paper2 thm:zeroproduct, v2.5.0):
#   b_j = q^{j-j(j-1)/2}/(q;q)_j;  Bhat(xi) = 1/(q^2/xi;q)_inf;
#   DRESSED-THETA IDENTITY: (q;q)_inf G(z) = sum_m (-1)^m q^{m(m-1)} z^m P_m(1/z),
#   P_m(w) = sum_{j<=m} b_j w^j -- the rearrangement that makes the C1 proof complete.
# ============================================================================
def verify_closed_forms(qs='0.3'):
    import mpmath as mp
    q = mp.mpf(qs)
    def poch_inf(a0, base):
        r = mp.mpf(1); x = mp.mpc(a0)
        for _ in range(500):
            r *= (1-x); x *= base
            if abs(x) < mp.mpf(10)**-42: break
        return r
    # b_j closed form vs recursion
    Q = q*q
    bs = [mp.mpf(1)]
    for k in range(1, 12):
        bs.append((-(q+1)*Q*bs[k-1]-(Q**(3-k)*bs[k-2] if k >= 2 else 0))/(q*(Q**k-1)))
    den = mp.mpf(1); ok = True
    for j in range(1, 12):
        den *= (1-q**j)
        if abs(bs[j]-q**(mp.mpf(j)-mp.mpf(j)*(j-1)/2)/den) > mp.mpf(10)**-30: ok = False
    print("b_j closed form == recursion (j<=11):", ok)
    # Bhat closed form
    xi = mp.mpf('1.7')
    series = sum((q**2/xi)**k/mp.fprod([(1-q**i) for i in range(1, k+1)]) for k in range(60))
    print("Bhat(1.7): series vs 1/(q^2/xi;q)inf rel err:",
          mp.nstr(abs(series-1/poch_inf(q**2/xi, q))/abs(series), 3))
    # dressed-theta identity
    z = mp.mpf('3.7')
    def G(zv, K=200):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            term = mp.mpf((-1)**k)*q**(k*(k-1))*mp.mpc(zv)**k/poch
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-42: break
        return t
    cj = []; den = mp.mpf(1)
    for j in range(70):
        if j > 0: den *= (1-q**j)
        cj.append(q**(mp.mpf(j)-mp.mpf(j)*(j-1)/2)/den)
    rhs = sum(mp.mpf((-1)**m)*q**(m*(m-1))*mp.mpc(z)**m *
              sum(cj[j]*mp.mpc(z)**(-j) for j in range(m+1)) for m in range(70))
    lhs = poch_inf(q, q)*G(z)
    print("dressed-theta identity rel err:", mp.nstr(abs(lhs-rhs)/abs(lhs), 3))


# ============================================================================
# PROOF INGREDIENTS for L f1^{[lambda]} = 0 (paper2 prop, v2.6.0 -- now a THEOREM):
# theta shifts theta_q(q^-2 x) = q^-3 x^2 theta_q(x), theta_q(q^-4 x) = q^-10 x^4 theta_q(x)
# turn f1(Qz), f1(Q^2 z) into the same kernel sum with Bhat(lam q^{m+2}), Bhat(lam q^{m+4});
# collecting coefficients yields q[Bhat(xi)+((q+1)/xi)Bhat(q xi)+(xi^-2-1)Bhat(q^2 xi)] = 0
# identically (the proven functional equation of the product form). Casoratian covariance
# Cas(Qz) = q Cas(z) (det A = q) proves C1, C2 elliptic; the peak-window argument along every
# orbit class != [1]_Q proves C1 == 1/(q;q)_inf CONSTANT and lambda-independent.
# ============================================================================
def verify_solution_proof(qs='0.3', lam_='2.0'):
    import mpmath as mp
    q = mp.mpf(qs); Q = q*q; lam = mp.mpf(lam_)
    th = lambda x, N=80: sum(q**(mp.mpf(n)*(n-1)/2)*mp.mpc(x)**n for n in range(-N, N+1))
    def poch_inf(a0, base):
        r = mp.mpf(1); xx = mp.mpc(a0)
        for _ in range(500):
            r *= (1-xx); xx *= base
            if abs(xx) < mp.mpf(10)**-42: break
        return r
    Bh = lambda xi: 1/poch_inf(q**2/xi, q)
    def T(z, shift=0, M=45):
        num = sum(q**(mp.mpf(m)*(m-1)/2)*(lam/mp.mpc(z))**m*Bh(lam*q**(m+shift))
                  for m in range(-M, M+1))
        return num/th(lam/mp.mpc(z))
    x = mp.mpc('0.7', '0.2'); z = mp.mpf('1.9')
    print("theta shift q^-2:", mp.nstr(abs(th(x/q**2)-x**2/q**3*th(x)), 3))
    print("reindex T(Qz):", mp.nstr(abs(T(Q*z)-T(z, 2))/abs(T(Q*z)), 3))
    print("g-equation for explicit kernel sum:",
          mp.nstr(abs(q*T(z)+((q+1)/z-q)*T(Q*z)+T(Q*Q*z)/(Q*z**2)), 3))


# ============================================================================
# SYMMETRIC SQUARE (paper2 prop:sym2, v2.7.1): products of solutions satisfy
#   w(Q^3 z) = A1(A0A1-q)/A0 w(Q^2 z) + q(q-A0A1) w(Qz) + q^3 A1/A0 w(z),
# A0=a(z), A1=a(Qz); char roots at 0 = {1, q, q^2}. Verified on G^2, z^(1/2)GH,
# zH^2 (41-43 digits). Divisor-orientation lemma (paper2 lem:divisor): on orbits
# off z_a Q^Z any rational sigma-quotient r has no pole at its top zero-or-pole
# and no zero at its bottom one. [An earlier stronger "divisor localization"
# claim had a gap (mixed zeros-above-poles configurations evade both extremal
# evaluations) -- caught before shipping; only the oriented version is proven.]
# ============================================================================
def verify_sym2(qs='0.3'):
    import mpmath as mp
    S = build(qs); q, Q = S['q'], S['Q']
    G = S['G']
    def H(z, K=200):
        t = mp.mpf(0)
        for k in range(K):
            den = mp.mpf(1)
            for i in range(1, 2*k+2): den *= (1-q**i)
            term = mp.mpf((-1)**k)*q**(k*k)*(1-q)*mp.mpc(z)**k/den
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-45: break
        return t
    a = lambda z: q+1-q*z
    def resid(w, z):
        A0 = a(z); A1 = a(Q*z)
        return abs(w(Q**3*z) - (A1*(A0*A1-q)/A0*w(Q*Q*z) + q*(q-A0*A1)*w(Q*z)
                                + q**3*A1/A0*w(z)))
    z = mp.mpf('1.7')
    print("sym2 residuals:",
          mp.nstr(resid(lambda t: G(t)**2, z), 3),
          mp.nstr(resid(lambda t: mp.sqrt(mp.mpc(t))*G(t)*H(t), z), 3),
          mp.nstr(resid(lambda t: mp.mpc(t)*H(t)**2, z), 3))


# ============================================================================
# THE GALOIS PACKAGE (paper2 thm:sl2, prop:nonintegrable, cor:hypertranscendence, v2.8.0):
# (1) SL2 THEOREM: no Sym^N rank-1 submodule for any N>=1:
#     - k0 < N: the rational quotient r would have the asymptotic expansion of
#       (ghat(Qz)/ghat(z))^{N-k0}(h(Qz)/h(z))^{k0} whose j-th coefficient is
#       (N-k0) b_j Q^{-j}(1+o(1)), b_j = q^{j-j(j-1)/2}/(q;q)_j: SUPER-GEOMETRIC
#       (q^{-j^2/2}) -- rational functions have geometric expansions. Dead.
#     - k0 = N: N-th root of rational, single-valued on C* => rational => rank-2
#       Riccati solution => contradicts irreducibility (lem:irreducible).
#     N=1 reducible, N=2 dihedral, N<=12 finite-primitive (binary polyhedral
#     invariants): all excluded => G contains SL2.
# (2) NON-INTEGRABILITY: no rational B, c with theta(A) = sigma(B)A - AB + cA.
#     Elimination (central c cancels identically) => third-order inhomogeneous
#     equation for beta; no polynomial part (top-degree 1-q^{2+2m} != 0); poles
#     confined to window z_a Q^{-1..3} (extremal slots); slot sweep kills all
#     orders (two coprime kill-polynomials cover every q in (0,1)); beta == 0
#     contradicts the inhomogeneity z[(q+1)(1+q^2)-2q^3 z]. Cross-check at
#     q=1/3: rank(A)=15 < rank([A|b])=16 (exact).
# (3) => modulo the cited Hardouin-Singer / Dreyfus-Hardouin-Roques criterion:
#     G(q,.) (the Hahn-Exton q-cosine) is DIFFERENTIALLY TRANSCENDENTAL over
#     C(z) for every q in (0,1). Function-level transcendence: DONE.
# ============================================================================
def verify_galois_package():
    import sympy as sp
    q = sp.Rational(1, 3); Q = q**2; z = sp.symbols('z')
    a = lambda w: q+1-q*w
    za = (q+1)/q
    unk = []; beta = sp.Integer(0)
    for j, c in enumerate([za*Q**j for j in range(-1, 4)]):
        for i in range(1, 4):
            m = sp.symbols(f'm_{j}_{i}'); unk.append(m); beta += m/(z-c)**i
    sh = lambda e, k: e.subs(z, Q**k*z)
    b0, b1, b2, b3 = beta, sh(beta, 1), sh(beta, 2), sh(beta, 3)
    a0, a1 = a(z), a(Q*z)
    EQ = q*a0*b3 - (a1*(a0*a1-q)*b2 - a0*(a0*a1-q)*b1 + q*a1*b0 + q*z*(a1+q**2*a0))
    poly = sp.Poly(sp.expand(sp.numer(sp.together(EQ))), z)
    A, bvec = sp.linear_eq_to_matrix(poly.all_coeffs(), unk)
    print("non-integrability cross-check: rank(A) =", A.rank(),
          " rank([A|b]) =", A.row_join(bvec).rank(), " (inconsistent => no B)")
    D1 = sp.expand((q_+1)**2*(1-q_**2)*(1-q_**4)-q_) if False else None
    q_ = sp.symbols('q', positive=True)
    D1 = sp.Poly(sp.expand((q_+1)**2*(1-q_**2)*(1-q_**4)-q_), q_)
    D2 = sp.Poly(sp.expand((q_+1)**2*(1-q_**4)*(1-q_**6)-q_), q_)
    print("kill-polynomials coprime (gcd deg 0):", sp.gcd(D1, D2).degree() == 0)
