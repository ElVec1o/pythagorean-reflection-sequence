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
# The Borel transform's poles lie on +q^{-N} only (B regular at -1, B(-1)=(q+1)B(-q)):
# the POSITIVE axis is the q-Stokes direction -- exactly where G's zeros live.
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
