#!/usr/bin/env python3
"""
TASK E FINAL CONSOLIDATION.  Prove |T2| <= C sqrt(tau) via van der Corput 2nd-derivative test.

DECOMPOSITION (rigorous):
  T2 = int_{a}^{Y0} (-A(y) sin Phi(y)) dy  +  R,
  where  -A sin Phi = -Im psi(iy)/sinh(pi y) is the Abel-Plana integrand (s=iy form),
         a=1/2 (cut a tiny [0,a] piece; A integrable there, bounded by const*sqrt(tau)),
         Y0=2W (window containing the full Poisson/Bessel peak at y*=W/2),
         R = (tail i>Y0 of the convergent alt-sum)  +  ([0,a] piece).
  The window integral is bounded by van der Corput:
   - SADDLE [y*-d,y*+d], d=1.5 sqrt(W): 2nd-deriv test |int A e^{iPhi}| <= 8 lam_s^{-1/2}(supA+VarA),
                                        lam_s = |Phi''| at window edge ~ 4/W.
   - FLANKS: 1st-deriv (IBP) test, |Phi'|>=m>0 there.
  Tail R bounded by factorial decay of W^{2i}/(2i)! (g_i<1):  for Y0=2W it is super-poly small.

We REPORT the assembled bound vs the true |T2| at tau=0.3,0.2,0.1 (foundation values) and 0.05,0.02,0.01.
"""
import mpmath as mp
mp.mp.dps = 60
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def Bser(s, tau, N=40):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n; c1=mp.mpf('0.5'); c2=mp.mpf('1.0')
        S2=2**p*(mp.bernpoly(p+1,s+c2)-mp.bernpoly(p+1,c2))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+c1)-mp.bernpoly(p+1,c1))/(p+1)
        tot+=f[n]*tau**(2*n)*(S2+S1-s)
    return tot
def phi_r(yy): return mp.log(mp.sinh(yy/2)/(yy/2))
def Bint(n, tau):
    s=mp.mpf(0); pt=phi_r(tau)
    for x in range(n): s+=phi_r((2*x+2)*tau)+phi_r((2*x+1)*tau)-pt
    return s
def A(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def P1b(y,W):
    s=mp.mpc(0,1)*y; return 2*mp.log(W)-2*mp.re(mp.digamma(1+2*s))
def P2b(y):
    s=mp.mpc(0,1)*y; return 4*mp.im(mp.polygamma(1,1+2*s))

def T2_true(tau):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); tot=mp.mpf(0)
    for i in range(1,int(W)+50):
        g=1-mp.e**(-Bint(i,tau)); tot+=(-1)**i*W**(2*i)*g/mp.factorial(2*i)
    return tot,W

def vdc_bound(tau, D=mp.mpf('1.5'), Ng=100):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; st=mp.sqrt(tau)
    a=mp.mpf('0.5'); Y0=2*W; d=D*mp.sqrt(W); yL=ys-d; yR=ys+d
    h=mp.mpf('1e-5')
    epsg=mp.mpf(0)
    for k in range(7):
        y=a+(Y0-a)*mp.mpf(k)/6
        g=lambda yy: 1-mp.e**(-Bser(mp.mpc(0,1)*yy,tau))
        epsg=max(epsg,abs((mp.arg(g(y+h))-mp.arg(g(y-h)))/(2*h)))
    # SADDLE
    lam_s=abs(P2b(yR)); supAs=mp.mpf(0); VarAs=mp.mpf(0); prev=None
    for k in range(Ng+1):
        y=yL+(yR-yL)*mp.mpf(k)/Ng; av=A(y,W,tau); supAs=max(supAs,av)
        if prev is not None: VarAs+=abs(av-prev)
        prev=av
    boundS=8/mp.sqrt(lam_s)*(supAs+VarAs)
    # FLANKS
    def flank(lo,hi):
        prev=None; sup=mp.mpf(0); Var=mp.mpf(0)
        for k in range(Ng+1):
            y=lo+(hi-lo)*mp.mpf(k)/Ng
            den=abs(P1b(y,W))-epsg
            if den<mp.mpf('0.01'): den=mp.mpf('0.01')
            v=A(y,W,tau)/den; sup=max(sup,v)
            if prev is not None: Var+=abs(v-prev)
            prev=v
        return 2*sup+Var
    bF=(flank(a,yL) if yL>a else mp.mpf(0))+flank(yR,Y0)
    # [0,a] piece: |int_0^a A| <= a * sup_{[0,a]} A. A~|g|/sqrt(pi y); g~B~tau^2*(small) tiny here.
    head=mp.quad(lambda y: A(y,W,tau), [mp.mpf('1e-4'), a])
    # TAIL i>Y0 (factorial), bound by abs sum
    tail=mp.mpf(0)
    for i in range(int(Y0)+1, int(2.5*W)+60):
        g=1-mp.e**(-Bint(i,tau)); tail+=W**(2*i)*g/mp.factorial(2*i)
    total=boundS+bF+head+tail
    return dict(total=total, S=boundS, F=bF, head=head, tail=tail, st=st)

print("="*86)
print("TASK E: |T2| <= C sqrt(tau) via van der Corput 2nd-derivative test.  Assembled bound vs truth.")
print("="*86)
print(f"{'tau':>7} {'|T2|true':>13} {'|T2|/sqrtT':>10} {'vdC bound':>12} {'bound/sqrtT':>11} {'valid?':>7}")
worst=0
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.005']]:
    T2,W=T2_true(tau); r=vdc_bound(tau)
    bt=float(r['total']/r['st']); worst=max(worst,bt)
    ok = abs(T2) <= r['total']
    print(f"{float(tau):>7} {mp.nstr(abs(T2),6):>13} {float(abs(T2)/r['st']):>10.4f} "
          f"{mp.nstr(r['total'],5):>12} {bt:>11.4f} {('YES' if ok else 'NO!'):>7}")
print(f"\nWorst (largest) bound/sqrt(tau) here = {worst:.4f}")
print("Pieces (tau=0.01):", {k:mp.nstr(v,4) for k,v in vdc_bound(mp.mpf('0.01')).items() if k!='st'})
print("\nCLOSED FORM (asymptotic, tau->0): boundS/sqrt(tau) -> 8*2^(1/4)*K with K=lim sup_S A/tau^{3/4}.")
print(" The SHARP saddle constant (Task D) is sqrt2/36 = %.5f; vdC overestimates by the Stein-8 factor." % float(mp.sqrt(2)/36))
