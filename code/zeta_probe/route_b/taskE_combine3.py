#!/usr/bin/env python3
"""
FAST combined vdC bound on [a, Y0=2W], split saddle window |y-y*|<=d=D sqrt(W) + flanks.
Phase derivatives: analytic Bessel part (exact digamma/trigamma) + measured (arg g)' correction.
Amplitude A from B_series.
"""
import mpmath as mp
mp.mp.dps = 45
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def Bser(s, tau, N=35):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n; c1=mp.mpf(1)/2; c2=mp.mpf(2)/2
        S2=2**p*(mp.bernpoly(p+1,s+c2)-mp.bernpoly(p+1,c2))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+c1)-mp.bernpoly(p+1,c1))/(p+1)
        Q=S2+S1-s
        tot+=f[n]*tau**(2*n)*Q
    return tot
def amp(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y)), g
def Phi1(y,W,argg_prime):  # full Phi' = Bessel + (arg g)'
    s=mp.mpc(0,1)*y
    return 2*mp.log(W)-2*mp.re(mp.digamma(1+2*s))+argg_prime
def Phi2(y):
    s=mp.mpc(0,1)*y
    return 4*mp.im(mp.polygamma(1,1+2*s))

def bound(tau, D, Ng=160):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; st=mp.sqrt(tau)
    a=mp.mpf('0.5'); Y0=2*W; d=D*mp.sqrt(W)
    yL=ys-d; yR=ys+d
    h=mp.mpf('1e-5')
    def arggp(y):
        gp=mp.arg(amp(y+h,W,tau)[1]); gm=mp.arg(amp(y-h,W,tau)[1])
        return (gp-gm)/(2*h)
    # SADDLE window: vdC-2.  lam_s = inf|Phi''| (Bessel part, monotone decreasing in y => min at yR)
    lam_s=abs(Phi2(yR))   # |Phi''| decreasing => min at right edge of window
    supAs=mp.mpf(0); VarAs=mp.mpf(0); prev=None
    for k in range(Ng+1):
        y=yL+(yR-yL)*mp.mpf(k)/Ng; av=amp(y,W,tau)[0]; supAs=max(supAs,av)
        if prev is not None: VarAs+=abs(av-prev)
        prev=av
    boundS=8/mp.sqrt(lam_s)*(supAs+VarAs)
    # FLANKS: vdC-1.  |int A e^{iPhi}|<= 2 sup|A/Phi'| + Var(A/Phi')
    def flank(lo,hi):
        prev=None; sup=mp.mpf(0); Var=mp.mpf(0)
        for k in range(Ng+1):
            y=lo+(hi-lo)*mp.mpf(k)/Ng
            v=amp(y,W,tau)[0]/abs(Phi1(y,W,arggp(y)))
            sup=max(sup,v)
            if prev is not None: Var+=abs(v-prev)
            prev=v
        return 2*sup+Var
    bFL=flank(a,yL) if yL>a else mp.mpf(0)
    bFR=flank(yR,Y0)
    tot=boundS+bFL+bFR
    return tot/st, boundS/st, (bFL+bFR)/st, float(lam_s)

print("FAST combined vdC bound /sqrt(tau).  Y0=2W, d=D sqrt(W).")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002')]:
    best=None
    for D in [mp.mpf('1.5'),mp.mpf('2.0'),mp.mpf('2.5'),mp.mpf('3.0'),mp.mpf('4.0')]:
        tot,bS,bF,lam=bound(tau,D)
        if best is None or tot<best[0]: best=(tot,bS,bF,float(D),lam)
    print(f" tau={float(tau):<7}: best total={mp.nstr(best[0],5)} sqrtT  (saddle={mp.nstr(best[1],4)}, "
          f"flanks={mp.nstr(best[2],4)})  at D={best[3]}  lam_s={best[4]:.4f}")
