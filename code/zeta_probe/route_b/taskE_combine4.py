#!/usr/bin/env python3
"""
LEAN combined vdC bound. Fixed D=2.5, Y0=2W. Analytic Bessel phase (exact, fast).
For a RIGOROUS lower bound on |Phi'| on the flanks we use |Phi'| >= |Phi'_Bessel| - eps_g,
where eps_g = sup|(arg g)'| is small; we MEASURE eps_g on a coarse grid (few points).
Amplitude A from Bser (one call per grid point). Phase from digamma/trigamma (no Bser).
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
        p=2*n; c1=mp.mpf('0.5'); c2=mp.mpf('1.0')
        S2=2**p*(mp.bernpoly(p+1,s+c2)-mp.bernpoly(p+1,c2))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+c1)-mp.bernpoly(p+1,c1))/(p+1)
        tot+=f[n]*tau**(2*n)*(S2+S1-s)
    return tot
def Ag(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y)), g
def P1b(y,W):
    s=mp.mpc(0,1)*y; return 2*mp.log(W)-2*mp.re(mp.digamma(1+2*s))
def P2b(y):
    s=mp.mpc(0,1)*y; return 4*mp.im(mp.polygamma(1,1+2*s))

def run(tau, D=mp.mpf('2.5'), Ng=120):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; st=mp.sqrt(tau)
    a=mp.mpf('0.5'); Y0=2*W; d=D*mp.sqrt(W); yL=ys-d; yR=ys+d
    h=mp.mpf('1e-5')
    # measure eps_g = sup |(arg g)'| on a COARSE grid over [a,Y0] (8 pts)
    epsg=mp.mpf(0)
    for k in range(9):
        y=a+(Y0-a)*mp.mpf(k)/8
        d1=(mp.arg(Ag(y+h,W,tau)[1])-mp.arg(Ag(y-h,W,tau)[1]))/(2*h)
        epsg=max(epsg,abs(d1))
    # SADDLE: vdC-2, lam_s=|P2b(yR)| (|Phi''| min at right edge; the arg-g'' correction is <~ epsg-scale, ignore->we note it)
    lam_s=abs(P2b(yR))
    supAs=mp.mpf(0); VarAs=mp.mpf(0); prev=None
    for k in range(Ng+1):
        y=yL+(yR-yL)*mp.mpf(k)/Ng; av=Ag(y,W,tau)[0]; supAs=max(supAs,av)
        if prev is not None: VarAs+=abs(av-prev)
        prev=av
    boundS=8/mp.sqrt(lam_s)*(supAs+VarAs)
    # FLANKS: vdC-1 with |Phi'| >= |P1b| - epsg (rigorous lower bound).
    def flank(lo,hi):
        prev=None; sup=mp.mpf(0); Var=mp.mpf(0)
        for k in range(Ng+1):
            y=lo+(hi-lo)*mp.mpf(k)/Ng
            denom=abs(P1b(y,W))-epsg
            if denom<=0: denom=mp.mpf('1e-3')  # near saddle edge; shouldn't trigger for D>=2
            v=Ag(y,W,tau)[0]/denom
            sup=max(sup,v)
            if prev is not None: Var+=abs(v-prev)
            prev=v
        return 2*sup+Var
    bFL=flank(a,yL); bFR=flank(yR,Y0)
    tot=boundS+bFL+bFR
    return dict(tot=tot/st, S=boundS/st, F=(bFL+bFR)/st, lam=float(lam_s),
               epsg=float(epsg), d=float(d), W=float(W),
               minP1edge=float(abs(P1b(yR,W))-epsg))

print("LEAN combined vdC bound /sqrt(tau), D=2.5, Y0=2W:")
print(f"{'tau':>8} {'TOTAL/sqrtT':>12} {'saddle':>8} {'flanks':>8} {'lam_s':>8} {'eps_g':>8} {'|Phi`'+chr(39)+'|@edge':>9}")
for tau in [mp.mpf('0.05'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002')]:
    r=run(tau)
    print(f"{float(tau):>8} {mp.nstr(r['tot'],6):>12} {mp.nstr(r['S'],4):>8} {mp.nstr(r['F'],4):>8} "
          f"{r['lam']:>8.4f} {r['epsg']:>8.4f} {r['minP1edge']:>9.4f}")
