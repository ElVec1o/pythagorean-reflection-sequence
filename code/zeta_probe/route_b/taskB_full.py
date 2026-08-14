#!/usr/bin/env python3
"""
TASK B -- verify stationary-phase INGREDIENTS at tau in {0.02,0.005,0.001}.

B_s computed by the tau-series in the HURWITZ-ZETA (analytic in complex s) form,
validated at integer s against the first-principles form factor (buildR).
This series converges for |s| < pi/tau; the saddle s*=iW/2 has |s*|=W/2 << pi/tau.

Phi'(y) computed by central finite differences of the phase of psi(iy) (per task).
psi(s) = W^{2s} g_s / Gamma(2s+1),  g_s = 1 - e^{-B_s}.
"""
import mpmath as mp, sympy as sp
mp.mp.dps = 60

# ---- f_n = [y^{2n}] phi(y),  phi=log(sinh(y/2)/(y/2)) ----
def build_fcoeffs(Nmax=60):
    yv = sp.symbols('y')
    ser = sp.series(sp.log(sp.sinh(yv/2)/(yv/2)), yv, 0, 2*Nmax+2).removeO()
    poly = sp.Poly(ser, yv)
    fdict = {}
    for (m,), c in poly.terms():
        fdict[int(m)] = mp.mpf(str(sp.Float(c, 70)))
    return fdict
FCO = build_fcoeffs(60)

def Bs(s, tau, Nmax=60):
    """B_s = sum_{n>=1} f_n tau^{2n} Q_n(s-1),  analytic in complex s via Hurwitz zeta.
       Q_n(m)=sum_{i=0}^m[(2i+2)^{2n}+(2i+1)^{2n}-1].  m=s-1."""
    s = mp.mpc(s); m = s - 1
    tot = mp.mpc(0)
    for n in range(1, Nmax+1):
        fn = FCO.get(2*n, None)
        if fn is None or fn == 0:
            continue
        def powsum(c):  # sum_{i=0}^m (2i+c)^{2n} = 2^{2n}(zeta(-2n,c/2)-zeta(-2n,m+1+c/2))
            return (mp.mpf(2)**(2*n))*(mp.zeta(-2*n, mp.mpf(c)/2) - mp.zeta(-2*n, m+1+mp.mpf(c)/2))
        Qn = powsum(2) + powsum(1) - (m+1)
        term = fn * mp.mpf(tau)**(2*n) * Qn
        tot += term
        if n > 6 and abs(term) < mp.mpf(10)**(-55)*(1+abs(tot)):
            break
    return tot

def gs(s, tau):
    return 1 - mp.e**(-Bs(s, tau))

def psi(s, tau, W):
    # psi(s)=W^{2s} g_s / Gamma(2s+1)
    return W**(2*s) * gs(s, tau) / mp.gamma(2*s+1)

# ---- first-principles B at integers (cross-check reference) ----
def alpha_t(k, t): return 2/(mp.e**((k+1)*t)-1)
def buildR(t, J):
    rho = []; prod = mp.mpf(1); out = []
    for jj in range(J):
        a1 = alpha_t(1+2*jj, t); that = (2/t)**(jj+1)/mp.factorial(2*jj+2)
        rho.append(a1*prod/that); prod *= (a1-alpha_t(2+2*jj, t))
        out.append(-mp.log(rho[jj])-(jj+1)*t)
    return out

# ---- bulk S1 (true) for T2_direct ----
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb1(q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-120) and j>50: break
    return tot

# ---- phase of psi(iy) and Phi via finite difference ----
def arg_psi_iy(y, tau, W):
    # psi(iy) = W^{2iy} g_{iy}/Gamma(1+2iy);  return its complex value
    return psi(mp.mpc(0,1)*y, tau, W)

def Phi_phase(y, tau, W):
    # Phi(y)=2y log W + arg(g_{iy}) - arg Gamma(1+2iy)  (continuous-ish; we use the actual arg of psi(iy))
    # arg psi(iy) = Im(2iy log W) + arg g_{iy} - arg Gamma(1+2iy) = 2y log W + arg g - arg Gamma  (W>0 real)
    val = psi(mp.mpc(0,1)*y, tau, W)
    return mp.arg(val)

def Phi_explicit(y, tau, W):
    g = gs(mp.mpc(0,1)*y, tau)
    return 2*y*mp.log(W) + mp.arg(g) - mp.arg(mp.gamma(1+mp.mpc(0,1)*2*y))

def Phiprime_fd(y, tau, W, h):
    # central finite diff of Phi_explicit (smooth, avoids 2pi jumps of mp.arg over wide ranges)
    return (Phi_explicit(y+h,tau,W) - Phi_explicit(y-h,tau,W))/(2*h)

def Phidoubleprime_fd(y, tau, W, h):
    return (Phi_explicit(y+h,tau,W) - 2*Phi_explicit(y,tau,W) + Phi_explicit(y-h,tau,W))/(h*h)

def amplitude(y, tau, W):
    g = gs(mp.mpc(0,1)*y, tau)
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

# =====================================================================
print("="*92)
print("SANITY: Bs (tau-series Hurwitz form) vs first-principles form factor at integer s")
print("="*92)
for tau in [mp.mpf('0.02'),mp.mpf('0.005'),mp.mpf('0.001')]:
    R=buildR(tau,5)
    errs=[abs(Bs(si,tau).real-R[si-1]) for si in range(1,5)]
    print(f"tau={mp.nstr(tau,4)}: max|Bs-formfac| over s=1..4 = {mp.nstr(max(errs),4)}")

results={}
for tau in [mp.mpf('0.02'),mp.mpf('0.005'),mp.mpf('0.001')]:
    print("\n"+"="*92)
    print(f"TAU = {mp.nstr(tau,6)}")
    print("="*92)
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    print(f"  q={mp.nstr(q,10)}  w={mp.nstr(w,10)}  W={mp.nstr(W,10)}")

    # ---- (1) stationary point: solve Phi'(y)=0 ----
    h=mp.mpf(10)**(-12)
    f=lambda y: Phiprime_fd(y,tau,W,h)
    ystar=mp.findroot(f, W/2)
    print(f"\n(1) STATIONARY POINT  Phi'(y)=0")
    print(f"    y_star (solved)   = {mp.nstr(ystar,12)}")
    print(f"    W/2 (predicted)   = {mp.nstr(W/2,12)}")
    print(f"    ratio y*/(W/2)    = {mp.nstr(ystar/(W/2),10)}    |y*-W/2|={mp.nstr(abs(ystar-W/2),4)}")
    check1 = abs(ystar/(W/2)-1) < mp.mpf('1e-3')

    # ---- (2) Phi''(y*) ~ -4/W ----
    hh=mp.mpf(10)**(-8)
    Phi2=Phidoubleprime_fd(ystar,tau,W,hh)
    Phi2_pred=-4/W
    print(f"\n(2) SECOND DERIVATIVE  Phi''(y*)")
    print(f"    Phi''(y*) (numeric) = {mp.nstr(Phi2,12)}")
    print(f"    -4/W (predicted)    = {mp.nstr(Phi2_pred,12)}")
    print(f"    ratio               = {mp.nstr(Phi2/Phi2_pred,10)}")
    check2 = abs(Phi2/Phi2_pred-1) < mp.mpf('5e-2')

    # ---- (3) amplitude * sqrt(2pi/|Phi''|) = O(sqrt tau) ~ |g_{iW/2}| ----
    A_ystar=amplitude(ystar,tau,W)
    spfac=mp.sqrt(2*mp.pi/abs(Phi2))
    SPA = A_ystar*spfac
    g_at_sstar = gs(mp.mpc(0,1)*W/2, tau)
    print(f"\n(3) AMPLITUDE SCALING")
    print(f"    A(y*)               = {mp.nstr(A_ystar,10)}")
    print(f"    sqrt(2pi/|Phi''|)   = {mp.nstr(spfac,10)}")
    print(f"    A(y*)*sqrt(2pi/|..|)= {mp.nstr(SPA,10)}")
    print(f"    |g_{{iW/2}}|          = {mp.nstr(abs(g_at_sstar),10)}")
    print(f"    sqrt(tau)           = {mp.nstr(mp.sqrt(tau),10)}")
    print(f"    SPA/|g_iW/2|        = {mp.nstr(SPA/abs(g_at_sstar),8)}   SPA/sqrt(tau)={mp.nstr(SPA/mp.sqrt(tau),8)}")
    check3 = abs(SPA/abs(g_at_sstar)-1) < mp.mpf('1e-1')

    # ---- (4) full leading prediction ----
    # T2_direct
    S1=Sb1(q); T1=mp.cos(w)-mp.cos(W); T2_direct=S1-(1-mp.cos(w))-T1
    # stationary-phase: integrand = -A sin Phi;  T2 = int -A(y) sin Phi(y) dy
    # leading SP value (for a single saddle, Phi''<0):
    #   int A(y)(-sin Phi) dy ~ -A(y*) sqrt(2pi/|Phi''|) sin(Phi(y*) - pi/4)
    Phi_at=Phi_explicit(ystar,tau,W)
    SP_pred = -A_ystar*spfac*mp.sin(Phi_at - mp.pi/4)
    # closed form Re[g_{s*} e^{iW}]
    sstar=mp.mpc(0,1)*W/2
    closed = mp.re(gs(sstar,tau)*mp.e**(mp.mpc(0,1)*W))
    print(f"\n(4) FULL LEADING PREDICTION")
    print(f"    T2_direct (S1-...)         = {mp.nstr(T2_direct,12)}")
    print(f"    SP: -A sqrt(2pi/|Phi''|) sin(Phi-pi/4) = {mp.nstr(SP_pred,12)}")
    print(f"    Re[g_s* e^iW] (closed)     = {mp.nstr(closed,12)}")
    print(f"    ratio SP/T2_direct         = {mp.nstr(SP_pred/T2_direct,8)}")
    print(f"    ratio closed/T2_direct     = {mp.nstr(closed/T2_direct,8)}")
    print(f"    ratio SP/closed            = {mp.nstr(SP_pred/closed,8)}")
    print(f"    Phi(y*)                    = {mp.nstr(Phi_at,10)}")
    print(f"    Phi(y*)-pi/4 vs W          : Phi-pi/4={mp.nstr(Phi_at-mp.pi/4,8)}  W={mp.nstr(W,8)}  W mod 2pi={mp.nstr(mp.fmod(W,2*mp.pi),8)}")
    check4a = abs(SP_pred/T2_direct-1) < mp.mpf('1.5e-1')
    check4b = abs(closed/T2_direct-1) < mp.mpf('1.5e-1')

    results[str(tau)]=dict(check1=check1,check2=check2,check3=check3,check4a=check4a,check4b=check4b,
                           ystar=ystar,Whalf=W/2,Phi2=Phi2,SPA=SPA,g=abs(g_at_sstar),
                           T2=T2_direct,SP=SP_pred,closed=closed)

print("\n"+"="*92)
print("SUMMARY of checks")
print("="*92)
for tau,r in results.items():
    print(f"tau={tau}: (1)y*={r['check1']} (2)Phi''={r['check2']} (3)ampl={r['check3']} (4a)SP={r['check4a']} (4b)closed={r['check4b']}")
