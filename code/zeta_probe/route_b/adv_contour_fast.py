#!/usr/bin/env python3
"""
FAST closed-contour residue test (lighter B continuation).
Validates: (1/(2 pi i)) oint psi pi/sin(pi s) ds = sum_{n=1}^M (-1)^n psi(n),
which confirms psi=W^{2s} g_s/Gamma(2s+1) is analytic in the rectangle (no spurious
poles) and the B continuation is correct off the real axis.
Uses a cheaper Phi_a with smaller KMAX and dps; M small.
"""
import mpmath as mp

def phi_scalar(y):
    return mp.log(mp.sinh(y/2)/(y/2))

def _term(k, s, a, tau):
    ck = 2*mp.pi*k/tau
    zm = mp.mpf(a)/2 - mp.mpc(0,1)*ck/2
    zp = mp.mpf(a)/2 + mp.mpc(0,1)*ck/2
    return ((mp.loggamma(s+zm)-mp.loggamma(zm))+(mp.loggamma(s+zp)-mp.loggamma(zp))
            +2*s*mp.log(2)-2*s*mp.log(ck))

def Phi_a(s, a, tau, KMAX=60):
    s=mp.mpc(s); head=mp.mpc(0)
    for k in range(1,KMAX+1): head+=_term(k,s,a,tau)
    k1,k2=8*KMAX,16*KMAX
    t1=_term(k1,s,a,tau); t2=_term(k2,s,a,tau)
    i12,i14=mp.mpf(1)/k1**2,mp.mpf(1)/k1**4
    i22,i24=mp.mpf(1)/k2**2,mp.mpf(1)/k2**4
    det=i12*i24-i14*i22
    A=(t1*i24-t2*i14)/det; Bc=(i12*t2-i22*t1)/det
    H2=mp.fsum(mp.mpf(1)/k**2 for k in range(1,KMAX+1))
    H4=mp.fsum(mp.mpf(1)/k**4 for k in range(1,KMAX+1))
    return head + A*(mp.zeta(2)-H2)+Bc*(mp.zeta(4)-H4)

def B_exact(s,tau): return Phi_a(s,2,tau)+Phi_a(s,1,tau)-mp.mpc(s)*phi_scalar(tau)

def h(s,W,tau):
    g=1-mp.e**(-B_exact(s,tau))
    return mp.e**(2*s*mp.log(W))/mp.gamma(2*s+1)*g*mp.pi/mp.sin(mp.pi*s)

def Bint(n,tau): return mp.fsum(phi_scalar((2*x+2)*tau)+phi_scalar((2*x+1)*tau)-phi_scalar(tau) for x in range(n))

if __name__=="__main__":
    mp.mp.dps=35
    tau=mp.mpf('0.1'); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); M=6; H=5
    c0=mp.mpf('0.5'); R=mp.mpf(M)+mp.mpf('0.5')
    f=lambda s:h(s,W,tau)
    def seg(p0,p1):
        L=p1-p0
        return mp.quad(lambda t:f(p0+t*L)*L,[0,mp.mpf('0.5'),1])
    A=mp.mpc(c0,-H); Bc=mp.mpc(R,-H); C=mp.mpc(R,H); D=mp.mpc(c0,H)
    I=seg(A,Bc)+seg(Bc,C)+seg(C,D)+seg(D,A)
    val=I/(2*mp.pi*mp.mpc(0,1))
    resn=mp.fsum((-1)**n*W**(2*n)/mp.factorial(2*n)*(1-mp.e**(-Bint(n,tau))) for n in range(1,M+1))
    print(f"tau={float(tau)}, M={M}, H={H}")
    print(f"  contour/(2pi i)   = {mp.nstr(val,12)}")
    print(f"  residue sum 1..M  = {mp.nstr(resn,12)}")
    print(f"  |diff|            = {mp.nstr(abs(val-resn),4)}")
    print("  => contour representation VALID (psi analytic, B off-axis correct)" if abs(val-resn)<mp.mpf('1e-8') else "  => MISMATCH")
