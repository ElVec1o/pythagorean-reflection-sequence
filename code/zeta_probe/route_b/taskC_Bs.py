#!/usr/bin/env python3
"""
TASK C - module: high-precision B_s for complex s, via per-k loggamma antidifference
with an analytic 1/k^2 + 1/k^4 + ... tail correction so we get dps>=50 accuracy
with a modest explicit Kmax.

phi(c) = sum_{k>=1} log(1 + (c/(2 pi k))^2)  (exact = log(sinh(c/2)/(c/2)))
B_s = sum_{x=0}^{s-1}[ phi((2x+2)tau)+phi((2x+1)tau) ] - s*phi(tau)

Per-k antidifference (analytic in s):
 T_k(s) = AD(s; a=2tau, r=2tau, L=2pi k) + AD(s; a=2tau, r=tau, L=2pi k)
 AD(s;a,r,L) = sum_{m=0}^{s-1} log(1+((a m+r)/L)^2)
             = s*log a + logGamma(s+zp)-logGamma(zp) + s*log a + logGamma(s+zm)-logGamma(zm) - 2 s log L
   zp=(r+iL)/a, zm=(r-iL)/a.

Large-k expansion: log(1+(x/L)^2) = (x/L)^2 - (x/L)^4/2 + (x/L)^6/3 - ...
 sum_{m=0}^{s-1} x^{2p} for x in {(2m+2)tau,(2m+1)tau} = tau^{2p} * P_p(s),
 P_p(s) = sum_{m=0}^{s-1} [(2m+2)^{2p}+(2m+1)^{2p}]  (Faulhaber, analytic in s via Bernoulli).
 So coefficient of 1/k^{2p} in T_k(s) is  c_p(s) = (-1)^{p+1}/p * tau^{2p} P_p(s) / (2 pi)^{2p}.
 Tail_{k>K} = sum_p c_p(s) * (zeta(2p) - H_K^{(2p)}).
"""
import mpmath as mp
mp.mp.dps = 60

def phi_real(y):
    if abs(y) < mp.mpf('1e-25'):
        return (y*y)/24
    return mp.log(mp.sinh(y/2)/(y/2))

def AD(s, a, r, L):
    zp = mp.mpc((r + 1j*L)/a)
    zm = mp.mpc((r - 1j*L)/a)
    return (s*mp.log(a) + mp.loggamma(s+zp) - mp.loggamma(zp)
            + s*mp.log(a) + mp.loggamma(s+zm) - mp.loggamma(zm)
            - 2*s*mp.log(L))

# Faulhaber: sum_{m=0}^{s-1} (2m+2)^{2p} + (2m+1)^{2p}, analytic in s.
# sum_{m=0}^{s-1} (alpha m + beta)^n = (1/(alpha(n+1)))*(B_{n+1}(alpha s + beta) - B_{n+1}(beta))
# with Bernoulli polynomial B_{n+1}. mpmath: mp.bernpoly(n, x).
def faulhaber_arith(s, alpha, beta, n):
    # sum_{m=0}^{s-1} (alpha m + beta)^n = alpha^n*(B_{n+1}(s+c)-B_{n+1}(c))/(n+1), c=beta/alpha
    c = mp.mpf(beta)/alpha
    return alpha**n*(mp.bernpoly(n+1, s + c) - mp.bernpoly(n+1, c))/(n+1)

def P_p(s, p):
    n = 2*p
    # (2m+2): alpha=2,beta=2 ; (2m+1): alpha=2,beta=1
    return faulhaber_arith(s, 2, 2, n) + faulhaber_arith(s, 2, 1, n)

def B_s(s, tau, Kmax=200, Pmax=8):
    s = mp.mpc(s)
    a = 2*tau
    # exact head sum over k=1..Kmax
    head = mp.mpc(0)
    for k in range(1, Kmax+1):
        L = 2*mp.pi*k
        head += AD(s, a, 2*tau, L) + AD(s, a, 1*tau, L)
    # analytic tail k>Kmax
    tail = mp.mpc(0)
    for p in range(1, Pmax+1):
        cp = mp.mpf((-1)**(p+1))/p * tau**(2*p) * P_p(s, p) / (2*mp.pi)**(2*p)
        # zeta(2p) - H_Kmax^{(2p)} = sum_{k>Kmax} 1/k^{2p}
        Hk = mp.zeta(2*p) - mp.zeta(2*p, Kmax+1)  # = sum_{1..Kmax} 1/k^{2p}
        tailsum = mp.zeta(2*p, Kmax+1)            # = sum_{k>Kmax} 1/k^{2p}
        tail += cp * tailsum
    return head + tail - s*phi_real(tau)

if __name__ == "__main__":
    tau = mp.mpf('0.01')
    # cross-check: integer s vs direct exact (using closed-form phi)
    def B_int_exact(S, tau):
        tot = mp.mpf(0)
        for x in range(S):
            tot += phi_real((2*x+2)*tau)+phi_real((2*x+1)*tau)-phi_real(tau)
        return tot
    print("== B_s (tail-corrected) vs exact integer sum ==")
    for S in [1,2,3,5,8,14]:
        a1 = B_s(S, tau, Kmax=200, Pmax=8)
        a2 = B_int_exact(S, tau)
        print(f"  s={S:>3}: B_s={mp.nstr(mp.re(a1),16)}  exact={mp.nstr(a2,16)}  |im|={mp.nstr(abs(mp.im(a1)),3)}  diff={mp.nstr(abs(a1-a2),3)}")

    print("\n== Convergence in Kmax for a COMPLEX s = i*7 ==")
    s = mp.mpc(0, 7)
    ref = B_s(s, tau, Kmax=4000, Pmax=10)
    for Kmax in [50,100,200,400]:
        v = B_s(s, tau, Kmax=Kmax, Pmax=8)
        print(f"  Kmax={Kmax}: B_s={mp.nstr(v,14)}  err vs ref={mp.nstr(abs(v-ref),3)}")

    print("\n== saddle value B_{iW/2} check (should be O(sqrt tau), ~ -i tau^2 W^3/72) ==")
    W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    sstar = mp.mpc(0,1)*W/2
    bval = B_s(sstar, tau, Kmax=400, Pmax=10)
    pred = -mp.mpc(0,1)*tau**2*W**3/72
    print(f"  B_{{iW/2}} = {mp.nstr(bval,12)}   leading pred -i tau^2 W^3/72 = {mp.nstr(pred,12)}")
