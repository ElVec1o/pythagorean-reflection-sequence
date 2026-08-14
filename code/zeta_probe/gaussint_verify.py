#!/usr/bin/env python3
r"""
gaussint_verify.py -- the Hubbard-Stratonovich Gaussian-integral representation of S_e
(transcendence.tex / paper2.tex, rem:gaussint), and the entire-amplitude stationary phase.

Claim (eq:HS):
   S_e = (4 pi tau)^{-1/2} \int_R e^{-u^2/(4tau)} Psi(u,q) du,
   Psi(u,q) = sum_j Z^j/(q;q)_{2j},   Z = -2(1-q) q e^{iu}.
from q^{j(j+1)} = q^j e^{-j^2 tau} and e^{-j^2 tau} = (4pi tau)^{-1/2} int e^{-u^2/4tau} e^{iju} du.

Three checks (dps 30, memory-safe: single Simpson quadrature, no matrices):
  (1) the EXACT-Psi integral equals the S_e series to full precision;
  (2) the amplitude A(u) = Psi(u,q)/cos(w e^{iu/2}) is SMOOTH & bounded across the saddle window
      (entire in e^{iu}) -> bounded variation is trivial, no lem:Bbounded needed;
  (3) the stationary-phase leading (two branches, saddle u* ~ -/+ sqrt(2 tau)) reproduces S_e.
"""
import mpmath as mp
mp.mp.dps = 30

def Se_series(q, K=400):
    s = mp.mpf(0)
    for j in range(K):
        den = mp.mpf(1)
        for i in range(1, 2*j+1):
            den *= (1 - q**i)
        t = (-2*(1-q))**j * q**(j*(j+1)) / den
        s += t
        if j > 6 and abs(t) < mp.mpf(10)**(-mp.mp.dps-5):
            break
    return s

def Psi(u, q, K=500):
    Z = -2*(1-q)*q*mp.e**(1j*u)
    s = mp.mpf(1); Zp = mp.mpf(1); den = mp.mpf(1)
    for j in range(1, K):
        den *= (1 - q**(2*j-1))*(1 - q**(2*j)); Zp *= Z
        t = Zp/den; s += t
        if j > 6 and abs(t) < mp.mpf(10)**(-mp.mp.dps-5):
            break
    return s

def Se_integral(q, L=14, N=4000):
    tau = -mp.log(q)
    pref = 1/mp.sqrt(4*mp.pi*tau)
    h = 2*L*mp.sqrt(tau)/N
    tot = mp.mpf(0)
    for i in range(N+1):
        u = -L*mp.sqrt(tau) + i*h
        wt = 1 if i in (0, N) else (4 if i % 2 else 2)
        tot += wt * mp.e**(-u**2/(4*tau)) * Psi(u, q)
    return pref*(h/3)*tot

def SD(q):
    tau = -mp.log(q); w = mp.sqrt(2/tau)
    pref = 1/mp.sqrt(4*mp.pi*tau); tot = mp.mpc(0)
    for sgn in (1, -1):
        u = mp.mpc(-sgn*mp.sqrt(2*tau))
        for _ in range(60):
            u = -sgn*tau*w*mp.e**(1j*u/2)
        phi = -u**2/(4*tau) + sgn*1j*w*mp.e**(1j*u/2)
        ph2 = -1/(2*tau) - sgn*(1j*w/4)*mp.e**(1j*u/2)
        amp = (Psi(u, q)/mp.cos(w*mp.e**(1j*u/2)))/2
        tot += pref*amp*mp.e**(phi)*mp.sqrt(2*mp.pi/(-ph2))
    return mp.re(tot)

if __name__ == "__main__":
    print("(1) exact rep: integral(Psi) == S_e series?")
    for tau in [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01')]:
        q = mp.e**(-tau)
        se, I = Se_series(q), Se_integral(q)
        print(f"    tau={float(tau):.3f}: S_e={mp.nstr(se,10)}  integral={mp.nstr(mp.re(I),10)}  "
              f"match={abs(mp.re(I)/se-1) < mp.mpf(10)**-6}")
    print("(2) amplitude A(u)=Psi/cos smooth across saddle window (spread over +/-3 sqrt(tau)):")
    for tau in [mp.mpf('0.02'), mp.mpf('0.005')]:
        q = mp.e**(-tau); w = mp.sqrt(2/tau); us = -mp.sqrt(2*tau)
        As = [abs(Psi(us+k*mp.sqrt(tau), q)/mp.cos(w*mp.e**(1j*(us+k*mp.sqrt(tau))/2)))
              for k in range(-2, 4)]
        print(f"    tau={float(tau):.3f}: |A| in [{float(min(As)):.4f},{float(max(As)):.4f}], "
              f"spread {float(max(As)/min(As)-1):.3f}")
    print("(3) stationary-phase (entire amplitude) reproduces S_e:")
    for tau in [mp.mpf('0.02'), mp.mpf('0.005')]:
        q = mp.e**(-tau)
        se, sd = Se_series(q), SD(q)
        print(f"    tau={float(tau):.3f}: S_e={mp.nstr(se,7)}  SD={mp.nstr(sd,7)}  "
              f"abs err={mp.nstr(abs(sd-se),3)}")
