#!/usr/bin/env python3
"""
ADVERSARIAL independent verification of the |T2| = O(sqrt tau) derivation.
Everything recomputed from scratch; cross-checked against colleague's modules
only as a sanity tie-out, not as ground truth.

Definitions (from lemcos_context.md):
  tau = -ln q,  w = sqrt(2/tau),  W = w * e^{-tau/2}
  phi(y) = log( sinh(y/2)/(y/2) ) = sum_{k>=1} log(1 + (y/(2 pi k))^2)
  b(x)   = phi((2x+2)tau) + phi((2x+1)tau) - phi(tau)
  B_i    = sum_{x=0}^{i-1} b(x),   B_0 = 0
  a_i    = W^{2i}/(2i)!  > 0
  g_i    = 1 - e^{-B_i}  in [0,1)
  T2     = sum_{i>=1} (-1)^i a_i g_i

Way-1 ground truth for T2 (independent of B):
  S1_bulk(q) = sum_j alpha_{1+2j} prod_{i<j} gamma_{1+2i}
  alpha_k = 2 q^{k+1}/(1-q^{k+1}),  gamma_k = alpha_{k+1}-alpha_k
  T2 = S1_bulk - (1-cos w) - (cos w - cos W)
"""
import mpmath as mp

# ---------- phi (scalar, real or complex) ----------
def phi(y):
    y = mp.mpc(y) if isinstance(y, complex) else mp.mpf(y) if not isinstance(y,(mp.mpf,mp.mpc)) else y
    return mp.log(mp.sinh(y/2)/(y/2))

# ---------- integer B_i from b(x), product form of phi (independent of loggamma) ----------
def b_int(x, tau):
    return phi((2*x+2)*tau) + phi((2*x+1)*tau) - phi(tau)

def B_int(i, tau):
    return mp.fsum(b_int(x, tau) for x in range(i))

# ---------- Way-1 bulk S1 (ground truth, real positive q) ----------
def S1_bulk(q, J=60000):
    tot = mp.mpf(0); prod = mp.mpf(1)
    for j in range(J):
        ak = 2*q**(1+2*j+1)/(1-q**(1+2*j+1))   # alpha_{1+2j}
        tot += ak*prod
        a_next = 2*q**(1+2*j+2)/(1-q**(1+2*j+2))   # alpha_{2+2j}
        gam = a_next - ak                       # gamma_{1+2j}
        prod *= gam
        if abs(prod) < mp.mpf(10)**(-(mp.mp.dps+12)) and j > 80:
            break
    return tot

def T2_direct(tau):
    q = mp.e**(-tau)
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

# ---------- T2 from the alternating sum (uses integer B_i) ----------
def T2_altsum(tau, N=None):
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    if N is None:
        N = int(3*float(W)) + 40
    tot = mp.mpf(0)
    for i in range(1, N+1):
        Bi = B_int(i, tau)
        gi = 1 - mp.e**(-Bi)
        ai = W**(2*i)/mp.factorial(2*i)
        tot += (-1)**i * ai * gi
    return tot, N

if __name__ == "__main__":
    mp.mp.dps = 60
    print("="*80)
    print("STEP 0: tie out T2_direct (bulk) vs T2_altsum (integer B) -- ground truth")
    print("="*80)
    for tau in [mp.mpf('0.3'), mp.mpf('0.1'), mp.mpf('0.02'), mp.mpf('0.005')]:
        td = T2_direct(tau)
        ta, N = T2_altsum(tau)
        print(f"tau={float(tau):8.4f}  T2_direct={mp.nstr(td,14):>20}  "
              f"T2_altsum={mp.nstr(ta,14):>20}  |diff|={mp.nstr(abs(td-ta),3)}  N={N}")
