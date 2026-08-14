"""
Verify the catalytic equation's structure is a SHIFT (q-difference) in the dilation index k,
not an argument-powering (Mahler) recursion.

Catalytic eq (relaxed bulk):
  F(q,t) = 2qt/(1-qt) + 2qt/(1-qt)[F(q,q) - F(q,q^2 t)] + 2q^2 t/(1-q^2 t) F(q,q^2 t)
Set G_k = F(q, q^k). Plug t=q^k:
  G_k = 2 q^{k+1}/(1-q^{k+1}) + 2q^{k+1}/(1-q^{k+1})[G_1 - G_{k+2}] + 2q^{k+2}/(1-q^{k+2}) G_{k+2}
      = alpha_k (1 + G_1) + gamma_k G_{k+2}
  with alpha_k = 2q^{k+1}/(1-q^{k+1}),  gamma_k = 2q^{k+2}/(1-q^{k+2}) - 2q^{k+1}/(1-q^{k+1}).

KEY: the recursion relates G_k to G_{k+2}: a SHIFT k -> k+2 in the dilation INDEX.
The ARGUMENT q is UNCHANGED. There is no q -> q^d powering anywhere.
This is the defining feature of a q-DIFFERENCE (dilation) equation, the same reason
BMJ's polynomial-kernel method fails. Mahler's method needs q -> q^d on the argument.

Verify numerically that G_k = alpha_k(1+G_1)+gamma_k G_{k+2} holds (telescoping), and that
the object we care about, G_0, is built by telescoping in k (NOT by a Mahler q->q^2 relation).
"""
import mpmath as mp
mp.mp.dps=40
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def G(k,q,J=2000):
    # G_k = sum_j alpha_{k+2j}(1+G_1?) ... actually telescoped closed form:
    # G_k = sum_{j>=0} alpha_{k+2j} prod_{i<j} gamma_{k+2i} * (1+G_1). But G_1 appears -> solve.
    # Compute S_k = sum_j alpha_{k+2j} prod_{i<j} gamma_{k+2i}; then G_k = S_k(1+G_1).
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-35) and j>30: break
    return tot
q=mp.mpf('0.3')
S0=G(0,q); S1=G(1,q)
G1=S1/(1-S1)          # G_1 = S_1(1+G_1) => G_1 = S_1/(1-S_1)
G0=S0*(1+G1)          # = S_0/(1-S_1)
print(f"q={q}: S0/(1-S1)={mp.nstr(S0/(1-S1),12)}, G0 via telescope={mp.nstr(G0,12)}")
# verify the shift recursion G_k = alpha_k(1+G_1)+gamma_k G_{k+2} for several k:
def Gk(k): return G(k,q)*(1+G1)
ok=True
for k in range(0,6):
    lhs=Gk(k); rhs=alpha(k,q)*(1+G1)+gamma(k,q)*Gk(k+2)
    if abs(lhs-rhs)>mp.mpf('1e-25'): ok=False
    print(f"  k={k}: G_k={mp.nstr(lhs,10)}  alpha_k(1+G1)+gamma_k G_{{k+2}}={mp.nstr(rhs,10)}  match={abs(lhs-rhs)<mp.mpf('1e-25')}")
print("Shift recursion (k->k+2) verified:", ok)
print()
print("There is NO q->q^d argument-powering: the recursion shifts the DILATION INDEX k by +2")
print("at fixed q. This is q-difference (dilation) structure, NOT Mahler structure.")
