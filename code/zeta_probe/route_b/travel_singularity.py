# Derive the EXPLICIT singularity equation for the travel block, mirroring the seed's
# bulk telescoping. Bulk section identity (s>=1):
#   F_s = 2q^s + 2q^s sum_{s'>=s}F_{s'}q^{s'} + 2q^{2s} sum_{s'<s}F_{s'}.
# Bulk unfolding: G_k=F(q,q^k), G_k=alpha_k(1+G_1)+gamma_k G_{k+2},
#   alpha_k=2q^{k+1}/(1-q^{k+1}), gamma_k=2q^{k+2}/(1-q^{k+2})-2q^{k+1}/(1-q^{k+1}).
#   singularity at S_1(q)=1, S_k=sum_j alpha_{k+2j} prod_{i<j} gamma_{k+2i}.
#
# TRAVEL section identity. Deposits |a|=2s+1 (s>=0), edge cost q^{(2s+1+1)/?}... let's
# REDERIVE cleanly in q=x^2. Travel edge of |a|=2s+1 costs x^{2s+1} (edge) and the site
# costs x^{max(|a|,|a'|)}. Append edge s' to edge s:
#   x^{2s'+1} * x^{2max(s,s')+1} = x^{2(s'+max(s,s')+1)} = q^{s'+max(s,s')+1}.
# weight 2 (signs). Let T_s(q) = sum over travel runs ending in half-index s of
# x^{length-to-left}. Section identity (analogous, with the +1 shift => extra q):
#   T_s = 2 q^{s+1} + 2 q^{s+1} sum_{s'>=s} T_{s'} q^{s'} + 2 q^{2s+1} sum_{s'<s} T_{s'} ,  s>=0.
# Compare bulk F_s = 2q^s + 2q^s sum_{s'>=s}F q^{s'} + 2q^{2s} sum_{s'<s}F, s>=1.
# So TRAVEL = BULK with the substitution: index s>=0 (not >=1) AND every explicit q-power
# carries one extra q (s -> with +1). Equivalently define U_s = T_s, then U satisfies the
# bulk recursion shape but evaluated with shifted indexing. 
#
# Just build the telescoping for travel directly. Define G^T_k = T(q,q^k)=sum_s T_s q^{ks}.
# Multiply section id by q^{ks} and sum over s>=0:
#   sum_s T_s q^{ks} = 2 sum_s q^{(k+1)s+1}  + 2 sum_s q^{(k+1)s+1} sum_{s'>=s}T_{s'}q^{s'}
#                      + 2 sum_s q^{(k+2)s+1} sum_{s'<s} T_{s'}.
# LHS = G^T_k. 
# term1 = 2q/(1-q^{k+1}).
# term2: 2q sum_{s'} T_{s'} q^{s'} sum_{s<=s'} q^{(k+1)s} = 2q sum_{s'} T_{s'} q^{s'} (1-q^{(k+1)(s'+1)})/(1-q^{k+1})
#       = 2q/(1-q^{k+1}) [ sum_{s'} T_{s'} q^{s'} - q^{k+1} sum_{s'} T_{s'} q^{(k+2)s'} ]
#       = 2q/(1-q^{k+1}) [ G^T_1 - q^{k+1} G^T_{k+2} ].
# term3: 2q sum_{s'} T_{s'} sum_{s>s'} q^{(k+2)s} = 2q sum_{s'} T_{s'} q^{(k+2)(s'+1)}/(1-q^{k+2})
#       = 2q^{k+3}/(1-q^{k+2}) sum_{s'} T_{s'} q^{(k+2)s'} = 2q^{k+3}/(1-q^{k+2}) G^T_{k+2}.
# So:
#   G^T_k = 2q/(1-q^{k+1}) [1 + G^T_1] + [ 2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1}) ] G^T_{k+2}.
# i.e.  G^T_k = A_k (1+G^T_1) + C_k G^T_{k+2}, with
#   A_k = 2q/(1-q^{k+1}),
#   C_k = 2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1}).
# Telescoping: G^T_k = (1+G^T_1) Sigma_k, Sigma_k = sum_{j>=0} A_{k+2j} prod_{i<j} C_{k+2i}.
# G^T_1 = Sigma_1/(1-Sigma_1); travel block GF G^T_0 = Sigma_0/(1-Sigma_1).
# SINGULARITY at Sigma_1(q)=1.
import mpmath as mp
mp.mp.dps=60
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=2000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod
        prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>30: break
    return tot
# verify G^T_0 series reproduces travel run series 2,6,10,26,54,114,274,... at q^?
def GT0(q): 
    s0=Sigma(0,q); s1=Sigma(1,q); return s0/(1-s1)
# travel run series indexed by length L=2m+? Build coeff in q: G^T_0 = sum_s T_s. 
# Numerically compare to polynomial with the known counts at lengths 1,3,5,...
# The length-to-left of a run ending at s includes that edge? Let's just match small-q.
counts=[(1,2),(3,6),(5,10),(7,26),(9,54),(11,114),(13,274),(15,582),(17,1298)]
def poly(q): return sum(c*q**((L-1)//2 + 0) for L,c in counts)  # guess exponent (L-1)/2
# Actually G^T_0 is in q with q^m; let's just expand GT0 in series via mpmath taylor
ser=mp.taylor(GT0, 0, 9)
print("G^T_0 taylor coeffs:", [mp.nstr(c,6) for c in ser])
print("travel counts:       ", [c for L,c in counts])
# solve Sigma_1=1
qstar=mp.findroot(lambda q: Sigma(1,q)-1, mp.mpf('0.4495'))
print("\nTRAVEL singularity Sigma_1(q*)=1 => q* =", mp.nstr(qstar,30))
print("beta_2_relaxed = 1/sqrt(q*) =", mp.nstr(1/mp.sqrt(qstar),20))
