"""
FAST exact rho_k(tau) = T_k/base_k tau-series via pure-Fraction truncated power series.
T_k = (-2)^k (1-q)^k q^{k^2+k} / [(q^2;q^2)_k (q^5;q^2)_k],  q=e^{-tau}.
base_k = 3(-1)^k/(k!(2k+3)!!) * tau^{-k}.
rho_k = T_k/base_k = [ (-2)^k (1-q)^k q^{k^2+k} (k!(2k+3)!!)/3 / ((-1)^k tau^{-k}) ] / [(q2;q2)_k (q5;q2)_k]
      = (2)^k (1-q)^k q^{k^2+k} tau^k (k!(2k+3)!!)/3 / [(q2;q2)_k (q5;q2)_k]
(the (-1)^k cancels (-2)^k -> 2^k).
"""
import sys
from fractions import Fraction as Fr
import math
sys.path.insert(0,'/tmp')
from ps import *

def double_fact(n):
    r=1
    while n>1:
        r*=n; n-=2
    return r

def rho_series_fast(kk, P):
    """[D_0..D_P] of rho_k for integer kk, exact Fraction."""
    Pout = P
    Pi = P + 2*kk + 2           # internal order (need headroom for tau^{2k} pole in den)
    P  = Pi
    q  = qpow(1, P)             # q=e^{-tau}
    one_minus_q = sub(const(1,P), q)
    # (1-q)^k
    omq_k = const(1,P)
    for _ in range(kk): omq_k = smul(omq_k, one_minus_q)
    # q^{k^2+k}
    qpk = qpow(kk*kk+kk, P)
    # (q^2;q^2)_k = prod_{j=0}^{k-1}(1-q^{2+2j})
    poch2 = const(1,P)
    for j in range(kk):
        poch2 = smul(poch2, sub(const(1,P), qpow(2+2*j, P)))
    # (q^5;q^2)_k = prod_{j=0}^{k-1}(1-q^{5+2j})
    poch5 = const(1,P)
    for j in range(kk):
        poch5 = smul(poch5, sub(const(1,P), qpow(5+2*j, P)))
    num = smul(omq_k, qpk)
    num = cmul(Fr(2**kk * math.factorial(kk) * double_fact(2*kk+3), 3), num)
    den = smul(poch2, poch5)
    # rho_k = tau^k * num/den.  num has tau-order k (from (1-q)^k * regular),
    # den has tau-order 2k.  So tau^k*num/den is regular (order 0).
    # Cancel: factor tau^{lnum} from num, tau^{lden} from den.
    def low(A):
        for i,c in enumerate(A):
            if c!=0: return i
        return len(A)
    lnum=low(num); lden=low(den)
    num_r = num[lnum:] + [Fr(0)]*lnum
    den_r = den[lden:] + [Fr(0)]*lden
    # rho = tau^k * (tau^{lnum} num_r)/(tau^{lden} den_r) = tau^{k+lnum-lden} num_r/den_r
    shift = kk + lnum - lden
    base = smul(num_r, inv(den_r))   # = num_r/den_r, regular
    out=[Fr(0)]*(P+1)
    for j in range(P+1):
        src=j-shift
        if 0<=src<=P: out[j]=base[src]
    return out[:Pout+1]

if __name__=="__main__":
    P=4
    for kk in range(6):
        r=rho_series_fast(kk,P)
        print(f"k={kk}:", [str(x) for x in r])
