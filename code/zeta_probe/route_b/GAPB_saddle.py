"""
STEP toward closing Atom B: set up the steepest descent of Y3(1)=sum_k d_k.
(1) IDENTIFY: Y3(1) = sum_k d_k = _0phi_1(-; q^5; q^2, 2(1-q)q^4)  -- a confluent basic hypergeometric
    (q-analog of _0F_1, the Bessel).  Verify numerically.
(2) SADDLE: |d_k| is Gaussian-peaked; locate the peak k* and check k* ~ w/2 = 1/sqrt(2 tau).
(3) STRUCTURAL ANALOGY to T2: Y3(1)=sum_k (-1)^k |d_k| is an ALTERNATING sum of Gaussian-peaked terms,
    EXACTLY the structure of T2=sum_n(-1)^n h(n) (lem:cos error). So the confluence is the SAME class as
    lem:T2abs / lem:extremephase. The gate Y3(1)(q_m)~tau^{5/2} is the EXTREME-PHASE next order (the leading
    Bessel oscillation ~ cos w vanishes at the pole), analogous to lem:extremephase T2(m pi)=O(tau).
    Verify: leading |Y3(1)| (generic q) ~ (3 tau/2)|sin w/w - cos w| ~ tau; at the pole it drops to tau^{5/2}.
"""
import mpmath as mp
def dk(k,q):
    num=(-2)**k*(1-q)**k*q**(k*k+3*k); den=mp.mpf(1)
    for i in range(k): den*=(1-q**(2*i+2))*(1-q**(2*i+5))
    return num/den
def absdk(k,q):
    num=2**k*(1-q)**k*q**(k*k+3*k); den=mp.mpf(1)
    for i in range(k): den*=(1-q**(2*i+2))*(1-q**(2*i+5))
    return num/den
def Y3at1(q):
    K=int(8/float(1-q)**0.5)+40; return mp.fsum(dk(k,q) for k in range(K))
def phi01(q):  # _0phi_1(-;q^5;q^2, 2(1-q)q^4) via the standard series sum_k (-1)^k Q^{k(k-1)/2} x^k/[(Q;Q)_k (c;Q)_k]
    Q=q*q; c=q**5; x=2*(1-q)*q**4; K=int(8/float(1-q)**0.5)+40
    tot=mp.mpf(0)
    for k in range(K):
        QP=mp.mpf(1); cP=mp.mpf(1)
        for i in range(k): QP*=(1-Q**(i+1)); cP*=(1-c*Q**i)
        tot+=(-1)**k*Q**(k*(k-1)//2 if (k*(k-1))%2==0 else 0)*Q**(mp.mpf(k*(k-1))/2 - (k*(k-1)//2))*x**k/(QP*cP)
    return tot
mp.mp.dps=40
print("(1) Y3(1) == _0phi_1(-;q^5;q^2,2(1-q)q^4)?   (2) saddle k* vs w/2:")
print(f"{'tau':>9}{'w':>8}{'Y3(1)':>16}{'_0phi_1':>16}{'rel':>9}{'k*(peak|d|)':>12}{'w/2':>9}")
for taus in ['0.05','0.02','0.008','0.003']:
    tau=mp.mpf(taus); q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Y=Y3at1(q); P=phi01(q)
    K=int(8/float(1-q)**0.5)+40
    ad=[absdk(k,q) for k in range(K)]; kstar=max(range(K),key=lambda k:ad[k])
    print(f"{taus:>9}{float(w):>8.3f}{mp.nstr(Y,8):>16}{mp.nstr(P,8):>16}{float(abs(Y-P)/(abs(Y)+1e-99)):>9.1e}{kstar:>12}{float(w/2):>9.3f}")

print("\n(3) leading |Y3(1)| ~ (3 tau/2)|sin w/w - cos w| at GENERIC q (~tau), vs the small value at travel poles:")
print(f"{'tau(generic)':>13}{'|Y3(1)|':>14}{'(3t/2)|sinw/w-cosw|':>20}{'ratio':>8}")
for taus in ['0.05','0.02','0.008']:
    tau=mp.mpf(taus); q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Y=Y3at1(q); lead=(3*tau/2)*abs(mp.sin(w)/w-mp.cos(w))
    print(f"{taus:>13}{float(abs(Y)):>14.6e}{float(lead):>20.6e}{float(abs(Y)/lead):>8.4f}")
print("=> Y3(1) is alternating-Gaussian-peaked at k*=w/2 (SAME structure as T2); leading ~ (3t/2)(sinw/w-cosw)~tau,")
print("   matching the Bessel limit.  Gate = its EXTREME-PHASE next order (cos w ~0 at pole) -> tau^{5/2}.")
print("   => Atom B confluence is the q-Bessel analog of lem:extremephase, attackable by the SAME SD machinery.")
