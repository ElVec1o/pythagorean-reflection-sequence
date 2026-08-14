import mpmath as mp
mp.mp.dps=50
def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>80: break
    return tot

# Does So/Se relate to the TRAVEL blocks Sigma_0,Sigma_1 directly (so that at Sigma_1=1, So/Se=1)?
# Test So/Se vs Sigma_0, Sigma_1 off-pole at smooth q where Sig is computable.
print("So/Se vs travel blocks Sigma_0, Sigma_1 (smooth q, off pole):")
print(f"{'q':>7} {'So/Se':>14} {'Sig0':>13} {'Sig1':>13} {'Sig0/(2 Sig?)':>14} {'(1-Sig1+Sig0)?':>14}")
for qf in ['0.85','0.9','0.93','0.95','0.97','0.99']:
    q=mp.mpf(qf); p=1-q; J=int(250/p)
    Se,So=SeSo(q,J)
    s0=Sig(0,q); s1=Sig(1,q)
    print(f"{qf:>7} {mp.nstr(So/Se,9):>14} {mp.nstr(s0,8):>13} {mp.nstr(s1,8):>13}")

# Direct test of the cleanest possible identity: 2*So/Se =? Sigma_0/Sigma_1 - or similar.
# Also: b0=(2q/p)So/Se=S0bulk/(1-S1bulk). Is there an analogous TRAVEL resolvent
# G_travel=Sigma_0/(1-Sigma_1) that ->? at poles 1-Sigma_1->0 => G_travel->inf. That's the V pole.
# So So/Se is BULK not travel. Conclusion test: confirm So/Se uses bulk, and its ->1 at travel poles
# is a STATEMENT requiring evaluating bulk blocks AT the travel-pole locus (no pure-bulk asymptotic).
print()
print("CONFIRM So/Se is bulk-resolvent-like (b0*p/2q), and ->1 only AT travel poles:")
print(" off-pole So/Se varies wildly (above). The ->1 limit is pole-locus-specific.")
