import mpmath as mp
mp.mp.dps = 40
# The CORRECT q-Borel/Gaussian representation (from the confluence work):
#   d_k = (-2(1-q))^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k]
#   c_k = d_k / q^{k^2}   (q-Borel: strip the Gaussian q^{k^2})
#   B(xi) = sum c_k xi^k
#   Then  sum_k d_k = (1/sqrt(4 pi tau)) Integral_{-inf}^{inf} e^{-u^2/(4tau)} B(e^{-iu}) du
# because (1/sqrt(4 pi tau)) Int e^{-u^2/4tau} e^{-iku} du = e^{-tau k^2} = q^{k^2}.  EXACT, no model.
def qpoch(a,Q,n):
    p=mp.mpf(1)
    for j in range(n): p*= (1-a*Q**j)
    return p
for taus in ['0.02','0.01','0.005']:
    tau=mp.mpf(taus); q=mp.e**(-tau); Q=q*q
    def dk(k): return (-2*(1-q))**k * q**(k*k+3*k) / (qpoch(Q,Q,k)*qpoch(q**5,Q,k))
    def ck(k): return (-2*(1-q))**k * q**(3*k)     / (qpoch(Q,Q,k)*qpoch(q**5,Q,k))
    Nk=80
    d=[dk(k) for k in range(Nk)]; c=[ck(k) for k in range(Nk)]
    sum_d = sum(d)                                   # the direct (alternating) q-series
    def B(xi): return sum(c[k]*xi**k for k in range(Nk))
    pref = 1/mp.sqrt(4*mp.pi*tau)
    integ = pref*mp.quad(lambda u: mp.e**(-u*u/(4*tau))*B(mp.e**(-1j*u)), [-mp.inf,0,mp.inf])
    print(f"--- tau={taus} ---")
    print(f"  sum_k d_k  (direct q-series)      = {mp.nstr(sum_d,12)}")
    print(f"  convolution (correct kernel)      = {mp.nstr(integ,12)}")
    print(f"  match? diff = {mp.nstr(abs(sum_d-integ),4)}")
    print(f"  |sum_d|/tau^1.5 = {mp.nstr(abs(sum_d)/tau**1.5,6)}   |sum_d|/tau^2.5 = {mp.nstr(abs(sum_d)/tau**2.5,6)}")
