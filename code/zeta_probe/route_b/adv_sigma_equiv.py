import mpmath as mp
mp.mp.dps = 50
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p

# Check: does the even-chain sum (seeded c0=1) equal Sigma_even as claimed?
# Sigma_even = sum_j (-2(1-q))^j q^{j(j+1)}/(q;q)_{2j}
# Sigma_odd  = sum_j (-2(1-q))^j q^{j(j+2)}(1-q)/(q;q)_{2j+1}
# and  c0 = -So_chain/Se_chain ... but closed form says b0=(2q/(1-q))*Sigmaodd/Sigmaeven
# So claim: -So_chain/Se_chain = (2q/(1-q)) Sigmaodd/Sigmaeven
def build_c(q,c0,c1,K=400):
    c=[mp.mpf(0)]*(K+2);c[0]=c0;c[1]=c1
    for k in range(2,K+1):
        c[k]=2*(1-q)*q*c[k-2]/((1-q**k)*(1-q**(1-k)))
    return c
for q in [mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]:
    onem=1-q
    Sig_e=mp.mpf(0);Sig_o=mp.mpf(0)
    for j in range(0,300):
        Sig_e+=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        Sig_o+=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
    # chain sums
    ce=build_c(q,mp.mpf(1),mp.mpf(0)); co=build_c(q,mp.mpf(0),-2*q/onem)
    Se_chain=sum(ce[k] for k in range(0,400,2))
    So_chain=sum(co[k] for k in range(1,400,2))
    lhs=-So_chain/Se_chain
    rhs=(2*q/onem)*Sig_o/Sig_e
    print(f"q={float(q):.2f}  -So/Se={mp.nstr(lhs,14)}  (2q/(1-q))So/Se_closed={mp.nstr(rhs,14)}  diff={mp.nstr(abs(lhs-rhs),3)}")
    print(f"       Se_chain={mp.nstr(Se_chain,12)} Sig_e={mp.nstr(Sig_e,12)}")
