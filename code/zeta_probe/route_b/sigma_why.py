import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# WHY Sigma=sum q^c L_c(1-q^c) -> 1/2 ?
# Recall S_b=(1-q)sum_{a>=b} q^a L_a. So sum_{c} q^c L_c = S_1/(1-q).
# And sum_c q^{2c} L_c = sum_c q^c (q^c L_c). Hmm.
# Sigma = sum q^c L_c - sum q^{2c}L_c = S_1/(1-q) - sum q^{2c}L_c.
# Let T = sum_{c>=1} q^{2c} L_c. Then Sigma = S_1/(1-q) - T.
# From recurrence S_{b+1}=S_b-(1-q)q^b L_b, multiply by q^b and sum?
# Better: use S_b itself. S_b = (1-q) sum_{a>=b} q^a L_a.
# Consider sum_{b>=1} S_b q^? ... Let's instead just look for the EXACT closed form of Sigma.
# Try: from L_b=L_{b-1}+2q^b(1+S_b) and the def, maybe sum_b (L_b-L_{b-1})*something.
# Empirically check candidate exact identities for Sigma.
for m in [2,4,8,16]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    S=[mp.mpf(0)]*(N+2)
    for b in range(N-1,0,-1):
        S[b]=S[b+1]-(1-q)*q**b*L[b] if False else (1-q)*sum(q**a*L[a] for a in range(b,N))
    Sig=sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    S1=S[1]
    T=sum(q**(2*c)*L[c] for c in range(1,N))
    # b0=2q/(1-q)+2q*Sig and also S1=(1-q)*sum q^a L_a = (1-q)*(Sig+T)/?
    sumqL=sum(q**c*L[c] for c in range(1,N))
    print(f'm={m}: Sig={float(Sig):.6f} S1={float(S1):.6f} (1-q)sumqL={float((1-q)*sumqL):.6f}')
    # relation b0 = L_1 + sum_{b>=2}(L_b-L_{b-1}) = L_inf. trivial.
    # Check: is Sigma = (b0 - 2q/(1-q))/(2q)? yes by construction. Want independent handle.
    # Try S1 -> ? and sumqL.
    print(f'      sum q^c L_c = {float(sumqL):.5f}, b0/(... )? b0*q/(1-q)... ')
