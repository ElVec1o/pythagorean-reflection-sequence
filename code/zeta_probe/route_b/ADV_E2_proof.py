"""
Try to PROVE [E2]: P11 + P21 = 1 - Sig_t  symbolically/structurally.

P11 = X_N (top of column started (1,0)), P21 = x_N (top of column started (0,1)).
So  P11+P21 = top component a_N  of the vector (a,b) evolving from (a0,b0)=(1,1)
under  a_{n} = a_{n-1}(1+2q^{2n}) - 2 b_{n-1} q^n
       b_{n} = 2 a_{n-1} q^{3n} + b_{n-1}(1-2q^{2n}).

Sig_t(q) = sum_{j>=0} Aq(1+2j) * prod_{i<j} Cq(1+2i),  Aq(k)=2q/(1-q^{k+1}),
   Cq(k)=2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1}).

I'll test the running partial-sum identity numerically: define
   a_n, b_n  (top/bottom of the (1,1)-seeded vector)
and the partial travel sum S_n. Find the telescoping relation that makes
a_N = 1 - S_inf exactly.
"""
import mpmath as mp
mp.mp.dps = 60

def evolve11(q, N):
    a = mp.mpf(1); b = mp.mpf(1)
    qn = mp.mpf(1)
    seq_a=[a]; seq_b=[b]
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        an = a*(1+2*q2n) - 2*b*qn
        bn = 2*a*q3n + b*(1-2*q2n)
        a,b = an,bn
        seq_a.append(a); seq_b.append(b)
    return a,b,seq_a,seq_b

q = mp.mpf('0.97'); N = int(200/(1-q))
a,b,sa,sb = evolve11(q,N)
print("a_N (=P11+P21) =", mp.nstr(a,12))
print("b_N            =", mp.nstr(b,12))

# Sig_t partial sums and the prod
def Sig_t_terms(q,maxj):
    terms=[]; pr=mp.mpf(1)
    for j in range(maxj):
        k=1+2*j
        Aq = 2*q/(1-q**(k+1))
        terms.append(Aq*pr)
        Cq = 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        pr*=Cq
    return terms
T = Sig_t_terms(q, 400)
St = sum(T)
print("Sig_t          =", mp.nstr(St,12), "  1-Sig_t =", mp.nstr(1-St,12))
print("a_N - (1-Sig_t)=", mp.nstr(a-(1-St),4))

# Now hunt for the telescoping: is b_n related to the travel partial products?
# Examine ratio b_{n}/b_{n-1} vs Cq and a-increments vs Aq-terms.
print("\nStructure probe: compare b-evolution to travel C-products")
# The travel block lives on ODD indices k=1+2j -> n? Let's print first few a,b and terms.
for n in range(0,8):
    print(f"  n={n}: a={mp.nstr(sa[n],8):>14} b={mp.nstr(sb[n],8):>14}")
print("travel terms (j=0..6):", [mp.nstr(t,6) for t in T[:7]])
