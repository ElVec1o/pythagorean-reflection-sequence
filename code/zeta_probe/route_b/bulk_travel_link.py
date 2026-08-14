import mpmath as mp
mp.mp.dps=50
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>80: break
    return tot
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>80: break
    return tot

# Relation between travel block Sigma_k and bulk block S_k.
# A(k)=2q/(1-q^{k+1}) ; alpha(k)=2q^{k+1}/(1-q^{k+1}). Ratio A(k)/alpha(k)=q^{-k}.
# C and gamma: C(k)=2q^{k+3}/(1-q^{k+2})-2q^{k+2}/(1-q^{k+1});
#              gamma(k)=2q^{k+2}/(1-q^{k+2})-2q^{k+1}/(1-q^{k+1}). C(k)=q*gamma(k)? check:
#   q*gamma(k)=2q^{k+3}/(1-q^{k+2})-2q^{k+2}/(1-q^{k+1}) = C(k). YES exactly.
# So C(k)=q*gamma(k). And A(k)=q^{-k}*alpha(k)... A(k)=2q/(1-q^{k+1}), alpha(k)=2q^{k+1}/(1-q^{k+1}),
#   A(k)/alpha(k)=q^{1-(k+1)}=q^{-k}. So A(k)=q^{-k} alpha(k).
print("Step coefficient relations: C(k)=q*gamma(k)? A(k)=q^{-k}*alpha(k)?")
for q in [mp.mpf('0.9'),mp.mpf('0.95')]:
    for k in [0,1,2,3]:
        print(f"  q={float(q)} k={k}: C-q*gamma={float(C(k,q)-q*gamma(k,q)):.2e}  A-q^-k*alpha={float(A(k,q)-q**(-k)*alpha(k,q)):.2e}")

# Sigma_1 = sum_j A(1+2j) prod_{i<j} C(1+2i).  With C=q*gamma and A(1+2j)=q^{-(1+2j)} alpha(1+2j):
#   term_j(Sig1) = q^{-(1+2j)} alpha(1+2j) * q^{j} prod gamma  [since prod of j factors C=q^j prod gamma]
#               = q^{-(1+2j)+j} alpha(1+2j) prodgamma = q^{-1-j} alpha(1+2j) prodgamma.
# Bulk S1 term_j = alpha(1+2j) prod gamma. So Sigma_1 = sum_j q^{-1-j} * (bulk S1 term_j). NOT a clean scalar.
# Let me just verify Sigma_1 vs a weighted bulk sum numerically isn't a single multiple. Instead,
# directly TEST the conjectured pole link: at travel poles Sigma_1=1. What is (p/2q)*S0/(1-S1) bulk there?
# That's exactly So/Se. We KNOW ->1. Question: is there an identity (p/2q)S0=(1-S1) AT Sigma_1=1 exactly,
# or only asymptotically? Check residual (So-Se)=(p/2q)S0-(1-S1) and its scale vs tau at poles.
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print()
print("At travel poles: So-Se = (p/2q)S0 - (1-S1).  Is it 0 (exact identity) or O(tau)?")
print(f"{'m':>3} {'w':>9} {'So-Se':>16} {'(So-Se)/tau':>14} {'Sig1-1':>12}")
for i in [1,2,4,8,16,24,32]:
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    b1=Sb(1,q); b0=Sb(0,q); Se=1-b1; So=(p/(2*q))*b0
    s1t=Sig(1,q)
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(So-Se,8):>16} {mp.nstr((So-Se)/tau,7):>14} {mp.nstr(s1t-1,4):>12}")
