import mpmath as mp
mp.mp.dps=50

# Fixed-q test: Y_3(x)=sum_k d_k x^{2k+3},
# d_k=(-2)^k (1-q)^k q^{k^2+3k}/[(q^2;q^2)_k (q^5;q^2)_k].
# This is a CONVERGENT (entire) series in x at fixed q<1 (q^{k^2} kills growth).
# The q-Gevrey structure is in the CONFLUENCE (q->1), not at fixed q.
# Confirm: at fixed q, d_k decays super-geometrically (q^{k^2}), so Y_3 entire, order 0.
def qpoch(a,q,k):
    p=mp.mpf(1)
    for i in range(k): p*= (1-a*q**i)
    return p
def dk(k,q):
    q=mp.mpf(q)
    num=(-2)**k*(1-q)**k*q**(k*k+3*k)
    den=qpoch(q**2,q**2,k)*qpoch(q**5,q**2,k)
    return num/den

for q in ['0.9','0.99','0.999']:
    qq=mp.mpf(q)
    print(f"q={q}: |d_k|^(1/k) for k=2..10:", end=" ")
    for k in [2,4,6,8,10]:
        v=abs(dk(k,qq))**(mp.mpf(1)/k)
        print(f"{float(v):.4f}", end=" ")
    print()
print()
print("=> at fixed q, |d_k|^(1/k)->0 (q^{k^2/k}=q^k->0): Y_3 ENTIRE, q-exp order 0 in x.")
print("   The q-Gevrey-1 (theta) growth lives in the CONFLUENCE series g(tau), not here.")
print()

# Now the actual (G2) object: g(tau)=sum a_n tau^n, a_n=c_{n+1}/2^n.
# Ordinary Borel B(t)=sum (a_n/n!) t^n = sum b_n t^n.
import pickle
bn=pickle.load(open('bn_vals.pkl','rb'))
an=pickle.load(open('an_vals.pkl','rb'))
bn=[mp.mpf(str(x)) for x in bn]
an=[mp.mpf(str(x)) for x in an]
N=len(bn)
print("Ordinary-Borel radius test (b_n=a_n/n!): |b_n|^(1/n):")
for n in range(2,N):
    print(f"  n={n}: |b_n|^(1/n)={float(abs(bn[n])**(mp.mpf(1)/n)):.5f}  -> R~{float(1/abs(bn[n])**(mp.mpf(1)/n)):.4f}")
