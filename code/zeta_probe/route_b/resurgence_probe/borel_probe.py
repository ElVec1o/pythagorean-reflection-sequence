import mpmath as mp, pickle
data = pickle.load(open('/tmp/poles_data.pkl','rb'))
ms = sorted(data.keys())
mp.mp.dps = 1500
W = {m: mp.mpf(data[m][0]) for m in ms}
dev = {m: (m+mp.mpf(1)/2)*mp.pi - W[m] for m in ms}
big = sorted(ms, reverse=True)

def fit_ck(K):
    A=mp.matrix(K,K); b=mp.matrix(K,1)
    for i,m in enumerate(big[:K]):
        b[i,0]=dev[m]
        for k in range(1,K+1): A[i,k-1]=1/W[m]**(2*k-1)
    sol=mp.lu_solve(A,b); return [sol[k,0] for k in range(K)]

# Determine how many c_k are RELIABLE: compare K=18 vs K=20 fits.
ck18=fit_ck(18); ck20=fit_ck(20); ck22=fit_ck(22)
print("k   c_k(K=20)         |c20-c22|     reliable?")
NREL=0
for k in range(1,21):
    d = abs(ck20[k-1]-ck22[k-1])
    rel = d < mp.mpf(10)**-12
    if rel: NREL=k
    print(f"{k:2d} {mp.nstr(ck20[k-1],14):>18} {mp.nstr(d,3):>12}  {rel}")
print(f"\nReliable c_1..c_{NREL}")
# use ck from a K safely above NREL
ck = ck22
import pickle as pk
pk.dump([mp.nstr(ck[k],60) for k in range(min(len(ck),NREL))], open('/tmp/ck_vals.pkl','wb'))

# a_n = c_{n+1}/2^n, n=0..NREL-1 ; g(tau)=sum a_n tau^n
NA = NREL
a = [ck[n]/mp.mpf(2)**n for n in range(NA)]
print("\n=== g coefficients a_n and Gevrey-1 check |a_n|^{1/n} ===")
for n in range(NA):
    rt = abs(a[n])**(mp.mpf(1)/n) if n>0 else mp.mpf(0)
    print(f"a_{n}={mp.nstr(a[n],12):>16}  |a_n|^(1/n)={mp.nstr(rt,8) if n>0 else '-'}")

# b_n = a_n/n!  (ordinary Borel transform coefficients)
b = [a[n]/mp.factorial(n) for n in range(NA)]
print("\n=== Borel coeffs b_n=a_n/n! and root test |b_n|^{1/n} (->1/R_Borel) ===")
for n in range(NA):
    rt = abs(b[n])**(mp.mpf(1)/n) if n>0 else mp.mpf(0)
    print(f"b_{n}={mp.nstr(b[n],10):>16}  |b_n|^(1/n)={mp.nstr(rt,8) if n>0 else '-'}")
pk.dump([mp.nstr(b[n],60) for n in range(NA)], open('/tmp/bn_vals.pkl','wb'))
pk.dump([mp.nstr(a[n],60) for n in range(NA)], open('/tmp/an_vals.pkl','wb'))
print(f"\nsaved {NA} a_n,b_n")
