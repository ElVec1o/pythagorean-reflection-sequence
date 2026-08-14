import mpmath as mp, pickle
data = pickle.load(open('/tmp/poles_data.pkl','rb'))
ms = sorted(data.keys())
# load w at full precision
WPREC = 1500
mp.mp.dps = WPREC
W = {}
for m in ms:
    wstr, dps = data[m]
    W[m] = mp.mpf(wstr)
# dev_m = (m+1/2)pi - w_m
dev = {m: (m+mp.mpf(1)/2)*mp.pi - W[m] for m in ms}
# Fit dev_m = sum_{k=1}^{K} c_k / w_m^{2k-1}  using the largest-m poles (most accurate asymptotics)
# Solve linear least-squares / exact solve with K unknowns from K poles (use top K).
def fit_ck(K, use_ms):
    A = mp.matrix(K,K); b = mp.matrix(K,1)
    for i,m in enumerate(use_ms[:K]):
        b[i,0] = dev[m]
        for k in range(1,K+1):
            A[i,k-1] = 1/W[m]**(2*k-1)
    sol = mp.lu_solve(A,b)
    return [sol[k,0] for k in range(K)]

# use the K LARGEST m poles
big = sorted(ms, reverse=True)
published = {1: mp.mpf(1)/18, 2: -mp.mpf(41)/600, 3: -mp.mpf(1915)/7056, 4: -mp.mpf(18617)/51840}
print("=== exact-solve fit using K largest poles ===")
for K in [6,8,10,12]:
    ck = fit_ck(K, big)
    print(f"K={K}:")
    for k in range(1,min(K,6)+1):
        c=ck[k-1]
        extra=""
        if k in published:
            extra=f"  published={mp.nstr(published[k],14)} diff={mp.nstr(abs(c-published[k]),3)}"
        print(f"  c_{k}={mp.nstr(c,16)}{extra}")
