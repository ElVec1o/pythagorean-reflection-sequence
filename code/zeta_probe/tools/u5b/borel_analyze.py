import json, mpmath as mp
mp.mp.dps = 50

with open('/Users/vico/Documents/elvec1o/u5b/cks.json') as f:
    cks = [mp.mpf(sp_to_float) if '/' not in sp_to_float else
           mp.mpf(int(sp_to_float.split('/')[0]))/mp.mpf(int(sp_to_float.split('/')[1]))
           for sp_to_float in json.load(f)]

K = len(cks)
print("loaded %d coeffs c_1..c_%d" % (K, K))
print()
print(" k        c_k                         |c_k|^(1/k)      |c_k|^(1/(2k-1))   ratio |c_{k}/c_{k-1}|")
prev = None
for i, c in enumerate(cks, start=1):
    ac = abs(c)
    r1 = mp.power(ac, mp.mpf(1)/i) if ac>0 else mp.mpf(0)
    r2 = mp.power(ac, mp.mpf(1)/(2*i-1)) if ac>0 else mp.mpf(0)
    rr = (ac/abs(prev)) if (prev is not None and prev!=0) else mp.mpf('nan')
    print("%2d  %s   %s   %s   %s" % (i, mp.nstr(c,12).rjust(22),
          mp.nstr(r1,8), mp.nstr(r2,8), mp.nstr(rr,8)))
    prev = c

print()
# ---- Gevrey-1 test in the w-variable: c_k ~ A * Gamma(2k-1) / S^{2k-1} * (alternating?) ----
# Then |c_k| / Gamma(2k-1) -> A * S^{-(2k-1)}, so [|c_k|/Gamma(2k-1)]^{1/(2k-1)} -> 1/S.
print("Gevrey-1-in-w test:  R_k := |c_k|/Gamma(2k-1);  R_k^{1/(2k-1)} -> 1/S")
for i, c in enumerate(cks, start=1):
    n = 2*i-1
    g = mp.gamma(n)            # (2k-2)!
    R = abs(c)/g
    inv = mp.power(R, mp.mpf(1)/n)
    print("  k=%2d  n=2k-1=%2d  |c_k|/Gamma(n)=%s   ^(1/n)=%s  -> S~%s"
          % (i, n, mp.nstr(R,8), mp.nstr(inv,10), mp.nstr(1/inv,10) if inv>0 else 'inf'))

print()
# ---- Gevrey order via ratio of successive |c_k| ----
# If c_k ~ Gamma(alpha*k + beta) C^k, then |c_{k+1}/c_k| ~ (alpha k)^alpha * C  (grows).
# log|c_{k+1}/c_k| / log k -> alpha  (the Gevrey order in the index k).
print("Gevrey order alpha:  log|c_{k+1}/c_k| vs alpha*log(k)+const")
import math
logs=[]
for i in range(1,K):
    if cks[i-1]!=0 and cks[i]!=0:
        lr = mp.log(abs(cks[i]/cks[i-1]))
        logs.append((i, lr))
for (i,lr) in logs:
    print("  k=%2d  log|c_{k+1}/c_k|=%s   /log k = %s" % (i, mp.nstr(lr,8),
          mp.nstr(lr/mp.log(i),8) if i>=2 else 'na'))
