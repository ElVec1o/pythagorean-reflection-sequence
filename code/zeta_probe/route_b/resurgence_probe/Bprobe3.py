import mpmath as mp, pickle
mp.mp.dps = 80
bn = [mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
N = len(bn)

# Conformal map: singularities at t_s = rho e^{+-i phi}, rho~5.1, phi~57deg (avg of 47,67).
# B(t) analytic in C minus two cuts from t_s, conjugate, going outward. The cut plane that
# contains R_+ and excludes both rays: map the t-plane cut along the two rays to a unit disk.
# Simpler robust approach: estimate the cut location and use a Mobius/sqrt conformal map that
# pushes the conjugate singularities to the unit circle, re-expand, and check convergence of
# the conformal series on R_+ (=> rigorous-style bounded continuation).
# Use the standard 2-cut conformal map for a conjugate pair (Caliceti-style): 
#   w = ( sqrt(1+ t/ a) - 1 )/( sqrt(1+t/a)+1 ) won't handle complex. 
# Instead: just test EXPONENTIAL GROWTH directly. We KNOW (Prony) nearest sing dist from a
# point t0>0 on R_+ is d(t0)=|t0 - t_s|. Cauchy: |b_n| <= max_{|t|=r} |B| / r^n for r< dist to
# sing. The DEFINITIVE empirical test: form many Pade approximants [L/M] with L+M<=N-1 and check
# they AGREE on R_+ and stay bounded. Already saw [6/7] stays ~0.05 out to t=30. Let's tabulate
# the SPREAD across all valid high-order Pade as a confidence band, and fit growth rate.
def pade_eval(L,M,t):
    p,q=mp.pade(bn[:L+M+1],L,M)
    return mp.polyval(p[::-1],t)/mp.polyval(q[::-1],t)
orders=[(6,7),(7,6),(5,8),(8,5),(6,6),(5,7),(7,5),(4,8),(8,4)]
print(f"{'t':>5}  " + "  ".join(f"[{L}/{M}]" for L,M in orders))
import math
ts_list=[mp.mpf(x) for x in ['1','3','5','8','12','20','40','80','160','320']]
band={}
for t in ts_list:
    vals=[]
    for (L,M) in orders:
        try: vals.append(pade_eval(L,M,t))
        except: vals.append(mp.nan)
    band[float(t)]=vals
    print(f"{float(t):>5}  " + "  ".join(mp.nstr(v,3) for v in vals))

# robust median magnitude & check it does NOT grow exponentially
print("\nt   median|B|   ; if exp growth e^{t/R}, median|B| would blow up")
for t in ts_list:
    mags=sorted(abs(v) for v in band[float(t)] if not mp.isnan(v))
    med=mags[len(mags)//2]
    print(f"{float(t):>5}  {mp.nstr(med,6)}")
