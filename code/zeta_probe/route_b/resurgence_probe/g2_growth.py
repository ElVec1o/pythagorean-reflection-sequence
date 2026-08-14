import mpmath as mp, pickle
mp.mp.dps=50
bn=pickle.load(open('bn_vals.pkl','rb')); bn=[mp.mpf(str(x)) for x in bn]
N=len(bn)  # 14 coeffs

# (G2) needs:  B analytic on [0,inf) AND |B(t)|<=K e^{|t|/R} on R_+.
# B(t)=sum b_n t^n.  With only 14 coeffs, raw power series diverges past |t|~R~4.8.
# Use diagonal Pade-Borel to continue B onto R_+ and probe growth.
def pade_eval(coeffs, L, M, t):
    # build [L/M] Pade of sum coeffs[k] t^k, then eval at t
    p,q=mp.pade(coeffs[:L+M+1], L, M)
    num=sum(p[i]*t**i for i in range(len(p)))
    den=sum(q[i]*t**i for i in range(len(q)))
    return num/den

print("Pade-Borel B(t) on R_+ (diagonal [6/6] and near-diagonal):")
for t in [1,2,5,10,20,50,100,500,1000,3000]:
    vals=[]
    for (L,M) in [(6,6),(5,7),(7,5),(6,7),(7,6)]:
        if L+M<=N-1:
            try: vals.append(pade_eval(bn,L,M,mp.mpf(t)))
            except: pass
    vr=[float(v) for v in vals]
    print(f"  t={t:5d}: B~ {['%.4g'%v for v in vr]}")
print()
print("Observation: denominator-heavy Pade -> B(t) bounded/decaying (consistent with G2,")
print("  K~O(1)) BUT this is forced by rational degree (deg den>deg num => ->0).")
print("  14 coeffs CANNOT certify the true large-t growth law. Honest: numerically")
print("  consistent with G2, not a proof.")
