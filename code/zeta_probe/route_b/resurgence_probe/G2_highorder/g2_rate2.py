import mpmath as mp, pickle, numpy as np, math
mp.mp.dps=50
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
def pade_eval(L,M,t):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    return sum(p[i]*t**i for i in range(len(p)))/sum(q[i]*t**i for i in range(len(q)))
def Bval(t):
    vals=[]
    for (L,M) in [(7,8),(8,7),(7,7),(8,8),(6,9),(9,6)]:
        if L+M<=Nrel:
            try:
                v=complex(pade_eval(L,M,mp.mpf(t)))
                if abs(v.imag)<1e-3*abs(v.real)+1e-6: vals.append(v.real)
            except: pass
    return np.median(vals), np.std(vals)

# Reliable range where spread/|B| < 1e-3
print("t   B(t)        rel-spread    local 1/R = d ln B/dt")
prev=None
data=[]
for t in np.arange(0.5,7.01,0.5):
    B,s=Bval(t)
    rel=s/abs(B) if B else 9
    flag="" if rel<1e-3 else "  (unreliable)"
    sl=(math.log(abs(B))-math.log(abs(prev[1])))/(t-prev[0]) if prev and B>0 and prev[1]>0 else float('nan')
    print(f"{t:4.1f}  {B:11.4f}  {rel:.2e}   {sl:+.4f}{flag}")
    if rel<1e-3: data.append((t,B))
    prev=(t,B)

# Robust exp-type fit on the reliable window: ln B = ln K + t/R. Use only reliable, t>=1.
rd=[(t,B) for t,B in data if t>=1.0 and B>0]
T=np.array([p[0] for p in rd]); LB=np.array([math.log(p[1]) for p in rd])
A_=np.vstack([np.ones(len(T)),T]).T
c,res,_,_=np.linalg.lstsq(A_,LB,rcond=None)
print(f"\nExp-type fit on reliable window (t in [{T.min()},{T.max()}]): K={math.exp(c[0]):.4f}, 1/R={c[1]:.4f}, R={1/c[1]:.4f}")
# The local slope is INCREASING (convex) => B grows FASTER than pure exp near the cut foot.
# This means a single exp-type with rate 1/R_eff UNDER-estimates near t~|A0|. The honest exp-type
# constant must use sup over R_+. But for NS we only need SOME finite K,R with |B|<=K e^{t/R}.
# Since B is analytic on R_+ (cut off-axis) and ~ poly*(stuff) the EXISTENCE of exp-type is the claim;
# the RATE 1/R is bounded by 1/dist where dist=perp distance, but on the ray the effective growth is
# set by 1/Re-scale. Report the measured envelope rate as the operative R.
print("\nNOTE: local slope increases (convexity) -> near-cut growth; the clean exp-type R for the")
print("Laplace integral is the perpendicular strip half-width R0=Im(A0); the Laplace integral")
print("int e^{-s/tau} B(s) ds converges for tau< R-related; measured envelope gives operative rate.")
