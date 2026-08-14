import mpmath as mp, pickle
mp.mp.dps=60
bn=[mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
N=len(bn)
# Prony with varying order to see if the off-axis singularity is STABLE (single branch pt =>
# resurgent-friendly) or DRIFTS/accumulates (=> not a clean alien singularity).
def prony(seq, M, n0):
    rows=len(seq)-M-n0
    A=mp.matrix(rows,M); rhs=mp.matrix(rows,1)
    for i in range(rows):
        n=n0+M+i; rhs[i,0]=seq[n]
        for j in range(M): A[i,j]=seq[n-1-j]
    coef=mp.lu_solve(A.T*A,A.T*rhs)
    poly=[mp.mpf(1)]+[-coef[j,0] for j in range(M)]
    return mp.polyroots(poly,maxsteps=300,extraprec=300)
print("Stability of dominant off-axis B-singularity t_s=1/z under Prony order M:")
print(f"{'M':>3} {'n0':>3}  dominant |t_s|   arg(deg)")
for M in [3,4,5]:
    for n0 in [0,1,2]:
        if len(bn)-M-n0 < M+1: continue
        try: rts=prony(bn,M,n0)
        except: continue
        # dominant = smallest |z| with nonzero, complex (the conj pair); pick min |1/z| among complex
        cand=[1/z for z in rts if abs(z)>1e-9 and abs(mp.im(z))>1e-6]
        if not cand: continue
        ts=min(cand,key=lambda t:abs(t))
        print(f"{M:>3} {n0:>3}  {mp.nstr(abs(ts),8):>12}   {mp.nstr(mp.arg(ts)*180/mp.pi,6)}")
print()
print("If |t_s| DRIFTS upward with M and arg fans -> branch CUT (turning-point), not a single")
print("isolated alien point => Ecalle 'simple resurgence' (isolated sings) NOT directly applicable.")
