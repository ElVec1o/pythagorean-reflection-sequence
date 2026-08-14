import mpmath as mp, pickle, numpy as np
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=40
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
print(f"B(t)=sum b_n t^n on R_+, via Pade-Borel continuation (b_0..b_{Nrel})")
# nearest sing at arg~63deg, |A|=5.657 => B analytic on R_+ (real axis clear of the cut).
# Eval B(t) on R_+ via diagonal Pade; check it stays finite & estimate growth |B(t)|<=K e^{t/R}.
def pade_eval(L,M,t):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    num=sum(p[i]*t**i for i in range(len(p))); den=sum(q[i]*t**i for i in range(len(q)))
    return num/den
print("\n t     B(t) [several near-diagonal Pade]      spread")
for t in [1,2,4,6,8,10,15,20,30,50]:
    vals=[]
    for (L,M) in [(6,6),(6,7),(7,6),(7,7),(5,7),(5,8)]:
        if L+M<=Nrel:
            try: vals.append(complex(pade_eval(L,M,mp.mpf(t))))
            except: pass
    vr=[v.real for v in vals]
    if vr:
        print(f" t={t:3d}: B~{np.mean(vr):+.5f}  spread={np.std(vr):.2e}  vals={[f'{v:.4f}' for v in vr[:3]]}")
print("\nIf B(t) bounded/slowly-growing on R_+ with small spread => analytic on R_+ (NS-a holds).")
print("|B(t)|<=K e^{|t|/R}: R = distance from R_+ to nearest sing.  Nearest sing 2.53+5.06i;")
print(f"  Re(A)=2.53 (the sing's real part); B's Taylor radius=|A|=5.657; on R_+ the relevant")
print(f"  exp-growth rate 1/R with R~Im-projected distance. Im(A)=5.06 => B grows mildly past t~Re(A).")
