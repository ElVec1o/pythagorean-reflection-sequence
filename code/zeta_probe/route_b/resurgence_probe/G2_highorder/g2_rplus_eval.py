import mpmath as mp, pickle, numpy as np
mp.mp.dps=50
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]

# ---- Evaluate B(t) on R_+ via several near-diagonal Pade; cross-check spread ----
def pade_eval(L,M,t):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    num=sum(p[i]*t**i for i in range(len(p))); den=sum(q[i]*t**i for i in range(len(q)))
    return num/den

print("B(t) on R_+ : near-diagonal Pade ensemble  (b_0..b_%d)"%Nrel)
print(" t      mean Re(B)        std(Re)     mean Im(B)      max|B|")
PADES=[(L,M) for L in range(6,10) for M in range(6,10) if 12<=L+M<=Nrel]
for t in [0.5,1,2,3,4,5,6,8,10,12,15,20,25,30,40,50]:
    vals=[]
    for (L,M) in PADES:
        try:
            v=complex(pade_eval(L,M,mp.mpf(t)))
            if abs(v)<1e6: vals.append(v)
        except: pass
    if vals:
        vr=np.array([v.real for v in vals]); vi=np.array([v.imag for v in vals])
        print(f" t={t:5.1f}: {vr.mean():+12.5f}  {vr.std():9.2e}  {vi.mean():+12.5f}  {max(abs(np.array(vals))):.3f}")

# ---- The Laplace integral g(tau)=int_0^inf e^{-t} B(t tau)/tau dt  ... actually
# g(tau)= (1/tau) int_0^inf e^{-s/tau} B(s) ds  (standard Borel sum). Check vs true g.
# Use B via Pade along R_+. Compare with directly-summed asymptotic at moderate tau.
print("\nBorel-Laplace resum vs partial-sum of g(tau):")
def Bpade(s):
    vals=[]
    for (L,M) in [(7,8),(8,7),(7,7),(8,8),(6,8),(8,6)]:
        if L+M<=Nrel:
            try:
                v=pade_eval(L,M,s)
                if abs(v)<1e8: vals.append(v)
            except: pass
    return sum(vals)/len(vals)
for tau in [mp.mpf('0.05'),mp.mpf('0.04'),mp.mpf('0.03')]:
    # Borel-Laplace: g = (1/tau) int_0^inf e^{-s/tau} B(s) ds
    BL=mp.quad(lambda s: mp.e**(-s/tau)*Bpade(s), [0,tau,2*tau,5*tau,10*tau,30*tau])/tau
    # optimal partial sum of asymptotic series sum a_n tau^n (truncate at smallest term)
    terms=[a[n]*tau**n for n in range(1,Nrel+1)]
    abss=[abs(x) for x in terms]; kmin=abss.index(min(abss))
    PS=sum(terms[:kmin+1])
    print(f" tau={float(tau):.3f}: BorelLaplace={mp.nstr(BL,12)}  optPartialSum(N={kmin+1})={mp.nstr(PS,12)}  diff={float(abs(BL-PS)):.2e}")
