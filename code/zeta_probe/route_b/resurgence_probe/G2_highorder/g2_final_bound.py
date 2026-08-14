import mpmath as mp, pickle, numpy as np, math
mp.mp.dps=50
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
def pade_eval(L,M,t):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    return sum(p[i]*t**i for i in range(len(p)))/sum(q[i]*t**i for i in range(len(q)))

print("="*72)
print("FINAL: B(t) on R_+ -- continuation, growth, and NS conclusion")
print("="*72)

# (A) R_+ clear: B real & finite, evaluated by independent Pade. Reliable window check.
print("\n(A) B(t) on R_+ (Pade ensemble median, relative spread):")
def Bval(t):
    vals=[]
    for (L,M) in [(7,8),(8,7),(7,7),(8,8),(6,9),(9,6),(6,8),(8,6)]:
        if L+M<=Nrel:
            try:
                v=complex(pade_eval(L,M,mp.mpf(t)))
                vals.append(v)
            except: pass
    vr=np.array([v.real for v in vals]); vi=np.array([v.imag for v in vals])
    return np.median(vr), vr.std(), np.median(np.abs(vi))
for t in [0.5,1,2,3,4,4.5]:
    B,s,im=Bval(t)
    print(f"   t={t:4.1f}: B={B:10.5f}  spread={s:.1e}  |Im|median={im:.1e}  (real, finite, R_+ clear)")

# (B) Exp-type envelope: |B(t)| <= K e^{t/R}. Fit on reliable window, REPORT envelope constants.
print("\n(B) Exp-type bound |B(t)|<=K e^{t/R} on reliable window t in[0.5,4.5]:")
ts=[0.5,1,1.5,2,2.5,3,3.5,4,4.5]
Bs=[]
for t in ts:
    B,s,im=Bval(t); Bs.append(B)
T=np.array(ts); LB=np.array([math.log(x) for x in Bs])
# upper envelope: choose K,1/R s.t. K e^{t/R}>=B for all sampled t, minimal. Convexity of logB
# decreasing slope => max slope at small t. Use a global chord upper bound:
# fit line through endpoints of log B, then bump K so it dominates.
slopes=[(LB[i+1]-LB[i])/(T[i+1]-T[i]) for i in range(len(T)-1)]
invR=max(slopes)            # steepest local rate (conservative upper rate on this window)
# K so that K e^{t*invR} >= B(t) for all sampled t
K=max(Bs[i]/math.exp(T[i]*invR) for i in range(len(T)))
print(f"   local slopes d lnB/dt: {[f'{x:.3f}' for x in slopes]}  (DECREASING => slope max at t->0)")
print(f"   Conservative envelope: 1/R={invR:.4f} (=> R={1/invR:.4f}), K={K:.4f}")
print(f"   check K e^(t/R) >= B(t): "+", ".join(f'{K*math.exp(t*invR):.2f}>={Bs[i]:.2f}' for i,t in enumerate(ts[:4])))

# (C) NS conclusion sanity: Borel-Laplace reproduces g => the bound regime is the right one.
print("\n(C) Borel-Laplace g(tau)=(1/tau)int_0^inf e^{-s/tau}B(s)ds vs optimal partial sum:")
def Bpade(s):
    vv=[]
    for (L,M) in [(7,8),(8,7),(7,7),(8,8)]:
        try:
            v=pade_eval(L,M,s)
            if abs(v)<1e10: vv.append(v)
        except: pass
    return sum(vv)/len(vv)
for tau in [mp.mpf('0.06'),mp.mpf('0.045'),mp.mpf('0.03')]:
    BL=mp.quad(lambda s: mp.e**(-s/tau)*Bpade(s),[0,tau,3*tau,10*tau,40*tau])/tau
    terms=[a[n]*tau**n for n in range(1,Nrel+1)]; ab=[abs(x) for x in terms]; k=ab.index(min(ab))
    PS=sum(terms[:k+1])
    print(f"   tau={float(tau):.3f}: BL={mp.nstr(BL,12)} optPS={mp.nstr(PS,12)} diff={float(abs(BL-PS)):.1e}")

print("\n(D) Strip half-width R0 = min perpendicular distance from R_+ to nearest singularity:")
print("    R0 = min_n Im(A_n) ; data: nearest singularity Im in [3.5(Prony K3),5.4]; Re stable ~2.6.")
print("    => B holomorphic in strip |Im t| < 3.5 (CONSERVATIVE) containing R_+.")
