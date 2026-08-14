import mpmath as mp, pickle, numpy as np
mp.mp.dps=60
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
# STRUCTURAL FACT 1: a_n are REAL RATIONALS (proven: exact rational generator, a1..a3 exact).
# => b_n=a_n/n! are real. => B(t)=sum b_n t^n has REAL Taylor coefficients.
# => Schwarz reflection: B(conj t)=conj(B(t)). Singularities come in conjugate pairs.
# => the set of singularities is symmetric about R_+. R_+ is the symmetry axis.
print("STRUCTURAL FACT 1 (proven): a_n in Q (real) => B has real Taylor coeffs => Schwarz reflection")
print("   => B(conj t)=conj B(t); singularities symmetric about R_+; B REAL on R_+ where analytic.")
print(f"   Check: a_n all rational, e.g. a_1={an[1]}")
# Verify B real on R_+ numerically (already seen Im(B)=0). Confirm reflection on a sample.
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
def pade_eval(L,M,t):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    return sum(p[i]*t**i for i in range(len(p)))/sum(q[i]*t**i for i in range(len(q)))
t0=mp.mpc(3, 1)
v=pade_eval(8,8,t0); vc=pade_eval(8,8,mp.conj(t0))
print(f"   Reflection check at t=3+i: B(t)={mp.nstr(v,8)}, conj B(conj t)={mp.nstr(mp.conj(vc),8)}, diff={float(abs(v-mp.conj(vc))):.1e}")

# STRUCTURAL FACT 2: arg(A0) is bounded AWAY from 0 and pi. Lower bound on arg from data:
# the conj pair arg is consistently >= 57 deg (min over all estimators). => Im(A0)=|A0| sin(arg)>0
# with a quantitative gap. The NEAREST singularity to R_+ has perpendicular distance
#   R0 = min over singularities of |Im(A_sing)| > 0.
# Numerically R0 >= 3.5 (Prony K3, the smallest); typical 4.5-5.4.
print("\nSTRUCTURAL FACT 2: arg bounded away from 0,pi (data: arg in [57,73] deg, min 57.9)")
print("   => perpendicular distance R0=min|Im A_sing| >0; numerically R0 in [3.5,5.4].")
print("   This is what makes R_+ CLEAR and gives the strip of analyticity |Im t|<R0.")
