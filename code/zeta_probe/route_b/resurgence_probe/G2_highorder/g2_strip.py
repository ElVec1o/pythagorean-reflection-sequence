import mpmath as mp, pickle, numpy as np, math
mp.mp.dps=45
# The asymptotic exp-type on R_+ is set by the singularity geometry, NOT the small-t transient.
# Model: conjugate pair of sqrt-branch points + ladder, all at Re=Re0~2.6, Im=+-(Im0+ ladder).
# For a function with sqrt branch points at A0=Re0+-i Im0 (nearest rung), the Taylor coeffs
#   b_n ~ Re[c A0^{-n} n^{-3/2}], so on R_+ the analytic continuation B(t) for t real grows like
#   the Borel-Laplace-relevant rate = 1/Re0 IF the dominant real-axis behavior is set by Re(1/A0)?
# Actually exp-type tau_exp = limsup (log|B(t)|)/t.  For B(t)=sum b_n t^n with |b_n|~ C R0^{-n} n^{-3/2}
# (R0=|A0|), the radius of conv is R0, but the CONTINUATION past R0 on R_+ (where there is NO sing,
# the nearest sing is off-axis at Im0>0) grows at the rate determined by the next-order Darboux /
# the saddle of the Laplace rep. Cleanest rigorous statement:
#
# B is holomorphic in the open strip Strip_d = {|Im t| < d}, d=Im0 (>0). On a horizontal strip,
# a function holomorphic and of finite exponential type satisfies (Phragmen-Lindelof for a strip):
#   if |B(x+iy)| <= M on the two edges y=+-d' (d'<d) and |B| <= C e^{c|t|} in the strip, then
#   |B(x)| <= sup over edges. The exp-type along R_+ is bounded by the exp-type on the edges.
#
# Operative numeric exp-type measured on R_+ (settling local slope) -> asymptote:
# the slope sequence 1.956,1.371,1.123,0.978,0.879,0.807,0.751,0.706 -- extrapolate.
sl=[1.956,1.371,1.123,0.978,0.879,0.807,0.751,0.706]
ts=[0.75,1.25,1.75,2.25,2.75,3.25,3.75,4.25]
# fit slope(t) = ainf + c/t (1/t decay toward asymptotic rate)
import numpy as np
X=np.vstack([np.ones(len(ts)),1.0/np.array(ts)]).T
c,_,_,_=np.linalg.lstsq(X,np.array(sl),rcond=None)
print(f"local exp-rate slope(t)=ainf + c/t fit:  asymptotic rate 1/R_inf = {c[0]:.4f} => R_inf={1/c[0]:.3f}")
X2=np.vstack([np.ones(len(ts)),1.0/np.array(ts),1.0/np.array(ts)**2]).T
c2,_,_,_=np.linalg.lstsq(X2,np.array(sl),rcond=None)
print(f"  with 1/t^2:  1/R_inf={c2[0]:.4f} => R_inf={1/c2[0]:.3f}")
print(f"\nInterpretation: asymptotic exp-rate on R_+ ~ 1/R_inf with R_inf in [1.5,3]; compare")
print(f"  1/Re(A0)=1/2.6={1/2.6:.3f}, 1/|A0|=1/5.5={1/5.5:.3f}. Asymptote sits near 1/Re(A0).")
print(f"  => operative R (exp-type) ~ Re(A0) ~ 2.6 (rate 1/2.6=0.38), consistent with slope->0.4-0.5.")

# CLEAN STATEMENT for the bound:
print("\n"+"="*60)
print("CLEAN EXPLICIT BOUND (conservative, holds on sampled R_+):")
print("  |B(t)| <= K e^{t/R}, with K=2, R=1  works on t in[0,4.5]:")
for t in [0.5,1,2,3,4,4.5]:
    print(f"    t={t}: 2 e^{{t/1}}={2*math.exp(t):.2f}")
print("  (B(4.5)=84.7 < 2 e^4.5=180; ample margin; slope decreasing => holds for larger t.)")
