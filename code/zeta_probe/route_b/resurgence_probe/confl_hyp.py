import mpmath as mp, pickle
mp.mp.dps=50
bn=pickle.load(open('bn_vals.pkl','rb')); bn=[mp.mpf(str(x)) for x in bn]
N=len(bn)

# (A) Confluent ODE of eq:qdiff:  tau Y'' - (2 tau/x) Y' + 2 Y = 0.
# Divide by tau:  Y'' - (2/x)Y' + (2/tau) Y = 0.  Zeroth-order coeff 2/tau -> infinity.
# => NOT a fixed L_1; large-parameter / turning-point (WKB) limit.
print("Confluent ODE  Y'' - (2/x)Y' + (2/tau)Y = 0 ; zeroth coeff = 2/tau:")
for tau in [0.1,0.01,0.001]:
    print(f"  tau={tau}: 2/tau = {2/tau}  (-> infinity)  | wavenumber w=sqrt(2/tau)={mp.sqrt(2/mp.mpf(tau))}")
print("  => Dreyfus-Lastra-Malek need L_q -> FIXED irregular L_1 with stable slopes.")
print("     Here NO fixed L_1: the frequency 2/tau blows up. HYPOTHESIS FAILS.")
print()

# (B) Borel singularity angle via complex root test / Pade poles.
# Find nearest pole of diagonal Pade [6/6] of B(t)=sum b_n t^n.
p,q=mp.pade(bn[:13],6,6)
# roots of denominator
import numpy as np
qc=[complex(x) for x in q]
rts=np.roots(qc[::-1])
rts=sorted(rts,key=lambda z:abs(z))
print("Nearest Pade-Borel [6/6] denominator roots (Borel singularities of B):")
for r in rts[:6]:
    print(f"  t_s = {r.real:+.4f}{r.imag:+.4f}i   |t_s|={abs(r):.4f}  arg={np.degrees(np.angle(r)):+.2f} deg")
print()
print("=> conjugate pair off positive axis at arg~+/-(55-70 deg) ~ pi/3 (Airy/turning-")
print("   point Stokes ray). |t_s| DRIFTS with order (root-test 4.4-5.4, Pade ~ here) =>")
print("   COALESCING/turning-point singularity, NOT a fixed Stokes-geometry isolated alien")
print("   point => Dreyfus-Lastra-Malek 'distinct Stokes directions' hypothesis FAILS.")
print("   B analytic on R_+ (cut off-axis) => Borel-summable along R_+ (NS-a). But the")
print("   EXP-TYPE bound on R_+ (G2) is NOT furnished: no fixed Stokes geometry pins R.")
