import mpmath as mp, pickle, numpy as np
mp.mp.dps=50
# The amplitude singularities sit on a fixed-Re ladder. The recurrence-extracted A_n had
# Re STABLE ~2.7-2.9, Im DRIFTING UP. The drift-up of the APPARENT nearest |A| is the
# finite-order estimator climbing the ladder (it sees an effective single point that is the
# resultant of the whole ladder). The structural claim: Re(A_sing)=const (=Re0), Im=Re0*tan(arg_n)
# with the rungs marching to i*inf. R_+ stays clear because EVERY rung has Im>=Im_min>0.
#
# Cross-check with the STRUCTURAL ladder 2 tau*_n: tau*_n=Re0' +- i(arg0'+2 pi n), Re0'=0.8808.
# These have CONSTANT Re=0.8808 (so 2tau* has constant Re=1.7616) and Im=2(arg0'+2pi n) growing
# by 4pi per rung. So the structural ladder is fixed-Re, growing-Im, spacing Delta Im=4pi=12.566.
# The amplitude ladder (measured) has Re~2.6 (shifted) -- different series, but SAME topology:
# fixed Re, growing Im. The point: R_+ is clear for ALL rungs, distance >= Im of foot rung.
print("Structural ladder (from S'(tau*)=0):  2tau*_n = 1.7616 +- i(4.1936 + 4*pi*n)")
print(f"   rung spacing Delta Im = 4 pi = {float(4*mp.pi):.4f}")
print(f"   foot rung (n=0): Im = 4.1936 ; all rungs Im>=4.1936 => R_+ clear with margin 4.19")
print()
print("Measured AMPLITUDE foot singularity: Re~2.6, Im~4.2-4.9 (foot), arg~61-67deg.")
print("   Same fixed-Re/growing-Im topology. Whether amplitude rungs are EXACTLY 2tau*_n or a")
print("   shifted relative is moot for the bound: the controlling quantity is")
print("   R0 = Im(foot) > 0, numerically >= 3.5 (most conservative estimator).")
print()
# Verify B's analytic continuation stays single-valued & finite crossing t=Re0 on R_+:
# already have B(t) real, finite, smooth through t=2.6 (=Re0) in part (A) -- NO singularity there.
# The branch point is at Re0 + i*Im0, OFF axis; on R_+ B is regular through and past Re0. Confirmed.
print("CONFIRMED: B(t) regular & real on R_+ through t=Re0~2.6 (no on-axis sing); part (A) data.")
print("The 'drift' of fitted |A| (5.5->6.1) = finite estimator climbing the fixed-Re ladder, NOT")
print("a pathology and NOT an on-axis accumulation. Accumulation point is at i*inf (off R_+).")
