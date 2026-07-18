# Extraction of the Borel data from the crossing coefficients (order 30)

## The oscillation must be removed first
The A_n carry a period-6 sign pattern (three positive, three negative) from n ~ 12. Every naive
growth diagnostic is dominated by it: a variance test over the model |A_n| ~ C^n (n!)^s returns
~0.358 for **every** s in [0.5, 1.0] and so discriminates nothing.

## Gevrey order
Phase-matched growth G_n = (log|A_n| - log|A_{n-6}|)/6 removes the oscillation. Under
|A_n| ~ C^n (n!)^s one has G_n ~ log C + s log n, so s is the slope of G_n against log n:
s = 0.844 (n=16..30), 0.897 (n=23..30), 1.033 (n=26..30) -- rising towards 1 as the window
advances. Consistent with Gevrey-1.

The unnormalised ratio log|A_n|/(n log n) equals s + (log C - s)/log n. Its corrections are
O(1/log n), so at n=30 it reads 0.411 while s ~ 1. **A 1/n extrapolation of that quantity is the
wrong model** and returns a spurious 1/2.

## Singularity modulus: two routes, one biased
- **Direct (robust).** Phase-matched decay of the Borel coefficients,
  R = |b_n/b_{n-6}|^{-1/6}: 3.439, 3.250, 3.432, 3.632, 3.293 at n = 26..30. Oscillates about
  **R ~ 3.4**, with no trend.
- **3-term recurrence (biased).** Fitting a pure conjugate pair gives |t_0| = 2.820 at n_0 = 14
  rising monotonically to 3.558 at n_0 = 30. The increments decay (first-half mean 0.058,
  second-half 0.034) with a period-3 substructure, so the sequence is converging, but slowly and
  from below: the fit neglects the algebraic prefactor n^alpha, which biases it upward.
  Richardson extrapolation on it **diverges** (5.37, 57.1, 2275 at depths 1,2,3), confirming the
  convergence is not a clean power series in 1/n; the earlier 1/n extrapolation to 4.30 is
  therefore not reliable.

## Present state
R ~ 3.4 (direct route), arg t_0 ~ 62 degrees, Gevrey-1 supported but not established. The
recurrence and Pade routes bracket rather than pin. Order-40 coefficients are being reconstructed
to test whether s stays at 1 and whether the two routes meet.
