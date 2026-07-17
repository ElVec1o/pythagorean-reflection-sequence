#!/usr/bin/env python3
"""v2.12.21: arithmetic type of the family-law Borel transform + honest bridge assessment.
(Multi-agent workflow wf_e9a70df5-2ae, 8 agents w/ adversarial verification; all load-bearing
facts re-verified independently in the main loop before banking.)

RETRACTION: the v2.12.20-turn message called the Borel-transform arithmetic "classical lcm/zeta/
pi^2". THAT WAS WRONG. Adversarial front 1 + independent recheck: the prime valuations grow
LINEARLY in n (factorial/Legendre signature), NOT logarithmically (lcm/zeta signature). Example
v_3(den b_n), n=0..22: 0,2,4,7,8,10,13,...,47,50,51 (slope ~2.38) vs lcm(1..2n+1) would give
0,1,1,2,4,4,...,18 (logarithmic). The arithmetic is FACTORIAL-POCHHAMMER, not lcm-type.

EXACT ONSET THEOREM (verified, exception-free, all 13 odd primes p<=43 on 23 coefficients):
  for every odd prime p, p | den(b_n)  <=>  2n+1 >= p, with v_p(den b_n) = 2 exactly at the
  onset n = (p-1)/2, growing linearly thereafter. (p=2 is separate/suppressed, slope ~1.9,
  a half-integer (1/2)_n Bessel/parabola signature -- measured, not proved.)

CONSEQUENCE (robust, holonomy-independent): den(A_n) is SUPER-GEOMETRIC (log den(A_n)/n rises
5.4 -> 10.2 over n<=20, unbounded). Super-geometric denominators alone exclude b(t) from the
G-function class; hence sum A_n x^n is NOT of Andre arithmetic-Gevrey type and lies OUTSIDE the
G-function / E-function / E-operator (Fischler-Rivoal) classes -- regardless of the holonomy
question (which remains only partially tested: NO ODE for boxes up to (2,4) and (3,2) on 23
coeffs; corners (3,3),(3,4),(4,3) still data-starved -- do NOT claim full non-holonomy).

BRIDGE STATUS (honest, post-adversarial):
 - Representation q* = 1 - (8/pi^2) S_Borel(4/pi^2): numerically CONSISTENT with exact equality;
   cos head confirmed to ~1e-4 (NOT 1e-5 -- the 1e-5/2e-6 figures were estimator cherry-picks
   inside a ~2e-4 scatter band); the SAME machinery nails the three lower-x heads to 1e-13..1e-26
   (the strong, indirect evidence). Not a proof; contributes nothing to transcendence by itself.
 - Coefficients now exact through A_22 (all rational; A_21, A_22 denominators ~1e93). Rationality
   conjecture holds through order 22.
 - STEP 1 (summability proof) is NOT a finite cite-the-theorems program: it reduces to ONE hard
   lemma, a q-uniform turning-point (Olver/Airy-grade) factorial remainder bound for the
   Hahn-Exton crossing as q->1, with no citable form -- plausibly the same degenerate-saddle wall.
 - STEP 2 (sixth technology): the closest existing frame is Fischler-Rivoal E-operator theory; its
   ONE blocking hypothesis is "b(t) is a G-function", which the prime law REFUTES. So the missing
   tool is genuinely new: a value theory for Borel-Laplace sums of non-holonomic, factorial-
   denominator series at points transcendental over Q. q* is a canonical first target.

beta_2 irrationality: OPEN. This turn CLASSIFIES the arithmetic and CORRECTS a mislabel; it proves
no irrationality and closes the classical value-theory toolbox as inapplicable with a clean reason.
"""

# --- reproduction (loads family_coeffs.json = exact A_0..A_22) ---
import json, math
from fractions import Fraction as Fr
d=json.load(open('family_coeffs.json'))
A=[Fr(n,dd) for n,dd in zip(d['A_num'],d['A_den'])]
fact=[1]
for i in range(1,len(A)): fact.append(fact[-1]*i)
b=[A[n]/fact[n] for n in range(len(A))]
def vp(m,p):
    v=0
    while m%p==0: v+=1; m//=p
    return v
# onset theorem: odd p enters den(b_n) at n=(p-1)/2 with valuation 2
for p in [3,5,7,11,13,17,19,23,29,31,37,41,43]:
    o=(p-1)//2
    print(p, 'onset', o, 'v=', vp(b[o].denominator,p), 'clean-before', all(vp(b[n].denominator,p)==0 for n in range(o)))
