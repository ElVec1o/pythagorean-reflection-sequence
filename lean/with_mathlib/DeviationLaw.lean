/-
  DeviationLaw.lean
  =================
  The three-regime deviation-depth law of `paper1.tex` (Proposition around line 1765), as
  a COMPUTABLE lookup from the shape `(a, b)` alone.

  For coprime `(a,b)` the paper gives closed forms (paper1.tex:980-992):

      a + b odd    :  c_T = a^2 + b^2,        e_T = 2 |a^2 - b^2|
      a, b both odd:  c_T = (a^2 + b^2)/2,    e_T =   |a^2 - b^2|

  and the law

      n_T = 3 (c_T + e_T)                      if e_T >= c_T
      n_T = 6 c_T + min(e_T, 3 (c_T - e_T))    if e_T <= c_T.

  Two things this file establishes, both relevant to using the law in practice:

  * `c_T` and `e_T` are ORDINARY ARITHMETIC in `a` and `b` -- no shortest-vector search is
    involved -- so `nLaw` is decidable and computes in constant time from the shape.
  * The regime boundaries are integer identities in `a` and `b`: `e_T = c_T` is exactly
    `b^2 = 3a^2`, and `e_T = (3/4) c_T` is exactly `5 b^2 = 11 a^2` (stated without
    division as `4 e_T = 3 c_T`).  So selecting the regime is two integer comparisons.

  STATUS, stated exactly, because the distinction matters for anything built on this:
  the INEQUALITY `n_T <= nLaw` is a theorem for every shape (paper1.tex:1772; it needs
  only the unconditional upper half of `thm:metric`, and explicitly does NOT use the open
  `conj:lowerbound`).  EQUALITY is a theorem only at `(1,2)`; at twelve further shapes it
  is exhaustive-search verification, and in general it is conjectural.  Nothing here
  proves equality; this file formalizes the law's arithmetic, not its exactness.

  No `sorry`.
-/

import Mathlib.Tactic

namespace DeviationLaw

/-- `c_T` of the shape `(a, b)`, from the paper's closed form. -/
def cT (a b : ℤ) : ℤ := if (a + b) % 2 = 0 then (a ^ 2 + b ^ 2) / 2 else a ^ 2 + b ^ 2

/-- `e_T` of the shape `(a, b)`, from the paper's closed form. -/
def eT (a b : ℤ) : ℤ := if (a + b) % 2 = 0 then |a ^ 2 - b ^ 2| else 2 * |a ^ 2 - b ^ 2|

/-- The three-regime law.  `min` handles the switch at `e_T = (3/4) c_T` inside the
`e_T <= c_T` branch. -/
def nLaw (a b : ℤ) : ℤ :=
  if eT a b ≥ cT a b then 3 * (cT a b + eT a b)
  else 6 * cT a b + min (eT a b) (3 * (cT a b - eT a b))

/-! ### The paper's worked shapes -/

/-- `(1,2)`: `c_T = 5`, `e_T = 6` (paper1.tex:990). -/
theorem cT_one_two : cT 1 2 = 5 := by decide
theorem eT_one_two : eT 1 2 = 6 := by decide

/-- **The certified first deviation depth**, `n_{(1,2)} = 33`.  This is the one shape at
which the law is a theorem with equality, not just an inequality. -/
theorem nLaw_one_two : nLaw 1 2 = 33 := by decide

/-- `(3,4)`: `c_T = 25`, `e_T = 14` (paper1.tex:991-992). -/
theorem cT_three_four : cT 3 4 = 25 := by decide
theorem eT_three_four : eT 3 4 = 14 := by decide

/-! ### The regime boundaries are integer identities in the shape

For the `a + b` odd family with `0 < a < b` the two boundaries of the three-regime law
are exactly the Diophantine conditions the paper names, so choosing the regime is two
integer comparisons on `(a, b)` -- no search, no floating point, no angle. -/

variable {a b : ℤ}

/-- **First boundary: `e_T = c_T` iff `b^2 = 3 a^2`.** -/
theorem eT_eq_cT_iff (ha : 0 < a) (hab : a < b) (hodd : (a + b) % 2 = 1) :
    eT a b = cT a b ↔ b ^ 2 = 3 * a ^ 2 := by
  have h2 : (a + b) % 2 ≠ 0 := by omega
  have habs : |a ^ 2 - b ^ 2| = b ^ 2 - a ^ 2 := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  simp only [cT, eT, if_neg h2, habs]
  constructor <;> intro h <;> nlinarith [h]

/-- **Second boundary: `4 e_T = 3 c_T` iff `5 b^2 = 11 a^2`.**  Stated multiplied out, so
it is an identity over `ℤ` rather than a rational comparison. -/
theorem four_eT_eq_three_cT_iff (ha : 0 < a) (hab : a < b) (hodd : (a + b) % 2 = 1) :
    4 * eT a b = 3 * cT a b ↔ 5 * b ^ 2 = 11 * a ^ 2 := by
  have h2 : (a + b) % 2 ≠ 0 := by omega
  have habs : |a ^ 2 - b ^ 2| = b ^ 2 - a ^ 2 := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  simp only [cT, eT, if_neg h2, habs]
  constructor <;> intro h <;> nlinarith [h]

/-- **The regime is decided by two integer comparisons.**  Below the first boundary the
law reads `6 c_T + e_T`; between the boundaries it reads `9 c_T - 3 e_T`; above the second
it reads `3 (c_T + e_T)`.  This states the first branch, which is the one the paper writes
as `n_T = 6 c_T + e_T`. -/
theorem nLaw_low_regime (h1 : 4 * eT a b ≤ 3 * cT a b) (h2 : 0 ≤ eT a b)
    (hc : 0 < cT a b) : nLaw a b = 6 * cT a b + eT a b := by
  have hlt : ¬ (eT a b ≥ cT a b) := by omega
  simp only [nLaw, if_neg hlt]
  rw [min_eq_left (by omega)]

/-- **The middle regime**, `n_T = 9 c_T - 3 e_T`. -/
theorem nLaw_mid_regime (h1 : 3 * cT a b ≤ 4 * eT a b) (h2 : eT a b < cT a b) :
    nLaw a b = 9 * cT a b - 3 * eT a b := by
  have hlt : ¬ (eT a b ≥ cT a b) := by omega
  simp only [nLaw, if_neg hlt]
  rw [min_eq_right (by omega)]
  ring

/-- **The high regime**, `n_T = 3 (c_T + e_T)`. -/
theorem nLaw_high_regime (h : cT a b ≤ eT a b) : nLaw a b = 3 * (cT a b + eT a b) := by
  simp only [nLaw, if_pos h]

end DeviationLaw

#print axioms DeviationLaw.cT_one_two
#print axioms DeviationLaw.nLaw_one_two
#print axioms DeviationLaw.cT_three_four
#print axioms DeviationLaw.eT_three_four
#print axioms DeviationLaw.eT_eq_cT_iff
#print axioms DeviationLaw.four_eT_eq_three_cT_iff
#print axioms DeviationLaw.nLaw_low_regime
#print axioms DeviationLaw.nLaw_mid_regime
#print axioms DeviationLaw.nLaw_high_regime
