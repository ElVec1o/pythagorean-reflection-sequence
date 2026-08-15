/-
  Mobius.lean
  ===========
  Proposition `prop:mobius` of `paper/journal/paper2.tex`, section 5.4 (`sec:mob`): the gap term
  of the bulk kernel \eqref{eq:gapkernel} is rank one, so marking the gap bridges moves the
  resolvent by a Sherman--Morrison correction and turns `B` into a Moebius function of the gap
  bridge weight `g = \mathfrak g`.

  The proposition has two hypotheses: that `I - M_0` is invertible on `\ell^1`, which is
  `S_e \ne 0` (Corollary `cor:sing`), and that `1 - \mathfrak g t_1 \ne 0`, which is `s \ne 1`
  (Remark `rem:mobhyp`).  Both are supplied elsewhere and are hypotheses here.  Once the first
  holds, the inverse `R_0` is an operator and nothing analytic is left: the paper's proof is the
  verification that a stated operator is a two-sided inverse, together with one scalar
  computation.  That is what is formalised, over an arbitrary module `E` over an arbitrary
  field `K`, with

  * `R_0`   an operator with `R_0(I - M_0) = (I - M_0)R_0 = I`, which is the hypothesis
            "`I - M_0` is invertible", the `\ell^1` structure entering only through the
            existence of that inverse;
  * `u : E` and `v : E \to K` the two factors of the rank-one gap term of \eqref{eq:rankone},
            the pairing `v(R_0 u) = t_1` being a scalar because `v` is linear;
  * `Evec : E` the source and `one : E \to K` the summation functional, so that
            `b_0 = one(R_0 Evec)`, `b_1 = one(R_0 u)`, `t_0 = v(R_0 Evec)`, `t_1 = v(R_0 u)`
            are the four scalars of Proposition `prop:bulkdress`.

  Formalised here:

  * `opN_opS`, `opS_opN`   equation \eqref{eq:smresolvent}: the stated operator is a two-sided
                           inverse of `I - M_0 - g uv^T`;
  * `solution_unique`      the system \eqref{eq:gapkernel} has exactly one solution;
  * `B_mobius`             `B = (b_0 + g kappa)/(1 - g t_1)` with `kappa = t_0b_1 - b_0t_1`,
                           which is \eqref{eq:mobius};
  * `B_eq_zero_iff`, `B_pole`
                           the single zero at `g = -b_0/kappa` and the single pole at
                           `g = 1/t_1`.

  No `sorry`.
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

namespace Mobius

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The rank-one operator `u v^T` of \eqref{eq:rankone}. -/
def rankOne (u : E) (v : E →ₗ[K] K) : E →ₗ[K] E := v.smulRight u

@[simp] theorem rankOne_apply (u : E) (v : E →ₗ[K] K) (x : E) : rankOne u v x = v x • u := rfl

/-- `I - M_0 - g u v^T`: the gap-marked operator of \eqref{eq:gapkernel}. -/
def opN (M0 : E →ₗ[K] E) (u : E) (v : E →ₗ[K] K) (g : K) : E →ₗ[K] E :=
  LinearMap.id - M0 - g • rankOne u v

/-- `R_0 + (g/delta) R_0 u v^T R_0`: the right-hand side of \eqref{eq:smresolvent}. -/
def opS (R0 : E →ₗ[K] E) (u : E) (v : E →ₗ[K] K) (g δ : K) : E →ₗ[K] E :=
  R0 + (g / δ) • (R0 ∘ₗ rankOne u v ∘ₗ R0)

variable (M0 R0 : E →ₗ[K] E) (u : E) (v : E →ₗ[K] K) (g : K)

theorem opN_apply (x : E) : opN M0 u v g x = x - M0 x - g • (v x • u) := by
  simp [opN]

theorem opS_apply (δ : K) (x : E) :
    opS R0 u v g δ x = R0 x + (g / δ * v (R0 x)) • R0 u := by
  simp [opS, smul_smul]

/-! ## The two inverse identities -/

/-- `(I - M_0 - g uv^T)` applied to the operator of \eqref{eq:smresolvent} is the identity. -/
theorem opN_opS_apply (hR : ∀ y, R0 y - M0 (R0 y) = y)
    (hδ : (1 : K) - g * v (R0 u) ≠ 0) (x : E) :
    opN M0 u v g (opS R0 u v g (1 - g * v (R0 u)) x) = x := by
  have e1 : M0 (R0 x) = R0 x - x := by
    have h := sub_eq_iff_eq_add.mp (hR x)
    rw [eq_sub_iff_add_eq, add_comm]; exact h.symm
  have e2 : M0 (R0 u) = R0 u - u := by
    have h := sub_eq_iff_eq_add.mp (hR u)
    rw [eq_sub_iff_add_eq, add_comm]; exact h.symm
  rw [opS_apply, opN_apply]
  simp only [map_add, map_smul, smul_eq_mul, e1, e2]
  match_scalars <;> field_simp <;> ring

/-- The operator of \eqref{eq:smresolvent} applied to `(I - M_0 - g uv^T)` is the identity. -/
theorem opS_opN_apply (hL : ∀ y, R0 (y - M0 y) = y)
    (hδ : (1 : K) - g * v (R0 u) ≠ 0) (x : E) :
    opS R0 u v g (1 - g * v (R0 u)) (opN M0 u v g x) = x := by
  have key : R0 (opN M0 u v g x) = x - (g * v x) • R0 u := by
    rw [opN_apply, show x - M0 x - g • (v x • u) = (x - M0 x) - (g * v x) • u by
      rw [smul_smul], map_sub, hL x, map_smul]
  rw [opS_apply, key]
  simp only [map_sub, map_smul, smul_eq_mul]
  match_scalars <;> field_simp <;> ring

/-- **Equation \eqref{eq:smresolvent}, first half.** -/
theorem opN_opS (hR : ∀ y, R0 y - M0 (R0 y) = y) (hδ : (1 : K) - g * v (R0 u) ≠ 0) :
    opN M0 u v g ∘ₗ opS R0 u v g (1 - g * v (R0 u)) = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using opN_opS_apply M0 R0 u v g hR hδ x

/-- **Equation \eqref{eq:smresolvent}, second half.** -/
theorem opS_opN (hL : ∀ y, R0 (y - M0 y) = y) (hδ : (1 : K) - g * v (R0 u) ≠ 0) :
    opS R0 u v g (1 - g * v (R0 u)) ∘ₗ opN M0 u v g = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using opS_opN_apply M0 R0 u v g hL hδ x

/-- **Proposition `prop:mobius`, existence and uniqueness.**  The gap-marked system
\eqref{eq:gapkernel} has exactly one solution, namely the one given by
\eqref{eq:smresolvent}. -/
theorem solution_unique (hR : ∀ y, R0 y - M0 (R0 y) = y) (hL : ∀ y, R0 (y - M0 y) = y)
    (hδ : (1 : K) - g * v (R0 u) ≠ 0) (Evec y : E) :
    opN M0 u v g y = Evec ↔ y = opS R0 u v g (1 - g * v (R0 u)) Evec := by
  constructor
  · rintro rfl
    exact (opS_opN_apply M0 R0 u v g hL hδ y).symm
  · rintro rfl
    exact opN_opS_apply M0 R0 u v g hR hδ Evec

/-! ## The Moebius form of `B` -/

/-- **Proposition `prop:mobius`, the closed form.**  `B = (b_0 + g kappa)/(1 - g t_1)` with
`kappa = t_0 b_1 - b_0 t_1`, which is \eqref{eq:mobius}.  The four scalars are those of
Proposition `prop:bulkdress`, read off the ungapped resolvent `R_0`. -/
theorem B_mobius (one : E →ₗ[K] K) (Evec : E) (b0 b1 t0 t1 kap : K)
    (hb0 : b0 = one (R0 Evec)) (hb1 : b1 = one (R0 u))
    (ht0 : t0 = v (R0 Evec)) (ht1 : t1 = v (R0 u))
    (hk : kap = t0 * b1 - b0 * t1) (hδ : (1 : K) - g * t1 ≠ 0) :
    one (opS R0 u v g (1 - g * t1) Evec) = (b0 + g * kap) / (1 - g * t1) := by
  subst hb0; subst hb1; subst ht0; subst ht1; subst hk
  rw [opS_apply]
  simp only [map_add, map_smul, smul_eq_mul]
  field_simp
  ring

/-- **Proposition `prop:mobius`, the single zero.**  For `kappa /= 0` the value
`(b_0 + g kappa)/(1 - g t_1)` vanishes exactly at `g = -b_0/kappa`. -/
theorem B_eq_zero_iff (b0 t1 kap gg : K) (hk : kap ≠ 0) (hδ : (1 : K) - gg * t1 ≠ 0) :
    (b0 + gg * kap) / (1 - gg * t1) = 0 ↔ gg = -b0 / kap := by
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rw [eq_div_iff hk]
      linear_combination h
    · exact absurd h hδ
  · rintro rfl
    left
    field_simp
    ring

/-- **Proposition `prop:mobius`, the single pole.**  For `t_1 /= 0` the denominator vanishes
exactly at `g = 1/t_1`. -/
theorem B_pole (t1 gg : K) (ht : t1 ≠ 0) : (1 : K) - gg * t1 = 0 ↔ gg = 1 / t1 := by
  constructor
  · intro h
    rw [eq_div_iff ht]
    linear_combination -h
  · rintro rfl
    field_simp
    ring

end Mobius

#print axioms Mobius.rankOne_apply
#print axioms Mobius.opN_apply
#print axioms Mobius.opS_apply
#print axioms Mobius.opN_opS_apply
#print axioms Mobius.opS_opN_apply
#print axioms Mobius.opN_opS
#print axioms Mobius.opS_opN
#print axioms Mobius.solution_unique
#print axioms Mobius.B_mobius
#print axioms Mobius.B_eq_zero_iff
#print axioms Mobius.B_pole
