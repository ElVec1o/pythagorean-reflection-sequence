/-
  TranslationTrick.lean
  =====================
  The elementary step behind the refutation of Class C faithfulness.

  Setting.  `rho : G -> H` is a homomorphism and `T <= H` is an ABELIAN NORMAL subgroup.  In the
  application `H = Isom(R^n)` and `T` is the translation subgroup: it is normal, with quotient
  the linear part, and abelian because it is the additive group of `R^n`.

  Statement.  If `rho u` lands in `T`, then for every `g` the commutator of `u` with the
  conjugate `g u g⁻¹` lies in `ker rho`.  Reason: `rho (g u g⁻¹)` is a conjugate of an element
  of `T`, hence in `T` by normality; elements of the abelian `T` commute; a commutator of
  commuting elements is trivial.

  That is the whole content.  No CAT(0) input, nothing about `G`, and nothing specific to
  dimension three, which is why the counterexamples extend from `n = 3` to `n = 4`.

  Used as: take `u` nontrivial in `W_n` whose image has trivial linear part, so that `rho_a u`
  is a translation; then `[u, R_0 u R_0]` lies in `ker rho_a`, and its nontriviality in `W_n` is
  checked separately in the Tits representation.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

namespace TranslationTrick

variable {G H : Type*} [Group G] [Group H]

/-- **The trick.**  `rho u` in an abelian normal `T` forces the commutator of `u` with any
    conjugate of `u` into `ker rho`. -/
theorem commutator_mem_ker
    (rho : G →* H) (T : Subgroup H) [T.Normal]
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (u : G) (hu : rho u ∈ T) (g : G) :
    rho (u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹) = 1 := by
  set v := g * u * g⁻¹ with hv
  have hconj : rho v ∈ T := by
    have he : rho v = rho g * rho u * (rho g)⁻¹ := by
      simp [hv, map_mul, map_inv]
    rw [he]
    exact ‹T.Normal›.conj_mem _ hu _
  have hc : rho u * rho v = rho v * rho u := hab _ hu _ hconj
  calc rho (u * v * u⁻¹ * v⁻¹)
      = rho u * rho v * (rho u)⁻¹ * (rho v)⁻¹ := by simp [map_mul, map_inv]
    _ = rho v * rho u * (rho u)⁻¹ * (rho v)⁻¹ := by rw [hc]
    _ = 1 := by simp [mul_assoc]

/-- The same conclusion, phrased as membership in the kernel. -/
theorem commutator_mem_ker'
    (rho : G →* H) (T : Subgroup H) [T.Normal]
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (u : G) (hu : rho u ∈ T) (g : G) :
    u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹ ∈ rho.ker := by
  rw [MonoidHom.mem_ker]
  exact commutator_mem_ker rho T hab u hu g

/-- Contrapositive, the form the refutation uses: a nontrivial such commutator witnesses that
    `rho` is not injective. -/
theorem not_injective_of_commutator_ne_one
    (rho : G →* H) (T : Subgroup H) [T.Normal]
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (u : G) (hu : rho u ∈ T) (g : G)
    (hne : u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹ ≠ 1) :
    ¬ Function.Injective rho := by
  intro hinj
  exact hne (hinj (by
    rw [map_one]
    exact commutator_mem_ker rho T hab u hu g))

/-! ### Axiom audit (Rule 5) -/

#print axioms commutator_mem_ker
#print axioms commutator_mem_ker'
#print axioms not_injective_of_commutator_ne_one

end TranslationTrick
