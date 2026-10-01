/-
CollisionBound.lean
===================
The algebraic chain behind `prop:collision-vanishing` and `thm:effective-universality`
(`paper1.tex`), assembled from `SymbolicForm` (`lem:symbolic-form`) and `EffUnivCore`:

  Two words `w, w'` of length `≤ e`, with the same symbolic class `(ε, δ, k)`, that collide
  (`ρ_T(w) = ρ_T(w')` at one point) and whose translation polynomials differ, give
  `D = P_w - P_{w'} ≠ 0` with `D(ζ_T) = 0`, `supp D ⊆ [-e,e]`, `‖D‖_∞ ≤ 2e`, `D(1) = 0`
  (`collision_vanishing`); and then `c_T ≤ 2e` (`collision_complexity_bound`).

NOT formalised: the step from "`u_e^T ≠ u_e^sym`" (orbit counts) to the existence of such a pair of
words, which needs the full lamplighter/ball-counting machinery.  No sorry.
-/
import SymbolicForm
import EffUnivCore

namespace CollisionBound

open SymbolicForm Polynomial

/-- `prop:collision-vanishing`, algebraic core. -/
theorem collision_vanishing {ζ : ℂ} (hζ : ‖ζ‖ = 1) (w w' : List Gen) {e : ℕ}
    (hw : w.length ≤ e) (hw' : w'.length ≤ e)
    (hε : (wd w).ε = (wd w').ε) (hδ : (wd w).δ = (wd w').δ) (hk : (wd w).k = (wd w').k)
    (hcol : ∃ z, rho ζ w z = rho ζ w' z) (hne : (wd w).P ≠ (wd w').P) :
    ∃ D : ℤ →₀ ℤ, D ≠ 0 ∧ evalP D ζ = 0 ∧ (∀ j, D j ≠ 0 → |j| ≤ e) ∧
      (∀ j, |D j| ≤ 2 * e) ∧ tot D = 0 := by
  obtain ⟨z, hz⟩ := hcol
  rw [rho_eq_act ζ hζ, rho_eq_act ζ hζ] at hz
  unfold act at hz
  rw [hε, hδ, hk] at hz
  have hev : evalP (wd w).P ζ = evalP (wd w').P ζ := by
    have := hz
    linear_combination this
  have b1 := Bd_wd w
  have b2 := Bd_wd w'
  refine ⟨(wd w).P - (wd w').P, sub_ne_zero.mpr hne, ?_, ?_, ?_, ?_⟩
  · have : evalP ((wd w).P - (wd w').P) ζ = evalP (wd w).P ζ - evalP (wd w').P ζ := by
      have h1 : evalP ((wd w).P - (wd w').P + (wd w').P) ζ =
          evalP ((wd w).P - (wd w').P) ζ + evalP (wd w').P ζ := evalP_add _ _ _
      rw [sub_add_cancel] at h1
      linear_combination -h1
    rw [this, hev, sub_self]
  · intro j hj
    have hj' : (wd w).P j - (wd w').P j ≠ 0 := by simpa using hj
    by_cases h1 : (wd w).P j = 0
    · have h2 : (wd w').P j ≠ 0 := by intro h; apply hj'; rw [h1, h]; simp
      have := b2.2.2.1 j h2
      have : (w'.length : ℤ) ≤ e := by exact_mod_cast hw'
      linarith [b2.2.2.1 j h2]
    · have := b1.2.2.1 j h1
      have : (w.length : ℤ) ≤ e := by exact_mod_cast hw
      linarith [b1.2.2.1 j h1]
  · intro j
    have h1 := b1.2.2.2.1 j
    have h2 := b2.2.2.2.1 j
    have hl : (w.length : ℤ) ≤ e := by exact_mod_cast hw
    have hl' : (w'.length : ℤ) ≤ e := by exact_mod_cast hw'
    simp only [Finsupp.sub_apply]
    calc |(wd w).P j - (wd w').P j| ≤ |(wd w).P j| + |(wd w').P j| := abs_sub _ _
      _ ≤ 2 * (e : ℤ) := by linarith
  · have h1 : tot ((wd w).P - (wd w').P + (wd w').P) = tot ((wd w).P - (wd w').P) + tot (wd w').P :=
      tot_add _ _
    rw [sub_add_cancel] at h1
    rw [b1.2.2.2.2, b2.2.2.2.2] at *
    linarith

/-! ### from Laurent polynomials to `Z[X]`, and `c_T <= 2e` -/

/-- `t^e * D` as an honest polynomial (valid when `supp D ⊆ [-e,e]`). -/
noncomputable def toPoly (e : ℕ) (D : ℤ →₀ ℤ) : ℤ[X] :=
  D.sum fun j c => C c * X ^ (j + e).toNat

theorem toPoly_coeff (e : ℕ) (D : ℤ →₀ ℤ) (hD : ∀ j, D j ≠ 0 → |j| ≤ e) (n : ℕ) :
    (toPoly e D).coeff n = D ((n : ℤ) - e) := by
  unfold toPoly Finsupp.sum
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : D ((n : ℤ) - e) = 0
  · rw [h]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finsupp.mem_support_iff.mp hj
    have hb := hD j hj'
    by_cases hn : n = (j + e).toNat
    · exfalso
      have : (n : ℤ) = j + e := by
        rw [hn]; exact Int.toNat_of_nonneg (by have := abs_le.mp hb; omega)
      have : j = (n : ℤ) - e := by omega
      rw [this] at hj'
      exact hj' h
    · simp [hn]
  · have hmem : ((n : ℤ) - e) ∈ D.support := Finsupp.mem_support_iff.mpr h
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · have : n = ((n : ℤ) - e + e).toNat := by omega
      rw [if_pos this, mul_one]
    · intro j hj hne
      have hj' := Finsupp.mem_support_iff.mp hj
      have hb := hD j hj'
      have : ¬ n = (j + e).toNat := by
        intro hn
        apply hne
        have : (n : ℤ) = j + e := by
          rw [hn]; exact Int.toNat_of_nonneg (by have := abs_le.mp hb; omega)
        omega
      simp [this]

theorem aeval_toPoly (e : ℕ) (D : ℤ →₀ ℤ) (hD : ∀ j, D j ≠ 0 → |j| ≤ e) {ζ : ℂ} (hζ : ζ ≠ 0) :
    aeval ζ (toPoly e D) = ζ ^ (e : ℤ) * evalP D ζ := by
  unfold toPoly evalP
  rw [map_finsuppSum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j hj => ?_
  have hj' := Finsupp.mem_support_iff.mp hj
  have hb := abs_le.mp (hD j hj')
  have hnn : (0 : ℤ) ≤ j + e := by omega
  rw [map_mul, aeval_C, aeval_X_pow]
  have : ζ ^ (j + (e : ℤ)).toNat = ζ ^ (j + (e : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  rw [this, zpow_add₀ hζ]
  simp only [algebraMap_int_eq, eq_intCast]
  ring

theorem toPoly_ne_zero (e : ℕ) (D : ℤ →₀ ℤ) (hD : ∀ j, D j ≠ 0 → |j| ≤ e) (hne : D ≠ 0) :
    toPoly e D ≠ 0 := by
  intro h0
  apply hne
  ext j
  by_contra hj
  have hb := abs_le.mp (hD j hj)
  have := toPoly_coeff e D hD (j + e).toNat
  rw [h0, Polynomial.coeff_zero] at this
  have h2 : (((j + e).toNat : ℕ) : ℤ) = j + e := Int.toNat_of_nonneg (by omega)
  rw [h2] at this
  have : D (j + e - e) = 0 := this.symm
  simp at this
  exact hj this

/-- **Effective universality, assembled.**  If two words of length `≤ e` with the same symbolic class
collide at `ζ_T` but have different translation polynomials, then `c_T ≤ 2e`; equivalently, if
`c_T > 2e` no such collision exists.  Here `mu_T = A t^2 - E t + A` is the (primitive) minimal
polynomial of `ζ_T`, `A = c_T`. -/
theorem collision_complexity_bound {A E : ℤ} (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A)
    (hprim : (EffUnivCore.mu A E).IsPrimitive) {ζ : ℂ} (hμ : aeval ζ (EffUnivCore.mu A E) = 0)
    (hζ : ‖ζ‖ = 1) (w w' : List Gen) {e : ℕ} (hw : w.length ≤ e) (hw' : w'.length ≤ e)
    (hε : (wd w).ε = (wd w').ε) (hδ : (wd w).δ = (wd w').δ) (hk : (wd w).k = (wd w').k)
    (hcol : ∃ z, rho ζ w z = rho ζ w' z) (hne : (wd w).P ≠ (wd w').P) : A ≤ 2 * e := by
  have hz0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
  obtain ⟨D, hD0, hDζ, hDs, hDc, -⟩ := collision_vanishing hζ w w' hw hw' hε hδ hk hcol hne
  have hroot : aeval ζ (toPoly e D) = 0 := by
    rw [aeval_toPoly e D hDs hz0, hDζ, mul_zero]
  have hne' := toPoly_ne_zero e D hDs hD0
  have hbound : ∀ n, |(toPoly e D).coeff n| ≤ 2 * (e : ℤ) := by
    intro n; rw [toPoly_coeff e D hDs]; exact hDc _
  have := EffUnivCore.complexity_le_bound hA hE hE2 hprim ζ hμ (toPoly e D) hroot hne'
    (2 * (e : ℤ)) hbound
  exact_mod_cast this

/-! ### deviation = non-injectivity of evaluation on the symbolic ball -/

/-- The symbolic ball: symbolic data of words of length `≤ e` (shape-independent). -/
def symBall (e : ℕ) : Set Sym := {d | ∃ w : List Gen, w.length ≤ e ∧ wd w = d}

theorem affine_eq (a a' p p' : ℂ) (δ δ' : Bool) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (h : ∀ z : ℂ, a * (if δ then (starRingEnd ℂ) z else z) + p =
      a' * (if δ' then (starRingEnd ℂ) z else z) + p') : δ = δ' ∧ a = a' ∧ p = p' := by
  have hp : p = p' := by simpa using h 0
  subst hp
  have h1 := h 1
  have hI := h Complex.I
  have haa : a = a' := by
    cases δ <;> cases δ' <;> simpa using h1
  refine ⟨?_, haa, rfl⟩
  by_contra hd
  subst haa
  cases δ <;> cases δ' <;> simp at hd hI
  · have : a * Complex.I = -(a * Complex.I) := by simpa using hI
    have h2 : a * Complex.I = 0 := by linear_combination (1 / 2 : ℂ) * this
    exact ha (by simpa using h2)
  · have : a * -Complex.I = a * Complex.I := by simpa using hI
    have h2 : a * Complex.I = 0 := by linear_combination (-1 / 2 : ℂ) * this
    exact ha (by simpa using h2)

/-- Equal actions force equal symbolic class and equal evaluated translation part, provided `ζ`
has modulus one and is not a root of unity. -/
theorem class_eq_of_act_eq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hnr : ∀ m : ℕ, 0 < m → ζ ^ m ≠ 1)
    {d d' : Sym} (hε : d.ε = 1 ∨ d.ε = -1) (hε' : d'.ε = 1 ∨ d'.ε = -1)
    (h : ∀ z, act d ζ z = act d' ζ z) :
    d.ε = d'.ε ∧ d.δ = d'.δ ∧ d.k = d'.k ∧ evalP d.P ζ = evalP d'.P ζ := by
  have hz0 : ζ ≠ 0 := by intro h0; rw [h0] at hζ; simp at hζ
  have hε0 : (d.ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hε0' : (d'.ε : ℂ) ≠ 0 := by rcases hε' with h | h <;> simp [h]
  have ha : (d.ε : ℂ) * ζ ^ d.k ≠ 0 := mul_ne_zero hε0 (zpow_ne_zero _ hz0)
  have ha' : (d'.ε : ℂ) * ζ ^ d'.k ≠ 0 := mul_ne_zero hε0' (zpow_ne_zero _ hz0)
  obtain ⟨hδ, haa, hpp⟩ := affine_eq _ _ _ _ d.δ d'.δ ha ha' (fun z => h z)
  have hεsq : ((d.ε : ℂ)) ^ 2 = 1 ∧ ((d'.ε : ℂ)) ^ 2 = 1 := by
    constructor
    · rcases hε with h | h <;> simp [h]
    · rcases hε' with h | h <;> simp [h]
  have hsq : ζ ^ d.k * ζ ^ d.k = ζ ^ d'.k * ζ ^ d'.k := by
    have := congrArg (fun x => x ^ 2) haa
    simp only [mul_pow, hεsq.1, hεsq.2, one_mul] at this
    simpa [sq] using this
  have hkk : d.k = d'.k := by
    by_contra hne
    have hpow : ζ ^ (d.k + d.k - (d'.k + d'.k)) = 1 := by
      rw [zpow_sub₀ hz0, zpow_add₀ hz0, zpow_add₀ hz0, hsq]
      exact div_self (mul_ne_zero (zpow_ne_zero _ hz0) (zpow_ne_zero _ hz0))
    set m : ℤ := d.k + d.k - (d'.k + d'.k) with hm
    have hm0 : m ≠ 0 := by omega
    rcases Int.natAbs_eq m with hm1 | hm1
    · apply hnr m.natAbs (Int.natAbs_pos.mpr hm0)
      rw [← zpow_natCast, ← hm1]; exact hpow
    · apply hnr m.natAbs (Int.natAbs_pos.mpr hm0)
      rw [← zpow_natCast]
      have : ζ ^ (m.natAbs : ℤ) = (ζ ^ (-(m.natAbs : ℤ)))⁻¹ := by rw [zpow_neg, inv_inv]
      rw [this, ← hm1, hpow]; simp
  refine ⟨?_, hδ, hkk, hpp⟩
  rw [hkk] at haa
  have hz : ζ ^ d'.k ≠ 0 := zpow_ne_zero _ hz0
  have := mul_right_cancel₀ hz haa
  exact_mod_cast this

/-- **`thm:effective-universality`** (formal form).  If evaluation at `ζ_T` is not injective on the
symbolic ball of radius `e` -- i.e. the image ball has fewer elements than the universal ball, a
deviation at depth `≤ e` -- then `c_T ≤ 2e`.  Hypotheses: `mu_T = A t^2 - E t + A` primitive with
`0 < E < 2A`, `ζ_T` a root of `mu_T` of modulus one that is not a root of unity. -/
theorem effective_universality {A E : ℤ} (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A)
    (hprim : (EffUnivCore.mu A E).IsPrimitive) {ζ : ℂ} (hμ : aeval ζ (EffUnivCore.mu A E) = 0)
    (hζ : ‖ζ‖ = 1) (hnr : ∀ m : ℕ, 0 < m → ζ ^ m ≠ 1) (e : ℕ)
    (hdev : ¬ Set.InjOn (fun d : Sym => act d ζ) (symBall e)) : A ≤ 2 * e := by
  unfold Set.InjOn at hdev
  push Not at hdev
  obtain ⟨d, ⟨w, hw, rfl⟩, d', ⟨w', hw', rfl⟩, hact, hne⟩ := hdev
  have hact' : ∀ z, act (wd w) ζ z = act (wd w') ζ z := fun z => by
    have := congrFun hact z
    simpa using this
  obtain ⟨hε, hδ, hk, hP⟩ := class_eq_of_act_eq hζ hnr (Bd_wd w).1 (Bd_wd w').1 hact'
  have hPne : (wd w).P ≠ (wd w').P := by
    intro hPeq
    apply hne
    rcases hd : wd w with ⟨e1, d1, k1, P1⟩
    rcases hd' : wd w' with ⟨e2, d2, k2, P2⟩
    rw [hd, hd'] at hε hδ hk hPeq
    simp only at hε hδ hk hPeq
    subst hε; subst hδ; subst hk; subst hPeq; rfl
  have hcol : ∃ z, rho ζ w z = rho ζ w' z :=
    ⟨0, by rw [rho_eq_act ζ hζ, rho_eq_act ζ hζ]; exact hact' 0⟩
  exact collision_complexity_bound hA hE hE2 hprim hμ hζ w w' hw hw' hε hδ hk hcol hPne

/-- Contrapositive: `c_T > 2e` implies universality of the depth-`e` ball (evaluation at `ζ_T` is
injective on the symbolic ball of radius `e`). -/
theorem universality_of_large_complexity {A E : ℤ} (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A)
    (hprim : (EffUnivCore.mu A E).IsPrimitive) {ζ : ℂ} (hμ : aeval ζ (EffUnivCore.mu A E) = 0)
    (hζ : ‖ζ‖ = 1) (hnr : ∀ m : ℕ, 0 < m → ζ ^ m ≠ 1) (e : ℕ) (hlarge : 2 * (e : ℤ) < A) :
    Set.InjOn (fun d : Sym => act d ζ) (symBall e) := by
  by_contra h
  have := effective_universality hA hE hE2 hprim hμ hζ hnr e h
  omega

end CollisionBound

#print axioms CollisionBound.collision_vanishing
#print axioms CollisionBound.effective_universality
#print axioms CollisionBound.universality_of_large_complexity
