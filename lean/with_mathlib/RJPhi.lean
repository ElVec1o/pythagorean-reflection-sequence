import EltBridge

/-! Room 60: the Elt group law is modelled faithfully by affine maps over ℤ[t,t⁻¹].
Following paper1 (eq. symbolic-form): sigma is the ring involution t ↦ t⁻¹, and
R_x = (1,σ,0,0), R_y = (-1,σ,0,0), R_h = (1,σ,-1, 1 - t⁻¹).  -/

namespace RJPhi
open EltBridge EltBridge.Elt LaurentPolynomial

abbrev L := LaurentPolynomial ℤ

/-- sigma^delta. -/
noncomputable def sig : Bool → L → L
  | true, z => invert z
  | false, z => z

/-- Affine map `z ↦ eps * t^k * sigma^delta z + P`, as data. -/
structure Aff where
  eps : ℤ
  k : ℤ
  delta : Bool
  P : L

/-- The map it denotes. -/
noncomputable def Aff.act (f : Aff) (z : L) : L :=
  C f.eps * T f.k * sig f.delta z + f.P

noncomputable def Rx : Aff := ⟨1, 0, true, 0⟩
noncomputable def Ry : Aff := ⟨-1, 0, true, 0⟩
noncomputable def Rh : Aff := ⟨1, -1, true, 1 - T (-1)⟩

/-- Coefficient of `t^i`. -/
noncomputable def cf (p : L) (i : ℤ) : ℤ := AddMonoidAlgebra.coeff p i

theorem cf_add (p q : L) (i : ℤ) : cf (p + q) i = cf p i + cf q i := by
  simp [cf, AddMonoidAlgebra.coeff_add]
theorem cf_sub (p q : L) (i : ℤ) : cf (p - q) i = cf p i - cf q i := by
  unfold cf
  have := map_sub (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := ℤ)) p q
  simp only [AddMonoidAlgebra.coeffAddEquiv_apply] at this
  rw [this]; rfl
theorem cf_sum (s : Finset ℤ) (f : ℤ → L) (i : ℤ) :
    cf (∑ j ∈ s, f j) i = ∑ j ∈ s, cf (f j) i := by
  unfold cf; rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
theorem cf_CT (e k i : ℤ) : cf (C e * T k) i = if k = i then e else 0 := by
  rw [← single_eq_C_mul_T]; exact Finsupp.single_apply
theorem cf_ext {p q : L} (h : ∀ i, cf p i = cf q i) : p = q :=
  AddMonoidAlgebra.coeff_injective (Finsupp.ext h)

/-- The deposit polynomial `D = Σ d_j t^j`. -/
noncomputable def D (g : Elt) : L := ∑ j ∈ g.supp, C (g.d j) * T j

theorem D_apply (g : Elt) (i : ℤ) : cf (D g) i = g.d i := by
  classical
  unfold D
  rw [cf_sum]
  simp only [cf_CT]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact ((g.hsupp i h).1).symm

theorem D_s1 (g : Elt) : D (s1 g) = D g := rfl
theorem D_s2 (g : Elt) : D (s2 g) = D g := rfl

/-- **Phi**: `P = (t - 1) D`. -/
noncomputable def Phi (g : Elt) : Aff := ⟨g.eps, g.kstar, g.delta, (T 1 - 1) * D g⟩

theorem sig_mul (δ : Bool) (a b : L) : sig δ (a * b) = sig δ a * sig δ b := by
  cases δ <;> simp [sig]
theorem sig_add (δ : Bool) (a b : L) : sig δ (a + b) = sig δ a + sig δ b := by
  cases δ <;> simp [sig]

theorem intertwine_s1 (g : Elt) : (Phi (s1 g)).act = (Phi g).act ∘ Rx.act := by
  have hP : Phi (s1 g) = ⟨g.eps, g.kstar, !g.delta, (T 1 - 1) * D g⟩ := rfl
  rw [hP]; funext z
  cases h : g.delta <;>
    simp [Aff.act, Phi, Rx, h, sig, involutive_invert z]

theorem intertwine_s2 (g : Elt) : (Phi (s2 g)).act = (Phi g).act ∘ Ry.act := by
  have hP : Phi (s2 g) = ⟨-g.eps, g.kstar, !g.delta, (T 1 - 1) * D g⟩ := rfl
  rw [hP]; funext z
  cases h : g.delta <;>
    simp [Aff.act, Phi, Ry, h, sig, involutive_invert z]

theorem D_s3_true (g : Elt) (h : g.delta = true) :
    D (s3 g) = D g - C g.eps * T g.kstar := by
  apply cf_ext; intro i
  have e : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    simp [s3, h]
  rw [D_apply, e, cf_sub, D_apply, cf_CT, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem D_s3_false (g : Elt) (h : g.delta = false) :
    D (s3 g) = D g + C g.eps * T (g.kstar - 1) := by
  apply cf_ext; intro i
  have e : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    simp [s3, h]
  rw [D_apply, e, cf_add, D_apply, cf_CT, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem intertwine_s3_true (g : Elt) (h : g.delta = true) :
    (Phi (s3 g)).act = (Phi g).act ∘ Rh.act := by
  have hk : (s3 g).kstar = g.kstar + 1 := by simp [s3, h]
  have he : (s3 g).eps = g.eps := by simp [s3, h]
  have hd : (s3 g).delta = false := by simp [s3, h]
  funext z
  simp only [Aff.act, Phi, Rh, Function.comp_apply, hk, he, hd, D_s3_true g h, h, sig,
    map_add, map_mul, map_sub, invert_C, invert_T, map_one, involutive_invert z]
  rw [T_add]
  have : T (- -1 : ℤ) = (T 1 : L) := by norm_num
  rw [this]
  simp only [map_one, one_mul, neg_zero, T_zero, mul_one]
  ring

theorem intertwine_s3_false (g : Elt) (h : g.delta = false) :
    (Phi (s3 g)).act = (Phi g).act ∘ Rh.act := by
  have hk : (s3 g).kstar = g.kstar - 1 := by simp [s3, h]
  have he : (s3 g).eps = g.eps := by simp [s3, h]
  have hd : (s3 g).delta = true := by simp [s3, h]
  funext z
  simp only [Aff.act, Phi, Rh, Function.comp_apply, hk, he, hd, D_s3_false g h, h, sig,
    map_add, map_mul, map_sub, invert_C, invert_T, map_one]
  rw [T_sub]
  have h1 : (T 1 : L) * T (-1) = 1 := by rw [← T_add]; norm_num
  simp only [map_one, one_mul, neg_zero, T_zero, mul_one]
  linear_combination (C g.eps * T g.kstar : L) * h1

theorem intertwine_s3 (g : Elt) : (Phi (s3 g)).act = (Phi g).act ∘ Rh.act := by
  cases h : g.delta
  · exact intertwine_s3_false g h
  · exact intertwine_s3_true g h

theorem monomial_cancel {e k a b : ℤ} (he : e ≠ 0)
    (H : C e * T k * T a = (C e * T k * T b : L)) : a = b := by
  rw [mul_assoc, mul_assoc, ← T_add, ← T_add] at H
  have c := congrArg (fun p : L => cf p (k + a)) H
  simp only [cf_CT, if_true] at c
  by_contra hab
  rw [if_neg (by omega)] at c
  exact he c

/-- **Injectivity**: equal affine maps give the same group element. -/
theorem injective (g h : Elt) (H : (Phi g).act = (Phi h).act) : SameElt g h := by
  have h0 := congrFun H 0
  have h1 := congrFun H 1
  have hT := congrFun H (T 1)
  simp only [Aff.act, Phi] at h0 h1 hT
  have sig0 : ∀ δ, sig δ (0 : L) = 0 := by intro δ; cases δ <;> simp [sig]
  have sig1 : ∀ δ, sig δ (1 : L) = 1 := by intro δ; cases δ <;> simp [sig]
  rw [sig0, sig0, mul_zero, mul_zero, zero_add, zero_add] at h0
  rw [sig1, sig1, mul_one, mul_one, h0, add_left_inj] at h1
  -- h1 : C g.eps * T g.kstar = C h.eps * T h.kstar
  have hge : g.eps ≠ 0 := by rcases g.heps with e | e <;> omega
  have c1 := congrArg (fun p : L => cf p g.kstar) h1
  simp only [cf_CT, if_true] at c1
  have hk : g.kstar = h.kstar := by
    by_contra hne
    rw [if_neg (Ne.symm hne)] at c1
    exact hge c1
  have he : g.eps = h.eps := by rw [c1, if_pos hk.symm]
  have hdel : g.delta = h.delta := by
    rw [h0, add_left_inj, he, hk] at hT
    have ev : ∀ δ, sig δ (T 1 : L) = T (if δ then -1 else 1) := by
      intro δ; cases δ <;> simp [sig]
    rw [ev, ev] at hT
    have hhe : h.eps ≠ 0 := he ▸ hge
    have key := monomial_cancel hhe hT
    cases hg : g.delta <;> cases hh : h.delta <;> simp_all
  have hD : D g = D h := by
    have hne : (T 1 - 1 : L) ≠ 0 := by
      intro hz
      have := congrArg (fun p : L => cf p 1) hz
      simp only at this
      rw [cf_sub, show (T 1 : L) = C 1 * T 1 by simp, show (1 : L) = C 1 * T 0 by simp,
        cf_CT, cf_CT, show (0 : L) = C 0 * T 0 by simp, cf_CT] at this
      simp at this
    exact mul_left_cancel₀ hne h0
  exact ⟨hk, he, hdel, funext fun i => by rw [← D_apply g i, ← D_apply h i, hD]⟩

end RJPhi

#print axioms RJPhi.D_apply
#print axioms RJPhi.intertwine_s1
#print axioms RJPhi.intertwine_s2
#print axioms RJPhi.D_s3_true
#print axioms RJPhi.D_s3_false
#print axioms RJPhi.intertwine_s3_true
#print axioms RJPhi.intertwine_s3_false
#print axioms RJPhi.intertwine_s3
#print axioms RJPhi.cf_CT
#print axioms RJPhi.monomial_cancel
#print axioms RJPhi.cf_add
#print axioms RJPhi.cf_sub
#print axioms RJPhi.cf_sum
#print axioms RJPhi.cf_ext
#print axioms RJPhi.injective
