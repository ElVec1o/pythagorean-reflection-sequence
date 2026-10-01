/-
SymbolicForm.lean
=================
`lem:symbolic-form` of `paper/journal/paper1.tex` (Tier-B), in full.

For every word `w` of length `ℓ` in the three side-reflections `R_x, R_y, R_h` there are
`ε ∈ {±1}`, `δ ∈ {0,1}`, `k ∈ Z` with `|k| ≤ ℓ`, and `P_w ∈ Z[t^{±1}]` (all independent of the
triangle) such that, for every `ζ` of modulus one,
    `ρ_T(w) : z ↦ ε ζ^k σ^δ(z) + P_w(ζ)`,
with `supp P_w ⊆ [-ℓ,ℓ]`, `‖P_w‖_∞ ≤ ℓ`, `P_w(1) = 0`.

The generators are `R_x z = σ z`, `R_y z = -σ z`, `R_h z = ζ⁻¹ σ z + (1 - ζ⁻¹)`.  Laurent polynomials
are finitely supported `ℤ →₀ ℤ`; the composition law is the paper's
`P_{gw}(t) = P_g(t) + ε_g t^{k_g} P_w(t^{±1})`.  No sorry.
-/
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

namespace SymbolicForm

open Finsupp

/-- Symbolic data `(ε, δ, k, P)`. `δ = true` means "with conjugation". -/
structure Sym where
  ε : ℤ
  δ : Bool
  k : ℤ
  P : ℤ →₀ ℤ

/-- Shift `t^k * P`. -/
noncomputable def sh (k : ℤ) (P : ℤ →₀ ℤ) : ℤ →₀ ℤ := Finsupp.mapDomain (· + k) P

/-- Reflection `P(t^{-1})`. -/
noncomputable def rf (P : ℤ →₀ ℤ) : ℤ →₀ ℤ := Finsupp.mapDomain (fun j => -j) P

/-- `P` or `P(t^{-1})` according to `δ`. -/
noncomputable def comb (δ : Bool) (P : ℤ →₀ ℤ) : ℤ →₀ ℤ := if δ then rf P else P

/-- The composition law of symbolic data (`g` after `w`). -/
noncomputable def mulD (g w : Sym) : Sym where
  ε := g.ε * w.ε
  δ := xor g.δ w.δ
  k := g.k + (if g.δ then -w.k else w.k)
  P := g.P + g.ε • sh g.k (comb g.δ w.P)

/-- Evaluation `P(ζ)`. -/
noncomputable def evalP (P : ℤ →₀ ℤ) (ζ : ℂ) : ℂ := P.sum fun j c => (c : ℂ) * ζ ^ j

/-- Total coefficient sum, i.e. `P(1)`. -/
noncomputable def tot (P : ℤ →₀ ℤ) : ℤ := P.sum fun _ c => c

/-- The affine map `z ↦ ε ζ^k σ^δ(z) + P(ζ)`. -/
noncomputable def act (d : Sym) (ζ : ℂ) (z : ℂ) : ℂ :=
  (d.ε : ℂ) * ζ ^ d.k * (if d.δ then (starRingEnd ℂ) z else z) + evalP d.P ζ

/-! ### coefficient formulas -/

theorem sh_apply (k : ℤ) (P : ℤ →₀ ℤ) (j : ℤ) : sh k P j = P (j - k) := by
  have := Finsupp.mapDomain_apply (add_left_injective k) P (j - k)
  simpa using this

theorem rf_apply (P : ℤ →₀ ℤ) (j : ℤ) : rf P j = P (-j) := by
  have := Finsupp.mapDomain_apply (f := fun j : ℤ => -j) (by intro a b h; simpa using h) P (-j)
  simpa using this

theorem comb_apply (δ : Bool) (P : ℤ →₀ ℤ) (j : ℤ) :
    comb δ P j = if δ then P (-j) else P j := by
  unfold comb; cases δ <;> simp [rf_apply]

/-! ### evaluation formulas -/

theorem evalP_add (P Q : ℤ →₀ ℤ) (ζ : ℂ) : evalP (P + Q) ζ = evalP P ζ + evalP Q ζ := by
  unfold evalP
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b c; push_cast; ring

theorem evalP_smul (ε : ℤ) (P : ℤ →₀ ℤ) (ζ : ℂ) : evalP (ε • P) ζ = (ε : ℂ) * evalP P ζ := by
  unfold evalP
  rw [Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun j _ => ?_
    simp; ring
  · intro a; simp

theorem evalP_sh (k : ℤ) (P : ℤ →₀ ℤ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    evalP (sh k P) ζ = ζ ^ k * evalP P ζ := by
  unfold evalP sh
  rw [Finsupp.sum_mapDomain_index]
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun j _ => ?_
    rw [zpow_add₀ hζ]; ring
  · intro a; simp
  · intro a b c; push_cast; ring

theorem evalP_rf (P : ℤ →₀ ℤ) (ζ : ℂ) : evalP (rf P) ζ = evalP P ζ⁻¹ := by
  unfold evalP rf
  rw [Finsupp.sum_mapDomain_index]
  · refine Finsupp.sum_congr fun j _ => ?_
    rw [inv_zpow', zpow_neg]
  · intro a; simp
  · intro a b c; push_cast; ring

theorem evalP_comb (δ : Bool) (P : ℤ →₀ ℤ) (ζ : ℂ) :
    evalP (comb δ P) ζ = if δ then evalP P ζ⁻¹ else evalP P ζ := by
  unfold comb; cases δ <;> simp [evalP_rf]

theorem conj_evalP (P : ℤ →₀ ℤ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (starRingEnd ℂ) (evalP P ζ) = evalP P ζ⁻¹ := by
  have hc : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have h : ζ * (starRingEnd ℂ) ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    exact (eq_inv_of_mul_eq_one_right h)
  unfold evalP
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [map_mul, map_zpow₀, hc, map_intCast]

theorem tot_sh (k : ℤ) (P : ℤ →₀ ℤ) : tot (sh k P) = tot P := by
  unfold tot sh
  rw [Finsupp.sum_mapDomain_index]
  · intro a; rfl
  · intro a b c; rfl

theorem tot_rf (P : ℤ →₀ ℤ) : tot (rf P) = tot P := by
  unfold tot rf
  rw [Finsupp.sum_mapDomain_index]
  · intro a; rfl
  · intro a b c; rfl

theorem tot_comb (δ : Bool) (P : ℤ →₀ ℤ) : tot (comb δ P) = tot P := by
  unfold comb; cases δ <;> simp [tot_rf]

theorem tot_add (P Q : ℤ →₀ ℤ) : tot (P + Q) = tot P + tot Q := by
  unfold tot
  rw [Finsupp.sum_add_index']
  · intro a; rfl
  · intro a b c; rfl

theorem tot_smul (ε : ℤ) (P : ℤ →₀ ℤ) : tot (ε • P) = ε * tot P := by
  unfold tot
  rw [Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun j _ => ?_
    simp
  · intro a; rfl

/-! ### the action respects composition -/

theorem act_mulD (g w : Sym) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : ℂ) :
    act g ζ (act w ζ z) = act (mulD g w) ζ z := by
  have hz0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have h : ζ * (starRingEnd ℂ) ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    exact (eq_inv_of_mul_eq_one_right h)
  have hcj : ∀ m : ℤ, (starRingEnd ℂ) (ζ ^ m) = (ζ ^ m)⁻¹ := by
    intro m; rw [map_zpow₀, hconj, inv_zpow', zpow_neg]
  have hpe := conj_evalP w.P hζ
  have hP : ∀ (δ : Bool), evalP (sh g.k (comb δ w.P)) ζ =
      ζ ^ g.k * (if δ then evalP w.P ζ⁻¹ else evalP w.P ζ) := by
    intro δ; rw [evalP_sh _ _ hz0, evalP_comb]
  unfold act mulD
  simp only [evalP_add, evalP_smul, hP]
  rcases g with ⟨εg, δg, kg, Pg⟩
  rcases w with ⟨εw, δw, kw, Pw⟩
  simp only at hpe ⊢
  cases δg <;> cases δw <;>
    simp [hcj, hpe, zpow_add₀ hz0, zpow_neg, map_intCast, map_add, map_mul] <;>
    field_simp <;> ring

/-! ### the bounds -/

/-- The bounds of `lem:symbolic-form` at length `ℓ`. -/
def Bd (d : Sym) (ℓ : ℕ) : Prop :=
  (d.ε = 1 ∨ d.ε = -1) ∧ |d.k| ≤ ℓ ∧ (∀ j, d.P j ≠ 0 → |j| ≤ ℓ) ∧ (∀ j, |d.P j| ≤ ℓ) ∧
    tot d.P = 0

theorem Bd_mulD {g w : Sym} {ℓ : ℕ} (hg : Bd g 1) (hw : Bd w ℓ) : Bd (mulD g w) (ℓ + 1) := by
  obtain ⟨hgε, hgk, hgs, hgc, hgt⟩ := hg
  obtain ⟨hwε, hwk, hws, hwc, hwt⟩ := hw
  simp only [Nat.cast_one] at hgk hgs hgc
  have hcomb_c : ∀ m, |comb g.δ w.P m| ≤ ℓ := by
    intro m; rw [comb_apply]; split_ifs
    · exact hwc _
    · exact hwc _
  have hcomb_s : ∀ m, comb g.δ w.P m ≠ 0 → |m| ≤ ℓ := by
    intro m hm; rw [comb_apply] at hm; split_ifs at hm
    · have := hws _ hm; rwa [abs_neg] at this
    · exact hws _ hm
  have hP : ∀ j, (mulD g w).P j = g.P j + g.ε * comb g.δ w.P (j - g.k) := by
    intro j
    simp only [mulD, Finsupp.add_apply, Finsupp.smul_apply, sh_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mulD]
    rcases hgε with h | h <;> rcases hwε with h' | h' <;> simp [h, h']
  · simp only [mulD]
    have : |(if g.δ then -w.k else w.k)| ≤ ℓ := by split_ifs <;> simpa [abs_neg] using hwk
    calc |g.k + (if g.δ then -w.k else w.k)| ≤ |g.k| + |if g.δ then -w.k else w.k| := abs_add_le _ _
      _ ≤ ((ℓ + 1 : ℕ) : ℤ) := by push_cast; linarith
  · intro j hj
    rw [hP] at hj
    by_cases h1 : g.P j = 0
    · rw [h1, zero_add] at hj
      have h2 : comb g.δ w.P (j - g.k) ≠ 0 := fun h => hj (by rw [h, mul_zero])
      have := hcomb_s _ h2
      have h3 : |j| ≤ |j - g.k| + |g.k| := by
        calc |j| = |(j - g.k) + g.k| := by ring_nf
          _ ≤ |j - g.k| + |g.k| := abs_add_le _ _
      push_cast; linarith
    · have := hgs j h1
      push_cast
      have : (0 : ℤ) ≤ ℓ := by positivity
      linarith
  · intro j
    rw [hP]
    have h1 := hgc j
    have h2 := hcomb_c (j - g.k)
    have h3 : |g.ε * comb g.δ w.P (j - g.k)| ≤ ℓ := by
      rw [abs_mul]
      rcases hgε with h | h <;> rw [h] <;> simpa using h2
    calc |g.P j + g.ε * comb g.δ w.P (j - g.k)| ≤ |g.P j| + |g.ε * comb g.δ w.P (j - g.k)| :=
          abs_add_le _ _
      _ ≤ ((ℓ + 1 : ℕ) : ℤ) := by push_cast; linarith
  · simp only [mulD]
    rw [tot_add, tot_smul, tot_sh, tot_comb, hgt, hwt]; simp

/-! ### generators and words -/

inductive Gen | x | y | h

/-- Symbolic data of the three side reflections. -/
noncomputable def gd : Gen → Sym
  | .x => ⟨1, true, 0, 0⟩
  | .y => ⟨-1, true, 0, 0⟩
  | .h => ⟨1, true, -1, Finsupp.single 0 1 + (-1 : ℤ) • Finsupp.single (-1) 1⟩

/-- The generators as maps of `ℂ`. -/
noncomputable def gmap (ζ : ℂ) : Gen → ℂ → ℂ
  | .x => fun z => (starRingEnd ℂ) z
  | .y => fun z => -(starRingEnd ℂ) z
  | .h => fun z => ζ⁻¹ * (starRingEnd ℂ) z + (1 - ζ⁻¹)

theorem act_gd (g : Gen) (ζ : ℂ) (hζ : ζ ≠ 0) (z : ℂ) : act (gd g) ζ z = gmap ζ g z := by
  cases g
  · simp [act, gd, gmap, evalP]
  · simp [act, gd, gmap, evalP]
  · simp only [act, gd, gmap, evalP_add, evalP_smul]
    have e1 : evalP (Finsupp.single (0 : ℤ) (1 : ℤ)) ζ = 1 := by
      unfold evalP
      rw [Finsupp.sum_single_index (by simp)]
      simp
    have e2 : evalP (Finsupp.single (-1 : ℤ) (1 : ℤ)) ζ = ζ⁻¹ := by
      unfold evalP
      rw [Finsupp.sum_single_index (by simp)]
      simp
    rw [e1, e2]
    simp
    ring

theorem tot_single (a c : ℤ) : tot (Finsupp.single a c) = c := by
  unfold tot; rw [Finsupp.sum_single_index rfl]

theorem gh_apply (j : ℤ) :
    (Finsupp.single (0 : ℤ) (1 : ℤ) + (-1 : ℤ) • Finsupp.single (-1 : ℤ) (1 : ℤ)) j =
      (if (0 : ℤ) = j then 1 else 0) - (if (-1 : ℤ) = j then 1 else 0) := by
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem Bd_gd (g : Gen) : Bd (gd g) 1 := by
  cases g
  · refine ⟨Or.inl rfl, by simp [gd], ?_, ?_, ?_⟩ <;> simp [gd, tot]
  · refine ⟨Or.inr rfl, by simp [gd], ?_, ?_, ?_⟩ <;> simp [gd, tot]
  · refine ⟨Or.inl rfl, by simp [gd], ?_, ?_, ?_⟩
    · intro j hj
      simp only [gd] at hj
      rw [gh_apply] at hj
      by_cases h0 : (0 : ℤ) = j
      · subst h0; simp
      · by_cases h1 : (-1 : ℤ) = j
        · subst h1; simp
        · simp [h0, h1] at hj
    · intro j
      simp only [gd]
      rw [gh_apply]
      by_cases h0 : (0 : ℤ) = j
      · subst h0; simp
      · by_cases h1 : (-1 : ℤ) = j
        · subst h1; simp
        · simp [h0, h1]
    · simp only [gd]
      rw [tot_add, tot_smul, tot_single, tot_single]; simp

/-- Symbolic data of a word. -/
noncomputable def wd : List Gen → Sym
  | [] => ⟨1, false, 0, 0⟩
  | g :: w => mulD (gd g) (wd w)

/-- The action of a word. -/
noncomputable def rho (ζ : ℂ) : List Gen → ℂ → ℂ
  | [] => id
  | g :: w => gmap ζ g ∘ rho ζ w

theorem Bd_wd : ∀ w : List Gen, Bd (wd w) w.length := by
  intro w
  induction w with
  | nil => exact ⟨Or.inl rfl, by simp [wd], by simp [wd], by simp [wd], by simp [wd, tot]⟩
  | cons g w ih => exact Bd_mulD (Bd_gd g) ih

theorem rho_eq_act (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∀ (w : List Gen) (z : ℂ), rho ζ w z = act (wd w) ζ z := by
  have hz0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
  intro w
  induction w with
  | nil => intro z; simp [rho, wd, act, evalP]
  | cons g w ih =>
    intro z
    simp only [rho, wd, Function.comp]
    rw [ih z, ← act_mulD _ _ hζ, act_gd g ζ hz0]

/-- **`lem:symbolic-form`.**  Every word of length `ℓ` acts, for every `ζ` of modulus one, by
`z ↦ ε ζ^k σ^δ(z) + P_w(ζ)` with `|k| ≤ ℓ`, `supp P_w ⊆ [-ℓ,ℓ]`, `‖P_w‖_∞ ≤ ℓ`, `P_w(1) = 0`,
the data `(ε,δ,k,P_w)` being independent of `ζ`. -/
theorem symbolic_form (w : List Gen) :
    ∃ d : Sym, Bd d w.length ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ z, rho ζ w z = act d ζ z :=
  ⟨wd w, Bd_wd w, fun ζ hζ z => rho_eq_act ζ hζ w z⟩

/-! ### the mod-2 cocycle: `P_w ≡ 1 + t^k (mod 2)` -/

/-- `P ≡ 1 + t^k (mod 2)`, coefficientwise in `ZMod 2`. -/
def Par (d : Sym) : Prop :=
  ∀ j : ℤ, ((d.P j : ℤ) : ZMod 2) = (if j = 0 then 1 else 0) + (if j = d.k then 1 else 0)

theorem Par_mulD {g w : Sym} (hε : g.ε = 1 ∨ g.ε = -1) (hg : Par g) (hw : Par w) :
    Par (mulD g w) := by
  intro j
  have hP : (mulD g w).P j = g.P j + g.ε * comb g.δ w.P (j - g.k) := by
    simp only [mulD, Finsupp.add_apply, Finsupp.smul_apply, sh_apply, smul_eq_mul]
  have hε2 : ((g.ε : ℤ) : ZMod 2) = 1 := by rcases hε with h | h <;> simp [h]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [hP]
  push_cast
  rw [hε2, one_mul, hg j, comb_apply]
  have hk : (mulD g w).k = g.k + (if g.δ then -w.k else w.k) := rfl
  rw [hk]
  cases hδ : g.δ
  · simp only [Bool.false_eq_true, if_false]
    rw [hw (j - g.k)]
    have e1 : (j - g.k = 0) ↔ (j = g.k) := by omega
    have e2 : (j - g.k = w.k) ↔ (j = g.k + w.k) := by omega
    simp only [e1, e2]
    generalize (if j = 0 then (1 : ZMod 2) else 0) = x
    generalize (if j = g.k then (1 : ZMod 2) else 0) = y
    generalize (if j = g.k + w.k then (1 : ZMod 2) else 0) = z
    linear_combination y * h2
  · simp only [if_true]
    rw [hw (-(j - g.k))]
    have e1 : (-(j - g.k) = 0) ↔ (j = g.k) := by omega
    have e2 : (-(j - g.k) = w.k) ↔ (j = g.k + -w.k) := by omega
    simp only [e1, e2]
    generalize (if j = 0 then (1 : ZMod 2) else 0) = x
    generalize (if j = g.k then (1 : ZMod 2) else 0) = y
    generalize (if j = g.k + -w.k then (1 : ZMod 2) else 0) = z
    linear_combination y * h2

theorem Par_gd (g : Gen) : Par (gd g) := by
  intro j
  have h2 : (2 : ZMod 2) = 0 := by decide
  cases g
  · simp only [gd, Finsupp.coe_zero, Pi.zero_apply, Int.cast_zero]
    split_ifs <;> decide
  · simp only [gd, Finsupp.coe_zero, Pi.zero_apply, Int.cast_zero]
    split_ifs <;> decide
  · simp only [gd]
    rw [gh_apply]
    push_cast
    have e0 : ((0 : ℤ) = j) ↔ (j = 0) := eq_comm
    have e1 : ((-1 : ℤ) = j) ↔ (j = -1) := eq_comm
    simp only [e0, e1]
    split_ifs <;> first | decide | (exfalso; omega)

theorem Par_wd : ∀ w : List Gen, Par (wd w) := by
  intro w
  induction w with
  | nil =>
    intro j; simp only [wd, Finsupp.coe_zero, Pi.zero_apply, Int.cast_zero]
    split_ifs <;> decide
  | cons g w ih => exact Par_mulD (Bd_gd g).1 (Par_gd g) ih

end SymbolicForm

#print axioms SymbolicForm.act_mulD
#print axioms SymbolicForm.symbolic_form
#print axioms SymbolicForm.Par_wd
