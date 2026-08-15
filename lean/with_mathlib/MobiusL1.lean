/-
  MobiusL1.lean
  =============
  The `\ell^1` instantiation of Proposition `prop:mobius` of `paper/journal/paper2.tex`,
  section 5.4 (`sec:mob`).

  `Mobius.lean` proves the Sherman--Morrison factorisation for an arbitrary module `E` over an
  arbitrary field `K`.  The paper's proposition is about one specific instance: `K = C`,
  `E = \ell^1(N)`, and `M_0`, `u`, `v`, `E` the concrete objects of \eqref{eq:rankone},
  \[
     M_0[b,a] = 2q^b q^{\max(a,b)}, \qquad E_b = 2q^b, \qquad u_b = 2q^{2b}, \qquad v_a = q^a ,
  \]
  the paper's indices running over `a, b \ge 1`.  Here the index type is `N` and index `n` stands
  for site `n+1`, so the exponents are written `n+1`.

  What this file adds over `Mobius.lean`:

  * `opOfKer`   a kernel with rows dominated by a summable sequence defines a `C`-linear operator
                on `\ell^1`; `funcOfSeq` the same for a bounded sequence and a functional;
  * `M0`, `uElt`, `EElt`, `vFun`, `oneFun`
                the concrete operator, the two `\ell^1` vectors and the two functionals of
                \eqref{eq:rankone}, for `\|q\| < 1`;
  * `rank_one`  the paper's one-line identity `2q^b\,q^{a+b} = (2q^{2b})(q^a)`, which is why the
                gap term is rank one;
  * `gapSystem_iff`
                the operator equation `(I - M_0 - g uv^T)P = E` is the display \eqref{eq:gapkernel}
                `P_b = 2q^b(1 + \sum_a K_g(a,b)P_a)`, coordinatewise;
  * `l1_solution_unique`
                \eqref{eq:gapkernel} has exactly one `\ell^1` solution, namely \eqref{eq:smresolvent};
  * `l1_smresolvent_left`, `l1_smresolvent_right`
                \eqref{eq:smresolvent} for the concrete operators;
  * `l1_B_mobius`
                `B = \sum_b P_b = (b_0 + g\kappa)/(1 - g t_1)`, which is \eqref{eq:mobius}, with the
                four scalars read off the concrete `R_0`;
  * `l1_B_of_solution`
                the two assembled: any `\ell^1` solution of \eqref{eq:gapkernel} has
                `\sum_b P_b = (b_0 + g\kappa)/(1 - g t_1)`;
  * `l1_B_eq_zero_iff`, `l1_B_pole`
                the single zero and the single pole.

  The two hypotheses are the proposition's own and are carried as hypotheses: `R_0` a two-sided
  inverse of `I - M_0` (Corollary `cor:sing`), and `1 - g t_1 \ne 0` (Remark `rem:mobhyp`).

  No `sorry`.
-/

import Mobius
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace MobiusL1

open scoped ENNReal

noncomputable section

/-! ## `\ell^1` as a `C`-module -/

/-- The complex sequence space `\ell^1(N)`.  It is a `C`-module with no further hypotheses; the
normed structure is not used. -/
abbrev ell1 := lp (fun _ : ℕ => ℂ) 1

theorem memlp_one_iff {f : ℕ → ℂ} : Memℓp f 1 ↔ Summable fun a => ‖f a‖ := by
  rw [memℓp_gen_iff (p := 1) (by simp)]
  simp

/-- An `\ell^1` element from an absolutely summable sequence. -/
def mk (f : ℕ → ℂ) (hf : Summable fun a => ‖f a‖) : ell1 := ⟨f, memlp_one_iff.mpr hf⟩

@[simp] theorem mk_apply (f : ℕ → ℂ) (hf : Summable fun a => ‖f a‖) (a : ℕ) :
    (mk f hf) a = f a := rfl

theorem summable_norm (x : ell1) : Summable fun a => ‖x a‖ :=
  memlp_one_iff.mp (lp.memℓp x)

theorem summable_self (x : ell1) : Summable fun a => x a :=
  (summable_norm x).of_norm

/-- Geometric summability in the shape the concrete data needs. -/
theorem summable_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (C : ℝ) {m : ℕ} (hm : m ≠ 0) (d : ℕ) :
    Summable fun b : ℕ => C * r ^ (m * b + d) := by
  have hrw : (fun b : ℕ => C * r ^ (m * b + d)) = fun b : ℕ => (C * r ^ d) * (r ^ m) ^ b := by
    funext b
    rw [pow_add, ← pow_mul, mul_comm m b]
    ring
  rw [hrw]
  exact (summable_geometric_of_lt_one (by positivity) (pow_lt_one₀ h0 h1 hm)).mul_left _

/-! ## Operators and functionals from dominated data -/

section Kernel

variable {k : ℕ → ℕ → ℂ} {c : ℕ → ℝ}

theorem row_summable_norm (hk : ∀ b a, ‖k b a‖ ≤ c b) (x : ell1) (b : ℕ) :
    Summable fun a => ‖k b a * x a‖ := by
  refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
    ((summable_norm x).mul_left (c b))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hk b a) (norm_nonneg _)

theorem row_summable (hk : ∀ b a, ‖k b a‖ ≤ c b) (x : ell1) (b : ℕ) :
    Summable fun a => k b a * x a :=
  (row_summable_norm hk x b).of_norm

theorem col_summable_norm (hk : ∀ b a, ‖k b a‖ ≤ c b) (hc : Summable c) (x : ell1) :
    Summable fun b => ‖∑' a, k b a * x a‖ := by
  refine Summable.of_nonneg_of_le (fun b => norm_nonneg _) (fun b => ?_)
    (hc.mul_right (∑' a, ‖x a‖))
  refine tsum_of_norm_bounded (((summable_norm x).hasSum.mul_left (c b))) (fun a => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hk b a) (norm_nonneg _)

/-- A kernel whose rows are dominated by a summable sequence defines a `C`-linear operator on
`\ell^1`. -/
def opOfKer (k : ℕ → ℕ → ℂ) (c : ℕ → ℝ) (hk : ∀ b a, ‖k b a‖ ≤ c b) (hc : Summable c) :
    ell1 →ₗ[ℂ] ell1 where
  toFun x := mk (fun b => ∑' a, k b a * x a) (col_summable_norm hk hc x)
  map_add' x y := by
    refine lp.ext (funext fun b => ?_)
    show ∑' a, k b a * (x a + y a) = (∑' a, k b a * x a) + ∑' a, k b a * y a
    have : ∀ a, k b a * (x a + y a) = k b a * x a + k b a * y a := fun a => by ring
    rw [tsum_congr this]
    exact (row_summable hk x b).tsum_add (row_summable hk y b)
  map_smul' t x := by
    refine lp.ext (funext fun b => ?_)
    show ∑' a, k b a * (t * x a) = t * ∑' a, k b a * x a
    have : ∀ a, k b a * (t * x a) = t * (k b a * x a) := fun a => by ring
    rw [tsum_congr this, tsum_mul_left]

@[simp] theorem opOfKer_apply (k : ℕ → ℕ → ℂ) (c : ℕ → ℝ) (hk : ∀ b a, ‖k b a‖ ≤ c b)
    (hc : Summable c) (x : ell1) (b : ℕ) :
    (opOfKer k c hk hc x) b = ∑' a, k b a * x a := rfl

end Kernel

section Functional

variable {w : ℕ → ℂ} {C : ℝ}

theorem pair_summable_norm (hw : ∀ a, ‖w a‖ ≤ C) (x : ell1) : Summable fun a => ‖w a * x a‖ := by
  refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
    ((summable_norm x).mul_left C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hw a) (norm_nonneg _)

theorem pair_summable (hw : ∀ a, ‖w a‖ ≤ C) (x : ell1) : Summable fun a => w a * x a :=
  (pair_summable_norm hw x).of_norm

/-- A bounded sequence defines a `C`-linear functional on `\ell^1`. -/
def funcOfSeq (w : ℕ → ℂ) (C : ℝ) (hw : ∀ a, ‖w a‖ ≤ C) : ell1 →ₗ[ℂ] ℂ where
  toFun x := ∑' a, w a * x a
  map_add' x y := by
    show ∑' a, w a * (x a + y a) = (∑' a, w a * x a) + ∑' a, w a * y a
    have : ∀ a, w a * (x a + y a) = w a * x a + w a * y a := fun a => by ring
    rw [tsum_congr this]
    exact (pair_summable hw x).tsum_add (pair_summable hw y)
  map_smul' t x := by
    show ∑' a, w a * (t * x a) = t * ∑' a, w a * x a
    have : ∀ a, w a * (t * x a) = t * (w a * x a) := fun a => by ring
    rw [tsum_congr this, tsum_mul_left]

@[simp] theorem funcOfSeq_apply (w : ℕ → ℂ) (C : ℝ) (hw : ∀ a, ‖w a‖ ≤ C) (x : ell1) :
    funcOfSeq w C hw x = ∑' a, w a * x a := rfl

end Functional

/-! ## The concrete data of \eqref{eq:rankone} -/

variable (q : ℂ)

/-- `M_0[b,a] = 2q^b q^{\max(a,b)}`, sites indexed from `1`. -/
def M0ker (b a : ℕ) : ℂ := 2 * q ^ (b + 1) * q ^ max (a + 1) (b + 1)

/-- `2q^b K_{\mathfrak g}(a,b)`, the gap-marked kernel of \eqref{eq:gapkernel} with its prefactor. -/
def gapKer (g : ℂ) (b a : ℕ) : ℂ :=
  2 * q ^ (b + 1) * (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g)

/-- `u_b = 2q^{2b}`. -/
def uSeq (b : ℕ) : ℂ := 2 * q ^ (2 * (b + 1))

/-- `v_a = q^a`. -/
def vSeq (a : ℕ) : ℂ := q ^ (a + 1)

/-- `E_b = 2q^b`. -/
def ESeq (b : ℕ) : ℂ := 2 * q ^ (b + 1)

/-- **The gap term is exactly rank one.**  This is the paper's `2q^b\cdot q^{a+b}=(2q^{2b})(q^a)`. -/
theorem rank_one (g : ℂ) (b a : ℕ) :
    gapKer q g b a = M0ker q b a + g * (uSeq q b * vSeq q a) := by
  unfold gapKer M0ker uSeq vSeq
  ring

/-! ### The bounds -/

theorem norm_M0ker_le (hq : ‖q‖ ≤ 1) (b a : ℕ) : ‖M0ker q b a‖ ≤ 2 * ‖q‖ ^ (b + 1) := by
  have h1 : ‖q‖ ^ max (a + 1) (b + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hq
  have h2 : ‖M0ker q b a‖ = 2 * ‖q‖ ^ (b + 1) * ‖q‖ ^ max (a + 1) (b + 1) := by
    unfold M0ker
    rw [norm_mul, norm_mul, norm_pow, norm_pow, RCLike.norm_two]
  rw [h2]
  calc 2 * ‖q‖ ^ (b + 1) * ‖q‖ ^ max (a + 1) (b + 1)
      ≤ 2 * ‖q‖ ^ (b + 1) * 1 := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * ‖q‖ ^ (b + 1) := by ring

theorem norm_uSeq (b : ℕ) : ‖uSeq q b‖ = 2 * ‖q‖ ^ (2 * b + 2) := by
  unfold uSeq
  rw [norm_mul, norm_pow, RCLike.norm_two]
  ring_nf

theorem norm_ESeq (b : ℕ) : ‖ESeq q b‖ = 2 * ‖q‖ ^ (1 * b + 1) := by
  unfold ESeq
  rw [norm_mul, norm_pow, RCLike.norm_two]
  ring_nf

theorem norm_vSeq_le (hq : ‖q‖ ≤ 1) (a : ℕ) : ‖vSeq q a‖ ≤ 1 := by
  unfold vSeq
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hq

/-! ### The concrete operator, vectors and functionals -/

variable (hq : ‖q‖ < 1)

/-- The ungapped bulk operator `M_0` of \eqref{eq:rankone} as an operator on `\ell^1`. -/
def M0 : ell1 →ₗ[ℂ] ell1 :=
  opOfKer (M0ker q) (fun b => 2 * ‖q‖ ^ (1 * b + 1))
    (fun b a => by simpa [one_mul] using norm_M0ker_le q hq.le b a)
    (summable_geom (norm_nonneg q) hq 2 one_ne_zero 1)

@[simp] theorem M0_apply (x : ell1) (b : ℕ) : (M0 q hq x) b = ∑' a, M0ker q b a * x a := rfl

/-- The source `E` of \eqref{eq:rankone}. -/
def EElt : ell1 :=
  mk (ESeq q) (by
    refine Summable.congr (summable_geom (norm_nonneg q) hq 2 one_ne_zero 1) (fun b => ?_)
    exact (norm_ESeq q b).symm)

@[simp] theorem EElt_apply (b : ℕ) : (EElt q hq) b = ESeq q b := rfl

/-- The left factor `u` of the rank-one gap term. -/
def uElt : ell1 :=
  mk (uSeq q) (by
    refine Summable.congr (summable_geom (norm_nonneg q) hq 2 (two_ne_zero) 2) (fun b => ?_)
    exact (norm_uSeq q b).symm)

@[simp] theorem uElt_apply (b : ℕ) : (uElt q hq) b = uSeq q b := rfl

/-- The right factor `v` of the rank-one gap term, as a functional on `\ell^1`. -/
def vFun : ell1 →ₗ[ℂ] ℂ := funcOfSeq (vSeq q) 1 (norm_vSeq_le q hq.le)

@[simp] theorem vFun_apply (x : ell1) : vFun q hq x = ∑' a, vSeq q a * x a := rfl

/-- The summation functional `\mathbf 1^{\top}`. -/
def oneFun : ell1 →ₗ[ℂ] ℂ := funcOfSeq (fun _ => 1) 1 (fun _ => by simp)

@[simp] theorem oneFun_apply (x : ell1) : oneFun x = ∑' a, x a := by
  simp [oneFun]

/-! ## The operator equation is the display \eqref{eq:gapkernel} -/

/-- The rank-one splitting at the level of the row sums. -/
theorem tsum_gapKer (g : ℂ) (P : ell1) (b : ℕ) :
    ∑' a, gapKer q g b a * P a
      = (∑' a, M0ker q b a * P a) + g * (vFun q hq P) * uSeq q b := by
  have hrow : Summable fun a => M0ker q b a * P a :=
    row_summable (c := fun b => 2 * ‖q‖ ^ (1 * b + 1))
      (fun b a => by simpa [one_mul] using norm_M0ker_le q hq.le b a) P b
  have hgap : Summable fun a => g * (uSeq q b * vSeq q a) * P a := by
    have : Summable fun a => (g * uSeq q b) * (vSeq q a * P a) :=
      (pair_summable (norm_vSeq_le q hq.le) P).mul_left _
    refine this.congr (fun a => by ring)
  have hsplit : ∀ a, gapKer q g b a * P a
      = M0ker q b a * P a + g * (uSeq q b * vSeq q a) * P a := by
    intro a
    rw [rank_one q g b a]
    ring
  rw [tsum_congr hsplit, hrow.tsum_add hgap]
  congr 1
  have : ∀ a, g * (uSeq q b * vSeq q a) * P a = (g * uSeq q b) * (vSeq q a * P a) := fun a => by
    ring
  rw [tsum_congr this, tsum_mul_left, vFun_apply]
  ring

/-- **The operator equation is \eqref{eq:gapkernel}.**  `(I - M_0 - g uv^{\top})P = E` holds in
`\ell^1` if and only if `P` satisfies the paper's display
`P_b = 2q^b(1 + \sum_{a\ge1}K_{\mathfrak g}(a,b)P_a)`. -/
theorem gapSystem_iff (g : ℂ) (P : ell1) :
    Mobius.opN (M0 q hq) (uElt q hq) (vFun q hq) g P = EElt q hq
      ↔ ∀ b : ℕ, P b
          = 2 * q ^ (b + 1)
            * (1 + ∑' a, (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g) * P a) := by
  constructor
  · intro h b
    have hb := congrArg (fun z : ell1 => z b) h
    simp only [Mobius.opN_apply] at hb
    have hcoord : P b - (∑' a, M0ker q b a * P a) - g * (vFun q hq P) * uSeq q b = ESeq q b := by
      simpa [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
        using hb
    have hg : ∑' a, gapKer q g b a * P a
        = (∑' a, M0ker q b a * P a) + g * (vFun q hq P) * uSeq q b := tsum_gapKer q hq g P b
    have hE : P b = ESeq q b + ∑' a, gapKer q g b a * P a := by
      rw [hg]; linear_combination hcoord
    have hfac : ∑' a, gapKer q g b a * P a
        = 2 * q ^ (b + 1)
          * ∑' a, (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g) * P a := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun a => ?_)
      unfold gapKer
      ring
    rw [hE, hfac]
    unfold ESeq
    ring
  · intro h
    refine lp.ext (funext fun b => ?_)
    have hg : ∑' a, gapKer q g b a * P a
        = (∑' a, M0ker q b a * P a) + g * (vFun q hq P) * uSeq q b := tsum_gapKer q hq g P b
    have hfac : ∑' a, gapKer q g b a * P a
        = 2 * q ^ (b + 1)
          * ∑' a, (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g) * P a := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun a => ?_)
      unfold gapKer
      ring
    have hE : P b = ESeq q b + ∑' a, gapKer q g b a * P a := by
      rw [hfac, h b]
      unfold ESeq
      ring
    show P b - (M0 q hq P) b - (g • ((vFun q hq P) • (uElt q hq))) b = ESeq q b
    have hu : (g • ((vFun q hq P) • (uElt q hq))) b = g * (vFun q hq P) * uSeq q b := by
      simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [hu, M0_apply]
    rw [hE, hg]
    ring

/-! ## The proposition, on `\ell^1` -/

variable (R0 : ell1 →ₗ[ℂ] ell1)

/-- **Proposition `prop:mobius`, \eqref{eq:smresolvent}, left half, on `\ell^1`.** -/
theorem l1_smresolvent_left (g : ℂ) (hR : ∀ y, R0 y - M0 q hq (R0 y) = y)
    (hδ : (1 : ℂ) - g * (vFun q hq) (R0 (uElt q hq)) ≠ 0) :
    Mobius.opN (M0 q hq) (uElt q hq) (vFun q hq) g
      ∘ₗ Mobius.opS R0 (uElt q hq) (vFun q hq) g (1 - g * (vFun q hq) (R0 (uElt q hq)))
      = LinearMap.id :=
  Mobius.opN_opS (M0 q hq) R0 (uElt q hq) (vFun q hq) g hR hδ

/-- **Proposition `prop:mobius`, \eqref{eq:smresolvent}, right half, on `\ell^1`.** -/
theorem l1_smresolvent_right (g : ℂ) (hL : ∀ y, R0 (y - M0 q hq y) = y)
    (hδ : (1 : ℂ) - g * (vFun q hq) (R0 (uElt q hq)) ≠ 0) :
    Mobius.opS R0 (uElt q hq) (vFun q hq) g (1 - g * (vFun q hq) (R0 (uElt q hq)))
      ∘ₗ Mobius.opN (M0 q hq) (uElt q hq) (vFun q hq) g
      = LinearMap.id :=
  Mobius.opS_opN (M0 q hq) R0 (uElt q hq) (vFun q hq) g hL hδ

/-- **Proposition `prop:mobius`, unique solvability, on `\ell^1`.**  The gap-marked system
\eqref{eq:gapkernel} has exactly one `\ell^1` solution, the one given by \eqref{eq:smresolvent}. -/
theorem l1_solution_unique (g : ℂ) (hR : ∀ y, R0 y - M0 q hq (R0 y) = y)
    (hL : ∀ y, R0 (y - M0 q hq y) = y)
    (hδ : (1 : ℂ) - g * (vFun q hq) (R0 (uElt q hq)) ≠ 0) (P : ell1) :
    (∀ b : ℕ, P b
        = 2 * q ^ (b + 1)
          * (1 + ∑' a, (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g) * P a))
      ↔ P = Mobius.opS R0 (uElt q hq) (vFun q hq) g
              (1 - g * (vFun q hq) (R0 (uElt q hq))) (EElt q hq) :=
  (gapSystem_iff q hq g P).symm.trans
    (Mobius.solution_unique (M0 q hq) R0 (uElt q hq) (vFun q hq) g hR hL hδ (EElt q hq) P)

/-- **Proposition `prop:mobius`, the closed form \eqref{eq:mobius}, on `\ell^1`.**
`B = \sum_b P_b = (b_0 + \mathfrak g\kappa)/(1 - \mathfrak g t_1)` with
`\kappa = t_0b_1 - b_0t_1`, the four scalars read off `R_0` exactly as in
Proposition `prop:bulkdress`. -/
theorem l1_B_mobius (g : ℂ) (b0 b1 t0 t1 kap : ℂ)
    (hb0 : b0 = oneFun (R0 (EElt q hq))) (hb1 : b1 = oneFun (R0 (uElt q hq)))
    (ht0 : t0 = (vFun q hq) (R0 (EElt q hq))) (ht1 : t1 = (vFun q hq) (R0 (uElt q hq)))
    (hk : kap = t0 * b1 - b0 * t1) (hδ : (1 : ℂ) - g * t1 ≠ 0) :
    oneFun (Mobius.opS R0 (uElt q hq) (vFun q hq) g (1 - g * t1) (EElt q hq))
      = (b0 + g * kap) / (1 - g * t1) :=
  Mobius.B_mobius R0 (uElt q hq) (vFun q hq) g oneFun (EElt q hq) b0 b1 t0 t1 kap
    hb0 hb1 ht0 ht1 hk hδ

/-- **Proposition `prop:mobius`, assembled.**  If `P \in \ell^1` solves the display
\eqref{eq:gapkernel} then `B = \sum_b P_b` is the M\"obius function
`(b_0 + \mathfrak g\kappa)/(1 - \mathfrak g t_1)` of the gap bridge weight. -/
theorem l1_B_of_solution (g : ℂ) (hR : ∀ y, R0 y - M0 q hq (R0 y) = y)
    (hL : ∀ y, R0 (y - M0 q hq y) = y) (b0 b1 t0 t1 kap : ℂ)
    (hb0 : b0 = oneFun (R0 (EElt q hq))) (hb1 : b1 = oneFun (R0 (uElt q hq)))
    (ht0 : t0 = (vFun q hq) (R0 (EElt q hq))) (ht1 : t1 = (vFun q hq) (R0 (uElt q hq)))
    (hk : kap = t0 * b1 - b0 * t1) (hδ : (1 : ℂ) - g * t1 ≠ 0) (P : ell1)
    (hP : ∀ b : ℕ, P b
        = 2 * q ^ (b + 1)
          * (1 + ∑' a, (q ^ max (a + 1) (b + 1) + q ^ ((a + 1) + (b + 1)) * g) * P a)) :
    ∑' b, P b = (b0 + g * kap) / (1 - g * t1) := by
  have hδ' : (1 : ℂ) - g * (vFun q hq) (R0 (uElt q hq)) ≠ 0 := by rw [← ht1]; exact hδ
  have hsol := (l1_solution_unique q hq R0 g hR hL hδ' P).mp hP
  rw [← ht1] at hsol
  rw [← oneFun_apply, hsol]
  exact l1_B_mobius q hq R0 g b0 b1 t0 t1 kap hb0 hb1 ht0 ht1 hk hδ

/-- **Proposition `prop:mobius`, the single zero, on `\ell^1`.** -/
theorem l1_B_eq_zero_iff (b0 t1 kap g : ℂ) (hk : kap ≠ 0) (hδ : (1 : ℂ) - g * t1 ≠ 0) :
    (b0 + g * kap) / (1 - g * t1) = 0 ↔ g = -b0 / kap :=
  Mobius.B_eq_zero_iff (K := ℂ) b0 t1 kap g hk hδ

/-- **Proposition `prop:mobius`, the single pole, on `\ell^1`.** -/
theorem l1_B_pole (t1 g : ℂ) (ht : t1 ≠ 0) : (1 : ℂ) - g * t1 = 0 ↔ g = 1 / t1 :=
  Mobius.B_pole (K := ℂ) t1 g ht

end

end MobiusL1

#print axioms MobiusL1.memlp_one_iff
#print axioms MobiusL1.summable_norm
#print axioms MobiusL1.summable_geom
#print axioms MobiusL1.row_summable
#print axioms MobiusL1.col_summable_norm
#print axioms MobiusL1.opOfKer
#print axioms MobiusL1.funcOfSeq
#print axioms MobiusL1.rank_one
#print axioms MobiusL1.norm_M0ker_le
#print axioms MobiusL1.tsum_gapKer
#print axioms MobiusL1.gapSystem_iff
#print axioms MobiusL1.l1_smresolvent_left
#print axioms MobiusL1.l1_smresolvent_right
#print axioms MobiusL1.l1_solution_unique
#print axioms MobiusL1.l1_B_mobius
#print axioms MobiusL1.l1_B_of_solution
#print axioms MobiusL1.l1_B_eq_zero_iff
#print axioms MobiusL1.l1_B_pole
