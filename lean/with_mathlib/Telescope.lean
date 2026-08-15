/-
  Telescope.lean
  ==============
  Lemma `lem:tel` (catalytic telescoping) of `paper/journal/paper2.tex`, section 5.2
  (`sec:tel`), together with the identification of its two instances.

  The paper indexes the sites by `s \ge s_0` with `s_0 \in \{0,1\}` and `\vartheta = 1 - s_0`.
  Here the index type is `N` and the index `n` stands for the site `s = n + s_0`, so
  `e_s = 2q^{\vartheta+s}` is `eCo q s0 th n = 2q^{\vartheta+(n+s_0)}`, which is `2q^{n+1}`
  once `s_0 + \vartheta = 1` is used.  `\Phi \in \ell^1` is carried as
  `Summable (fun n => \|\Phi n\|)`; the source is bounded, `\|c_n\| \le Cc`.

  Formalised here:

  * `three_term`      \eqref{eq:threeterm}, `G_k = C_k + a_kG_1 + b_kG_{k+2}`.  This is the
                      analytic heart: the split of the inner sum at `s' = s`, the interchange
                      of the two summations (Fubini against an `\ell^1 \times` geometric
                      majorant), one finite and one infinite geometric sum;
  * `summable_bProd`  the partial products `\prod_{i<j}b_{k+2i}` are absolutely summable in `j`,
                      by the ratio test, which is the paper's `\Xi^J|q|^{J^2+Jk} \to 0`;
  * `summable_aFrak`, `summable_cFrak`
                      the two ladders `\mathfrak a_k` and `\mathfrak c_k` converge;
  * `G_eq`            `G_k = \mathfrak c_k + \mathfrak a_kG_1`, the telescoping proper;
  * `G_one_solved`, `G_solved`
                      \eqref{eq:solved}, under `\mathfrak a_1 \ne 1`;
  * `aTel_bulk`, `bTel_bulk`, `aTel_travel`, `bTel_travel`
                      the last sentence of the lemma: `(s_0,\vartheta) = (1,0)` gives
                      `a_k = \alpha_k`, `b_k = \gamma_k`, and `(0,1)` gives `A_k`, `C_k`;
  * `l1_three_term`, `l1_G_eq`
                      the same statements for a `\Phi` given as an element of the `\ell^1` space
                      of `MobiusL1.lean`, so that the two files speak of one object.

  No `sorry`.
-/

import MobiusL1
import Mathlib.Analysis.SpecificLimits.Normed

namespace Telescope

open Filter Finset
open scoped Topology

noncomputable section

/-! ## The data of Definition `def:model` -/

variable (q : ℂ) (s0 th : ℕ)

/-- The edge weight `e_s = 2q^{\vartheta+s}` at the site `s = n + s_0`. -/
def eCo (n : ℕ) : ℂ := 2 * q ^ (th + (n + s0))

variable (c Φ : ℕ → ℂ)

/-- The section identity \eqref{eq:sectionid},
`\Phi_s = e_s(c_s + \sum_{s'\ge s_0}q^{\max(s,s')}\Phi_{s'})`, sites `s = n + s_0`. -/
def SectionId : Prop :=
  ∀ n, Φ n = eCo q s0 th n * (c n + ∑' m, q ^ (max n m + s0) * Φ m)

/-- The sections `G_k = \sum_{s \ge s_0}q^{ks}\Phi_s`. -/
def G (k : ℕ) : ℂ := ∑' n, q ^ (k * (n + s0)) * Φ n

/-- `\mathcal C_k = \sum_{s\ge s_0}e_sc_sq^{ks}`. -/
def CC (k : ℕ) : ℂ := ∑' n, q ^ (k * (n + s0)) * (eCo q s0 th n * c n)

/-- `a_k = 2q^{\vartheta+(k+1)s_0}/(1-q^{k+1})`. -/
def aTel (k : ℕ) : ℂ := 2 * q ^ (th + (k + 1) * s0) / (1 - q ^ (k + 1))

/-- `b_k = 2q^{\vartheta+k+2}/(1-q^{k+2}) - 2q^{\vartheta+k+1}/(1-q^{k+1})`. -/
def bTel (k : ℕ) : ℂ :=
  2 * q ^ (th + k + 2) / (1 - q ^ (k + 2)) - 2 * q ^ (th + k + 1) / (1 - q ^ (k + 1))

/-- `\prod_{i<j}b_{k+2i}`. -/
def bProd (k j : ℕ) : ℂ := ∏ i ∈ range j, bTel q th (k + 2 * i)

/-- `\mathfrak a_k = \sum_{j\ge0}a_{k+2j}\prod_{i<j}b_{k+2i}`. -/
def aFrak (k : ℕ) : ℂ := ∑' j, aTel q s0 th (k + 2 * j) * bProd q th k j

/-- `\mathfrak c_k = \sum_{j\ge0}\mathcal C_{k+2j}\prod_{i<j}b_{k+2i}`. -/
def cFrak (k : ℕ) : ℂ := ∑' j, CC q s0 th c (k + 2 * j) * bProd q th k j

end

end Telescope

namespace Telescope

noncomputable section

open Filter Finset
open scoped Topology

variable {q : ℂ} {s0 th : ℕ} {c Φ : ℕ → ℂ} {Cc : ℝ}

/-! ## Elementary bounds -/

theorem norm_pow_le_one (hq : ‖q‖ ≤ 1) (j : ℕ) : ‖q ^ j‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq

theorem summable_mul_of_bounded {w : ℕ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C)
    (hΦ : Summable fun n => ‖Φ n‖) : Summable fun n => ‖w n * Φ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hΦ.mul_left C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _)

theorem norm_eCo (hs : s0 + th = 1) (n : ℕ) : ‖eCo q s0 th n‖ = 2 * ‖q‖ ^ (n + 1) := by
  have he : th + (n + s0) = n + 1 := by omega
  unfold eCo
  rw [he, norm_mul, norm_pow, RCLike.norm_two]

theorem summable_geom_pow (hq : ‖q‖ < 1) (C : ℝ) : Summable fun n : ℕ => C * ‖q‖ ^ (n + 1) := by
  have : ∀ n : ℕ, C * ‖q‖ ^ (n + 1) = (C * ‖q‖) * ‖q‖ ^ n := fun n => by ring
  refine Summable.congr ?_ (fun n => (this n).symm)
  exact (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left _

/-- The denominators of `a_k` and `b_k` do not vanish. -/
theorem den_ne_zero (hq : ‖q‖ < 1) (j : ℕ) : (1 : ℂ) - q ^ (j + 1) ≠ 0 := by
  have h : ‖q ^ (j + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero j)
  intro hc
  have h1 : q ^ (j + 1) = 1 := by linear_combination -hc
  rw [h1] at h; simp at h

theorem pow_ne_one (hq : ‖q‖ < 1) (j : ℕ) : q ^ (j + 1) ≠ 1 := by
  intro hc
  have := den_ne_zero hq j
  rw [hc] at this
  exact this (by ring)

theorem norm_den_ge (hq : ‖q‖ < 1) (j : ℕ) : 1 - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (j + 1)‖ := by
  have h1 : ‖q ^ (j + 1)‖ ≤ ‖q‖ := by
    rw [norm_pow]
    calc ‖q‖ ^ (j + 1) = ‖q‖ ^ j * ‖q‖ := by ring
      _ ≤ 1 * ‖q‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
      _ = ‖q‖ := one_mul _
  have h2 : ‖(1 : ℂ)‖ - ‖q ^ (j + 1)‖ ≤ ‖(1 : ℂ) - q ^ (j + 1)‖ := norm_sub_norm_le _ _
  rw [norm_one] at h2
  linarith

theorem norm_div_den_le (hq : ‖q‖ < 1) (j : ℕ) (x : ℂ) :
    ‖x / (1 - q ^ (j + 1))‖ ≤ ‖x‖ / (1 - ‖q‖) := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hge : 1 - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (j + 1)‖ := norm_den_ge hq j
  rw [norm_div]
  gcongr

/-- `\|a_k\| \le 2/(1-\|q\|)`, uniformly in `k`. -/
theorem norm_aTel_le (hq : ‖q‖ < 1) (k : ℕ) : ‖aTel q s0 th k‖ ≤ 2 / (1 - ‖q‖) := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hnum : ‖(2 : ℂ) * q ^ (th + (k + 1) * s0)‖ ≤ 2 := by
    rw [norm_mul, RCLike.norm_two]
    calc 2 * ‖q ^ (th + (k + 1) * s0)‖ ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_pow_le_one hq.le _) (by norm_num)
      _ = 2 := by ring
  unfold aTel
  refine le_trans (norm_div_den_le hq k _) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hpos.le)

/-- `\|b_k\| \le \Xi\|q\|^{k+1}` with `\Xi = 4/(1-\|q\|)`, the paper's bound. -/
theorem norm_bTel_le (hq : ‖q‖ < 1) (k : ℕ) :
    ‖bTel q th k‖ ≤ (4 / (1 - ‖q‖)) * ‖q‖ ^ (k + 1) := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hmono : ∀ i j : ℕ, i ≤ j → ‖q‖ ^ j ≤ ‖q‖ ^ i := fun i j hij =>
    pow_le_pow_of_le_one (norm_nonneg _) hq.le hij
  have h2 : ‖(2 : ℂ) * q ^ (th + k + 2)‖ ≤ 2 * ‖q‖ ^ (k + 1) := by
    rw [norm_mul, RCLike.norm_two, norm_pow]
    have : ‖q‖ ^ (th + k + 2) ≤ ‖q‖ ^ (k + 1) := hmono _ _ (by omega)
    linarith
  have h1 : ‖(2 : ℂ) * q ^ (th + k + 1)‖ ≤ 2 * ‖q‖ ^ (k + 1) := by
    rw [norm_mul, RCLike.norm_two, norm_pow]
    have : ‖q‖ ^ (th + k + 1) ≤ ‖q‖ ^ (k + 1) := hmono _ _ (by omega)
    linarith
  have e2 : ‖2 * q ^ (th + k + 2) / (1 - q ^ (k + 2))‖ ≤ (2 * ‖q‖ ^ (k + 1)) / (1 - ‖q‖) := by
    refine le_trans (norm_div_den_le hq (k + 1) _) ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hpos.le)
  have e1 : ‖2 * q ^ (th + k + 1) / (1 - q ^ (k + 1))‖ ≤ (2 * ‖q‖ ^ (k + 1)) / (1 - ‖q‖) := by
    refine le_trans (norm_div_den_le hq k _) ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpos.le)
  unfold bTel
  refine le_trans (norm_sub_le _ _) ?_
  have : (4 / (1 - ‖q‖)) * ‖q‖ ^ (k + 1)
      = (2 * ‖q‖ ^ (k + 1)) / (1 - ‖q‖) + (2 * ‖q‖ ^ (k + 1)) / (1 - ‖q‖) := by
    field_simp; ring
  rw [this]
  exact add_le_add e2 e1

/-! ## Summability of the sections -/

theorem summable_G_norm (hq : ‖q‖ ≤ 1) (hΦ : Summable fun n => ‖Φ n‖) (k : ℕ) :
    Summable fun n => ‖q ^ (k * (n + s0)) * Φ n‖ :=
  summable_mul_of_bounded (fun _ => norm_pow_le_one hq _) hΦ

theorem norm_G_le (hq : ‖q‖ ≤ 1) (hΦ : Summable fun n => ‖Φ n‖) (k : ℕ) :
    ‖G q s0 Φ k‖ ≤ ∑' n, ‖Φ n‖ := by
  unfold G
  refine le_trans (norm_tsum_le_tsum_norm (summable_G_norm (s0 := s0) hq hΦ k)) ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_G_norm (s0 := s0) hq hΦ k) hΦ
  rw [norm_mul]
  calc ‖q ^ (k * (n + s0))‖ * ‖Φ n‖ ≤ 1 * ‖Φ n‖ :=
        mul_le_mul_of_nonneg_right (norm_pow_le_one hq _) (norm_nonneg _)
    _ = ‖Φ n‖ := one_mul _

/-- The bound on `\mathcal C_k` used by the ladder: `\|\mathcal C_k\|` is at most a constant
independent of `k`, as the paper's `2\|c\|_\infty/(1-|q|)` is. -/
theorem norm_CC_le (hq : ‖q‖ < 1) (hs : s0 + th = 1) (hc : ∀ n, ‖c n‖ ≤ Cc) (k : ℕ) :
    ‖CC q s0 th c k‖ ≤ ∑' n : ℕ, (2 * Cc) * ‖q‖ ^ (n + 1) := by
  have hCc : 0 ≤ Cc := le_trans (norm_nonneg _) (hc 0)
  have hterm : ∀ n, ‖q ^ (k * (n + s0)) * (eCo q s0 th n * c n)‖ ≤ (2 * Cc) * ‖q‖ ^ (n + 1) := by
    intro n
    rw [norm_mul, norm_mul, norm_eCo hs]
    have hXY : ‖q ^ (k * (n + s0))‖ * ‖c n‖ ≤ Cc := by
      calc ‖q ^ (k * (n + s0))‖ * ‖c n‖ ≤ 1 * ‖c n‖ :=
            mul_le_mul_of_nonneg_right (norm_pow_le_one hq.le _) (norm_nonneg _)
        _ = ‖c n‖ := one_mul _
        _ ≤ Cc := hc n
    calc ‖q ^ (k * (n + s0))‖ * (2 * ‖q‖ ^ (n + 1) * ‖c n‖)
        = (‖q ^ (k * (n + s0))‖ * ‖c n‖) * (2 * ‖q‖ ^ (n + 1)) := by ring
      _ ≤ Cc * (2 * ‖q‖ ^ (n + 1)) := mul_le_mul_of_nonneg_right hXY (by positivity)
      _ = (2 * Cc) * ‖q‖ ^ (n + 1) := by ring
  have hsum : Summable fun n => ‖q ^ (k * (n + s0)) * (eCo q s0 th n * c n)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (summable_geom_pow hq (2 * Cc))
  unfold CC
  refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
  exact Summable.tsum_le_tsum hterm hsum (summable_geom_pow hq (2 * Cc))

/-! ## The row sum: one finite and one infinite geometric sum -/

/-- The inner `n`-sum of \eqref{eq:threeterm} at a fixed `m`, after the split at `s' = s`.
This is the whole of the paper's two displays inside the proof of Lemma `lem:tel`. -/
theorem row_sum (hq : ‖q‖ < 1) (hs : s0 + th = 1) (k m : ℕ) (z : ℂ) :
    ∑' n, q ^ (k * (n + s0)) * eCo q s0 th n * (q ^ (max n m + s0) * z)
      = aTel q s0 th k * (q ^ (1 * (m + s0)) * z)
        + bTel q th k * (q ^ ((k + 2) * (m + s0)) * z) := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  set f : ℕ → ℂ := fun n => q ^ (k * (n + s0)) * eCo q s0 th n * (q ^ (max n m + s0) * z)
    with hfdef
  -- the two geometric ratios
  have hQ1 : ‖q ^ (k + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero k)
  have hQ2 : ‖q ^ (k + 2)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hd1 : (1 : ℂ) - q ^ (k + 1) ≠ 0 := den_ne_zero hq k
  have hd2 : (1 : ℂ) - q ^ (k + 2) ≠ 0 := den_ne_zero hq (k + 1)
  have hne1 : q ^ (k + 1) ≠ 1 := pow_ne_one hq k
  -- summability of `f`
  have hfnorm : ∀ n, ‖f n‖ ≤ (2 * ‖z‖) * ‖q‖ ^ (n + 1) := by
    intro n
    rw [hfdef]
    simp only
    rw [norm_mul, norm_mul, norm_mul, norm_eCo hs]
    have h1 := norm_pow_le_one hq.le (k * (n + s0))
    have h2 := norm_pow_le_one hq.le (max n m + s0)
    have hprod : ‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖ ≤ 1 := by
      calc ‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖ ≤ 1 * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ‖q ^ (k * (n + s0))‖ * (2 * ‖q‖ ^ (n + 1)) * (‖q ^ (max n m + s0)‖ * ‖z‖)
        = (‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖) * (2 * ‖z‖ * ‖q‖ ^ (n + 1)) := by ring
      _ ≤ 1 * (2 * ‖z‖ * ‖q‖ ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = 2 * ‖z‖ * ‖q‖ ^ (n + 1) := one_mul _
  have hfsum : Summable f :=
    Summable.of_norm_bounded (summable_geom_pow hq (2 * ‖z‖)) hfnorm
  -- the two closed forms
  set A : ℂ := 2 * q ^ (k * s0 + (th + s0) + m + s0) with hA
  set B : ℂ := 2 * q ^ (k * s0 + (th + s0) + s0) with hB
  have hlow : ∀ n ∈ range (m + 1), f n = A * z * (q ^ (k + 1)) ^ n := by
    intro n hn
    have hnm : n ≤ m := by
      have := Finset.mem_range.mp hn; omega
    have hmax : max n m = m := max_eq_right hnm
    have hE : k * (n + s0) + (th + (n + s0)) + (m + s0)
        = (k * s0 + (th + s0) + m + s0) + (k + 1) * n := by ring
    rw [hfdef]
    simp only [eCo, hmax, hA]
    calc q ^ (k * (n + s0)) * (2 * q ^ (th + (n + s0))) * (q ^ (m + s0) * z)
        = 2 * z * q ^ (k * (n + s0) + (th + (n + s0)) + (m + s0)) := by
          rw [pow_add, pow_add]; ring
      _ = 2 * z * q ^ ((k * s0 + (th + s0) + m + s0) + (k + 1) * n) := by rw [hE]
      _ = 2 * q ^ (k * s0 + (th + s0) + m + s0) * z * (q ^ (k + 1)) ^ n := by
          rw [pow_add, ← pow_mul]; ring
  have hhigh : ∀ i : ℕ, f (i + (m + 1)) = B * z * (q ^ (k + 2)) ^ (i + (m + 1)) := by
    intro i
    have hmax : max (i + (m + 1)) m = i + (m + 1) := max_eq_left (by omega)
    have hE : k * ((i + (m + 1)) + s0) + (th + ((i + (m + 1)) + s0)) + ((i + (m + 1)) + s0)
        = (k * s0 + (th + s0) + s0) + (k + 2) * (i + (m + 1)) := by ring
    rw [hfdef]
    simp only [eCo, hmax, hB]
    calc q ^ (k * ((i + (m + 1)) + s0)) * (2 * q ^ (th + ((i + (m + 1)) + s0)))
          * (q ^ ((i + (m + 1)) + s0) * z)
        = 2 * z * q ^ (k * ((i + (m + 1)) + s0) + (th + ((i + (m + 1)) + s0))
            + ((i + (m + 1)) + s0)) := by rw [pow_add, pow_add]; ring
      _ = 2 * z * q ^ ((k * s0 + (th + s0) + s0) + (k + 2) * (i + (m + 1))) := by rw [hE]
      _ = 2 * q ^ (k * s0 + (th + s0) + s0) * z * (q ^ (k + 2)) ^ (i + (m + 1)) := by
          rw [pow_add, ← pow_mul]; ring
  -- split the sum
  have hsplit : ∑' n, f n = (∑ n ∈ range (m + 1), f n) + ∑' i, f (i + (m + 1)) :=
    (hfsum.sum_add_tsum_nat_add (m + 1)).symm
  have hfin : ∑ n ∈ range (m + 1), f n
      = A * z * (((q ^ (k + 1)) ^ (m + 1) - 1) / (q ^ (k + 1) - 1)) := by
    rw [Finset.sum_congr rfl hlow, ← Finset.mul_sum, geom_sum_eq hne1]
  have htail : ∑' i, f (i + (m + 1))
      = B * z * ((q ^ (k + 2)) ^ (m + 1) * (1 - q ^ (k + 2))⁻¹) := by
    have hrw : ∀ i : ℕ, f (i + (m + 1))
        = (B * z * (q ^ (k + 2)) ^ (m + 1)) * (q ^ (k + 2)) ^ i := by
      intro i; rw [hhigh i, pow_add]; ring
    rw [tsum_congr hrw, tsum_mul_left, tsum_geometric_of_norm_lt_one hQ2, mul_assoc]
  rw [hsplit, hfin, htail]
  -- the algebra
  have hd1' : q ^ (k + 1) - 1 ≠ 0 := fun h => hne1 (by linear_combination h)
  have hAB : A = B * q ^ m := by
    rw [hA, hB, mul_assoc, ← pow_add,
      show k * s0 + (th + s0) + s0 + m = k * s0 + (th + s0) + m + s0 from by ring]
  have hXU : q ^ m * (q ^ (k + 1)) ^ (m + 1) = (q ^ (k + 2)) ^ m * q ^ (k + 1) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  have haT : aTel q s0 th k * (q ^ (1 * (m + s0)) * z)
      = (B * z * q ^ m) / (1 - q ^ (k + 1)) := by
    unfold aTel
    rw [hB, div_mul_eq_mul_div]
    congr 1
    calc (2 : ℂ) * q ^ (th + (k + 1) * s0) * (q ^ (1 * (m + s0)) * z)
        = 2 * z * q ^ (th + (k + 1) * s0 + 1 * (m + s0)) := by rw [pow_add]; ring
      _ = 2 * z * q ^ (k * s0 + (th + s0) + s0 + m) := by
          congr 2
          ring
      _ = 2 * q ^ (k * s0 + (th + s0) + s0) * z * q ^ m := by rw [pow_add]; ring
  have hbT : bTel q th k * (q ^ ((k + 2) * (m + s0)) * z)
      = (B * z * ((q ^ (k + 2)) ^ m * q ^ (k + 2))) / (1 - q ^ (k + 2))
        - (B * z * ((q ^ (k + 2)) ^ m * q ^ (k + 1))) / (1 - q ^ (k + 1)) := by
    unfold bTel
    rw [sub_mul, hB]
    congr 1
    · rw [div_mul_eq_mul_div]
      congr 1
      rw [← pow_mul]
      calc (2 : ℂ) * q ^ (th + k + 2) * (q ^ ((k + 2) * (m + s0)) * z)
          = 2 * z * q ^ (th + k + 2 + (k + 2) * (m + s0)) := by rw [pow_add]; ring
        _ = 2 * z * q ^ (k * s0 + (th + s0) + s0 + ((k + 2) * m + (k + 2))) := by
            congr 2
            ring
        _ = 2 * q ^ (k * s0 + (th + s0) + s0) * z * (q ^ ((k + 2) * m) * q ^ (k + 2)) := by
            rw [pow_add, pow_add]; ring
    · rw [div_mul_eq_mul_div]
      congr 1
      rw [← pow_mul]
      calc (2 : ℂ) * q ^ (th + k + 1) * (q ^ ((k + 2) * (m + s0)) * z)
          = 2 * z * q ^ (th + k + 1 + (k + 2) * (m + s0)) := by rw [pow_add]; ring
        _ = 2 * z * q ^ (k * s0 + (th + s0) + s0 + ((k + 2) * m + (k + 1))) := by
            congr 2
            ring
        _ = 2 * q ^ (k * s0 + (th + s0) + s0) * z * (q ^ ((k + 2) * m) * q ^ (k + 1)) := by
            rw [pow_add, pow_add]; ring
  rw [haT, hbT, hAB]
  have hI : B * q ^ m * z * (((q ^ (k + 1)) ^ (m + 1) - 1) / (q ^ (k + 1) - 1))
      = (B * z * q ^ m) / (1 - q ^ (k + 1))
        - (B * z * ((q ^ (k + 2)) ^ m * q ^ (k + 1))) / (1 - q ^ (k + 1)) := by
    rw [div_sub_div_same, ← mul_div_assoc, div_eq_div_iff hd1' hd1]
    linear_combination (B * z * (1 - q ^ (k + 1))) * hXU
  have hII : B * z * ((q ^ (k + 2)) ^ (m + 1) * (1 - q ^ (k + 2))⁻¹)
      = (B * z * ((q ^ (k + 2)) ^ m * q ^ (k + 2))) / (1 - q ^ (k + 2)) := by
    rw [pow_succ, div_eq_mul_inv]
    ring
  rw [hI, hII]
  ring

/-! ## The three-term relation \eqref{eq:threeterm} -/

theorem three_term (hq : ‖q‖ < 1) (hs : s0 + th = 1)
    (hΦ : Summable fun n => ‖Φ n‖) (hc : ∀ n, ‖c n‖ ≤ Cc)
    (hsec : SectionId q s0 th c Φ) (k : ℕ) :
    G q s0 Φ k
      = CC q s0 th c k + aTel q s0 th k * G q s0 Φ 1 + bTel q th k * G q s0 Φ (k + 2) := by
  have hCc : 0 ≤ Cc := le_trans (norm_nonneg _) (hc 0)
  have hΦnn : ∀ n, (0:ℝ) ≤ ‖Φ n‖ := fun n => norm_nonneg _
  -- the two-index family
  set F : ℕ → ℕ → ℂ :=
    fun n m => q ^ (k * (n + s0)) * eCo q s0 th n * (q ^ (max n m + s0) * Φ m) with hF
  have hFnorm : ∀ n m, ‖F n m‖ ≤ (2 * ‖q‖ ^ (n + 1)) * ‖Φ m‖ := by
    intro n m
    rw [hF]
    simp only
    rw [norm_mul, norm_mul, norm_mul, norm_eCo hs]
    have h1 := norm_pow_le_one hq.le (k * (n + s0))
    have h2 := norm_pow_le_one hq.le (max n m + s0)
    have hprod : ‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖ ≤ 1 := by
      calc ‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖ ≤ 1 * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ‖q ^ (k * (n + s0))‖ * (2 * ‖q‖ ^ (n + 1)) * (‖q ^ (max n m + s0)‖ * ‖Φ m‖)
        = (‖q ^ (k * (n + s0))‖ * ‖q ^ (max n m + s0)‖) * (2 * ‖q‖ ^ (n + 1) * ‖Φ m‖) := by
          ring
      _ ≤ 1 * (2 * ‖q‖ ^ (n + 1) * ‖Φ m‖) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = 2 * ‖q‖ ^ (n + 1) * ‖Φ m‖ := one_mul _
  have hmaj : Summable fun p : ℕ × ℕ => (2 * ‖q‖ ^ (p.1 + 1)) * ‖Φ p.2‖ :=
    Summable.mul_of_nonneg (summable_geom_pow hq 2) hΦ
      (fun n => by positivity) (fun m => norm_nonneg _)
  have hFsum : Summable (Function.uncurry F) :=
    Summable.of_norm_bounded hmaj (fun p => hFnorm p.1 p.2)
  -- the inner sums exist row by row
  have hrow : ∀ n, Summable fun m => F n m := by
    intro n
    refine Summable.of_norm_bounded (hΦ.mul_left (2 * ‖q‖ ^ (n + 1))) (fun m => hFnorm n m)
  -- expand `G k` by the section identity
  have hGexp : G q s0 Φ k
      = CC q s0 th c k + ∑' n, ∑' m, F n m := by
    have hterm : ∀ n, q ^ (k * (n + s0)) * Φ n
        = q ^ (k * (n + s0)) * (eCo q s0 th n * c n) + ∑' m, F n m := by
      intro n
      have hexp : ∑' m, F n m
          = q ^ (k * (n + s0)) * eCo q s0 th n * ∑' m, q ^ (max n m + s0) * Φ m := by
        simp only [hF]
        rw [tsum_mul_left]
      conv_lhs => rw [hsec n]
      rw [hexp]
      ring
    have hs1 : Summable fun n => q ^ (k * (n + s0)) * (eCo q s0 th n * c n) := by
      refine Summable.of_norm_bounded (summable_geom_pow hq (2 * Cc)) (fun n => ?_)
      rw [norm_mul, norm_mul, norm_eCo hs]
      have hXY : ‖q ^ (k * (n + s0))‖ * ‖c n‖ ≤ Cc := by
        calc ‖q ^ (k * (n + s0))‖ * ‖c n‖ ≤ 1 * ‖c n‖ :=
              mul_le_mul_of_nonneg_right (norm_pow_le_one hq.le _) (norm_nonneg _)
          _ = ‖c n‖ := one_mul _
          _ ≤ Cc := hc n
      calc ‖q ^ (k * (n + s0))‖ * (2 * ‖q‖ ^ (n + 1) * ‖c n‖)
          = (‖q ^ (k * (n + s0))‖ * ‖c n‖) * (2 * ‖q‖ ^ (n + 1)) := by ring
        _ ≤ Cc * (2 * ‖q‖ ^ (n + 1)) := mul_le_mul_of_nonneg_right hXY (by positivity)
        _ = (2 * Cc) * ‖q‖ ^ (n + 1) := by ring
    have hs2 : Summable fun n => ∑' m, F n m := by
      refine Summable.of_norm_bounded (summable_geom_pow hq (2 * ∑' m, ‖Φ m‖)) (fun n => ?_)
      refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
      · exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hFnorm n m)
          (hΦ.mul_left (2 * ‖q‖ ^ (n + 1)))
      · refine le_trans (Summable.tsum_le_tsum (fun m => hFnorm n m)
          (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hFnorm n m)
            (hΦ.mul_left (2 * ‖q‖ ^ (n + 1)))) (hΦ.mul_left (2 * ‖q‖ ^ (n + 1)))) ?_
        rw [tsum_mul_left]
        apply le_of_eq
        ring
    unfold G CC
    rw [tsum_congr hterm, hs1.tsum_add hs2]
  rw [hGexp]
  -- Fubini
  have hcomm : ∑' n, ∑' m, F n m = ∑' m, ∑' n, F n m := hFsum.tsum_comm.symm
  rw [hcomm]
  -- the row sums
  have hrowm : ∀ m, ∑' n, F n m
      = aTel q s0 th k * (q ^ (1 * (m + s0)) * Φ m)
        + bTel q th k * (q ^ ((k + 2) * (m + s0)) * Φ m) := fun m =>
    row_sum hq hs k m (Φ m)
  rw [tsum_congr hrowm]
  have hsa : Summable fun m => aTel q s0 th k * (q ^ (1 * (m + s0)) * Φ m) :=
    ((summable_G_norm (s0 := s0) hq.le hΦ 1).of_norm).mul_left _
  have hsb : Summable fun m => bTel q th k * (q ^ ((k + 2) * (m + s0)) * Φ m) :=
    ((summable_G_norm (s0 := s0) hq.le hΦ (k + 2)).of_norm).mul_left _
  rw [hsa.tsum_add hsb, tsum_mul_left, tsum_mul_left]
  unfold G
  ring

/-! ## The partial products and the two ladders -/

theorem bProd_succ (k j : ℕ) :
    bProd q th k (j + 1) = bProd q th k j * bTel q th (k + 2 * j) := by
  unfold bProd
  rw [Finset.prod_range_succ]

theorem bProd_zero (k : ℕ) : bProd q th k 0 = 1 := by
  unfold bProd; simp

/-- The paper's `\bigl|\prod_{i<J}b_{k+2i}\bigr| \le \Xi^J|q|^{J^2+Jk} \to 0`, in the form the
ratio test consumes. -/
theorem summable_bProd_norm (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun j => ‖bProd q th k j‖ := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hXi : (0:ℝ) ≤ 4 / (1 - ‖q‖) := by positivity
  -- eventually the ratio is at most 1/2
  have hto : Tendsto (fun j : ℕ => (4 / (1 - ‖q‖)) * ‖q‖ ^ (k + 2 * j + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ‖q‖ ^ (k + 2 * j + 1)) atTop (𝓝 0) := by
      have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
      have hsq : Tendsto (fun j : ℕ => ‖q‖ ^ (k + 1) * (‖q‖ ^ 2) ^ j) atTop (𝓝 0) := by
        have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq2
        simpa using this.const_mul (‖q‖ ^ (k + 1))
      refine hsq.congr (fun j => ?_)
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    simpa using h1.const_mul (4 / (1 - ‖q‖))
  have hev : ∀ᶠ j : ℕ in atTop, (4 / (1 - ‖q‖)) * ‖q‖ ^ (k + 2 * j + 1) ≤ 1 / 2 := by
    have := hto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))
    exact this.mono (fun j hj => le_of_lt hj)
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  refine hev.mono (fun j hj => ?_)
  have hstep : ‖bProd q th k (j + 1)‖
      = ‖bProd q th k j‖ * ‖bTel q th (k + 2 * j)‖ := by
    rw [bProd_succ, norm_mul]
  have hb : ‖bTel q th (k + 2 * j)‖ ≤ (4 / (1 - ‖q‖)) * ‖q‖ ^ (k + 2 * j + 1) :=
    norm_bTel_le hq _
  have : ‖bProd q th k (j + 1)‖ ≤ ‖bProd q th k j‖ * (1 / 2) := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (le_trans hb hj) (norm_nonneg _)
  calc ‖(fun j => ‖bProd q th k j‖) (j + 1)‖ = ‖bProd q th k (j + 1)‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
    _ ≤ ‖bProd q th k j‖ * (1 / 2) := this
    _ = 1 / 2 * ‖(fun j => ‖bProd q th k j‖) j‖ := by
        rw [Real.norm_of_nonneg (norm_nonneg (bProd q th k j))]
        ring

theorem summable_bProd (hq : ‖q‖ < 1) (k : ℕ) : Summable fun j => bProd q th k j :=
  (summable_bProd_norm hq k).of_norm

theorem tendsto_bProd (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun j => bProd q th k j) atTop (𝓝 0) :=
  (summable_bProd hq k).tendsto_atTop_zero

theorem summable_aFrak (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun j => aTel q s0 th (k + 2 * j) * bProd q th k j := by
  refine Summable.of_norm_bounded
    ((summable_bProd_norm (th := th) hq k).mul_left (2 / (1 - ‖q‖))) (fun j => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_aTel_le hq _) (norm_nonneg _)

theorem summable_cFrak (hq : ‖q‖ < 1) (hs : s0 + th = 1) (hc : ∀ n, ‖c n‖ ≤ Cc) (k : ℕ) :
    Summable fun j => CC q s0 th c (k + 2 * j) * bProd q th k j := by
  refine Summable.of_norm_bounded
    ((summable_bProd_norm (th := th) hq k).mul_left (∑' n : ℕ, (2 * Cc) * ‖q‖ ^ (n + 1)))
    (fun j => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_CC_le hq hs hc _) (norm_nonneg _)

/-! ## The telescoping proper -/

/-- **Lemma `lem:tel`, the telescoped form.**  `G_k = \mathfrak c_k + \mathfrak a_kG_1`. -/
theorem G_eq (hq : ‖q‖ < 1) (hs : s0 + th = 1)
    (hΦ : Summable fun n => ‖Φ n‖) (hc : ∀ n, ‖c n‖ ≤ Cc)
    (hsec : SectionId q s0 th c Φ) (k : ℕ) :
    G q s0 Φ k = cFrak q s0 th c k + aFrak q s0 th k * G q s0 Φ 1 := by
  set w : ℕ → ℂ :=
    fun j => (CC q s0 th c (k + 2 * j) + aTel q s0 th (k + 2 * j) * G q s0 Φ 1)
      * bProd q th k j with hw
  set R : ℕ → ℂ := fun j => G q s0 Φ (k + 2 * j) * bProd q th k j with hR
  -- one step of the recursion
  have hstep : ∀ j, R j = w j + R (j + 1) := by
    intro j
    have h3 := three_term hq hs hΦ hc hsec (k + 2 * j)
    have hidx : k + 2 * j + 2 = k + 2 * (j + 1) := by ring
    rw [hR, hw]
    simp only
    rw [h3, bProd_succ, hidx]
    ring
  -- partial sums telescope
  have hpart : ∀ J, ∑ j ∈ range J, w j = R 0 - R J := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        rw [Finset.sum_range_succ, ih, hstep J]
        ring
  have hR0 : R 0 = G q s0 Φ k := by
    rw [hR]; simp [bProd_zero]
  -- the remainder vanishes
  have hRto : Tendsto R atTop (𝓝 0) := by
    have hb : ∀ j, ‖R j‖ ≤ (∑' n, ‖Φ n‖) * ‖bProd q th k j‖ := by
      intro j
      rw [hR, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_G_le hq.le hΦ _) (norm_nonneg _)
    have hmaj : Tendsto (fun j => (∑' n, ‖Φ n‖) * ‖bProd q th k j‖) atTop (𝓝 0) := by
      have := (tendsto_bProd (th := th) hq k).norm
      simpa using this.const_mul (∑' n, ‖Φ n‖)
    refine squeeze_zero_norm hb ?_
    simpa using hmaj
  -- the sum of `w`
  have hwsum : Summable w := by
    have h1 := summable_cFrak (th := th) hq hs hc k
    have h2 := (summable_aFrak (s0 := s0) (th := th) hq k).mul_right (G q s0 Φ 1)
    refine (h1.add h2).congr (fun j => ?_)
    rw [hw]
    ring
  have hlim : Tendsto (fun J => ∑ j ∈ range J, w j) atTop (𝓝 (G q s0 Φ k)) := by
    have : (fun J => ∑ j ∈ range J, w j) = fun J => R 0 - R J := funext hpart
    rw [this, hR0]
    simpa using tendsto_const_nhds.sub hRto
  have heq : ∑' j, w j = G q s0 Φ k :=
    tendsto_nhds_unique hwsum.hasSum.tendsto_sum_nat hlim
  -- split it
  have hsplit : ∑' j, w j = cFrak q s0 th c k + aFrak q s0 th k * G q s0 Φ 1 := by
    have h1 := summable_cFrak (th := th) hq hs hc k
    have h2 := (summable_aFrak (s0 := s0) (th := th) hq k).mul_right (G q s0 Φ 1)
    have hrw : ∀ j, w j = CC q s0 th c (k + 2 * j) * bProd q th k j
        + (aTel q s0 th (k + 2 * j) * bProd q th k j) * G q s0 Φ 1 := by
      intro j; rw [hw]; ring
    rw [tsum_congr hrw, h1.tsum_add h2, tsum_mul_right]
    rfl
  rw [← heq, hsplit]

/-- **Lemma `lem:tel`, \eqref{eq:solved}, first half.** -/
theorem G_one_solved (hq : ‖q‖ < 1) (hs : s0 + th = 1)
    (hΦ : Summable fun n => ‖Φ n‖) (hc : ∀ n, ‖c n‖ ≤ Cc)
    (hsec : SectionId q s0 th c Φ) (ha : aFrak q s0 th 1 ≠ 1) :
    G q s0 Φ 1 = cFrak q s0 th c 1 / (1 - aFrak q s0 th 1) := by
  have h := G_eq hq hs hΦ hc hsec 1
  have hne : (1 : ℂ) - aFrak q s0 th 1 ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha)
  field_simp
  linear_combination h

/-- **Lemma `lem:tel`, \eqref{eq:solved}, second half.** -/
theorem G_solved (hq : ‖q‖ < 1) (hs : s0 + th = 1)
    (hΦ : Summable fun n => ‖Φ n‖) (hc : ∀ n, ‖c n‖ ≤ Cc)
    (hsec : SectionId q s0 th c Φ) (ha : aFrak q s0 th 1 ≠ 1) (k : ℕ) :
    G q s0 Φ k
      = cFrak q s0 th c k + aFrak q s0 th k * (cFrak q s0 th c 1 / (1 - aFrak q s0 th 1)) := by
  rw [← G_one_solved hq hs hΦ hc hsec ha]
  exact G_eq hq hs hΦ hc hsec k

/-! ## The two instances -/

/-- `\alpha_k = 2q^{k+1}/(1-q^{k+1})`. -/
def alphaSeq (q : ℂ) (k : ℕ) : ℂ := 2 * q ^ (k + 1) / (1 - q ^ (k + 1))

/-- `\gamma_k = -2q^{k+1}(1-q)/[(1-q^{k+1})(1-q^{k+2})]`. -/
def gammaSeq (q : ℂ) (k : ℕ) : ℂ :=
  -(2 * q ^ (k + 1) * (1 - q)) / ((1 - q ^ (k + 1)) * (1 - q ^ (k + 2)))

/-- `A_k = 2q/(1-q^{k+1})`. -/
def ASeq (q : ℂ) (k : ℕ) : ℂ := 2 * q / (1 - q ^ (k + 1))

/-- `C_k = q\gamma_k`. -/
def CSeq (q : ℂ) (k : ℕ) : ℂ := q * gammaSeq q k

/-- Bulk instance `(s_0,\vartheta) = (1,0)`: `a_k = \alpha_k`. -/
theorem aTel_bulk (q : ℂ) (k : ℕ) : aTel q 1 0 k = alphaSeq q k := by
  unfold aTel alphaSeq
  norm_num

/-- Bulk instance `(s_0,\vartheta) = (1,0)`: `b_k = \gamma_k`. -/
theorem bTel_bulk (hq : ‖q‖ < 1) (k : ℕ) : bTel q 0 k = gammaSeq q k := by
  have h1 : (1 : ℂ) - q ^ (k + 1) ≠ 0 := den_ne_zero hq k
  have h2 : (1 : ℂ) - q ^ (k + 2) ≠ 0 := den_ne_zero hq (k + 1)
  unfold bTel gammaSeq
  rw [show (0 : ℕ) + k + 2 = k + 2 by ring, show (0 : ℕ) + k + 1 = k + 1 by ring]
  field_simp
  ring

/-- Travel instance `(s_0,\vartheta) = (0,1)`: `a_k = A_k`. -/
theorem aTel_travel (q : ℂ) (k : ℕ) : aTel q 0 1 k = ASeq q k := by
  unfold aTel ASeq
  norm_num

/-- Travel instance `(s_0,\vartheta) = (0,1)`: `b_k = C_k`. -/
theorem bTel_travel (hq : ‖q‖ < 1) (k : ℕ) : bTel q 1 k = CSeq q k := by
  have h1 : (1 : ℂ) - q ^ (k + 1) ≠ 0 := den_ne_zero hq k
  have h2 : (1 : ℂ) - q ^ (k + 2) ≠ 0 := den_ne_zero hq (k + 1)
  unfold bTel CSeq gammaSeq
  rw [show (1 : ℕ) + k + 2 = k + 3 by ring, show (1 : ℕ) + k + 1 = k + 2 by ring]
  field_simp
  ring

/-! ## The same, for a `\Phi` given as an element of the `\ell^1` space of `MobiusL1.lean` -/

/-- **Lemma `lem:tel`, \eqref{eq:threeterm}, for `\Phi \in \ell^1`.** -/
theorem l1_three_term (hq : ‖q‖ < 1) (hs : s0 + th = 1) (Ψ : MobiusL1.ell1)
    (hc : ∀ n, ‖c n‖ ≤ Cc) (hsec : SectionId q s0 th c (fun n => Ψ n)) (k : ℕ) :
    G q s0 (fun n => Ψ n) k
      = CC q s0 th c k + aTel q s0 th k * G q s0 (fun n => Ψ n) 1
        + bTel q th k * G q s0 (fun n => Ψ n) (k + 2) :=
  three_term hq hs (MobiusL1.summable_norm Ψ) hc hsec k

/-- **Lemma `lem:tel`, telescoped, for `\Phi \in \ell^1`.** -/
theorem l1_G_eq (hq : ‖q‖ < 1) (hs : s0 + th = 1) (Ψ : MobiusL1.ell1)
    (hc : ∀ n, ‖c n‖ ≤ Cc) (hsec : SectionId q s0 th c (fun n => Ψ n)) (k : ℕ) :
    G q s0 (fun n => Ψ n) k
      = cFrak q s0 th c k + aFrak q s0 th k * G q s0 (fun n => Ψ n) 1 :=
  G_eq hq hs (MobiusL1.summable_norm Ψ) hc hsec k

end

end Telescope

#print axioms Telescope.norm_bTel_le
#print axioms Telescope.norm_aTel_le
#print axioms Telescope.norm_CC_le
#print axioms Telescope.norm_G_le
#print axioms Telescope.row_sum
#print axioms Telescope.three_term
#print axioms Telescope.summable_bProd_norm
#print axioms Telescope.summable_bProd
#print axioms Telescope.tendsto_bProd
#print axioms Telescope.summable_aFrak
#print axioms Telescope.summable_cFrak
#print axioms Telescope.G_eq
#print axioms Telescope.G_one_solved
#print axioms Telescope.G_solved
#print axioms Telescope.aTel_bulk
#print axioms Telescope.bTel_bulk
#print axioms Telescope.aTel_travel
#print axioms Telescope.bTel_travel
#print axioms Telescope.l1_three_term
#print axioms Telescope.l1_G_eq
