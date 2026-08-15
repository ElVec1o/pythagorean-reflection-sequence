/-
  SectionLadders.lean
  ===================
  Proposition `prop:travelsum` (the travel `k`-sum telescopes) and Proposition
  `prop:bulkdress` (the bulk dressing) of `paper/journal/paper2.tex`, section 5.2, both of
  which are Lemma `lem:tel` (`Telescope.lean`) evaluated at a geometric source.

  The paper states both "as meromorphic functions on `|q| < 1`", proving them first for
  `|q| < 1/3`, where Lemma `lem:modelexist` supplies the `\ell^1` solution, and then extending
  by analytic continuation.  The continuation is not needed for the identity itself: what
  `Telescope.G_eq` proves is that *any* `\ell^1` solution of the section identity satisfies
  `G_k = \mathfrak c_k + \mathfrak a_kG_1` on the whole of `\|q\| < 1`.  So the statements below
  are the propositions with the existence of the solution carried as a hypothesis, which is
  where the paper's `|q| < 1/3` restriction lives, and with no continuation step.  What is
  formalised is therefore the implication, not the existence; `lem:modelexist` is a separate
  statement and is not formalised here.

  The three source evaluations are the whole of the arithmetic:

  * `CC_travel`   `(s_0,\vartheta) = (0,1)`, `c \equiv 1`: `\mathcal C_k = 2q/(1-q^{k+1}) = A_k`;
  * `CC_bulk`     `(s_0,\vartheta) = (1,0)`, `c \equiv 1`:
                  `\mathcal C_k = 2q^{k+1}/(1-q^{k+1}) = \alpha_k`;
  * `CC_bulk_geo` `(s_0,\vartheta) = (1,0)`, `c_s = q^s`: `\mathcal C_k = \alpha_{k+1}`,
                  which is what turns `\mathfrak c_k` into the third ladder `T_k`.

  No `sorry`.
-/

import Telescope

namespace SectionLadders

open Telescope Filter Finset

noncomputable section

variable {q : ℂ}

/-! ## The three ladders of \eqref{eq:krec} and \eqref{eq:Tladder} -/

/-- `S_k`, the bulk ladder: `\mathfrak a_k` at `(s_0,\vartheta) = (1,0)`. -/
def Sladder (q : ℂ) (k : ℕ) : ℂ := aFrak q 1 0 k

/-- `\Sigma_k`, the travel ladder: `\mathfrak a_k` at `(s_0,\vartheta) = (0,1)`. -/
def SigmaLadder (q : ℂ) (k : ℕ) : ℂ := aFrak q 0 1 k

/-- `T_k = \sum_{j\ge0}\alpha_{k+2j+1}\prod_{i<j}\gamma_{k+2i}`, the third ladder
\eqref{eq:Tladder}. -/
def Tladder (q : ℂ) (k : ℕ) : ℂ := ∑' j, alphaSeq q (k + 2 * j + 1) * bProd q 0 k j

/-- `S_k` is the ladder of \eqref{eq:krec}: `\alpha` against `\gamma`. -/
theorem Sladder_eq (hq : ‖q‖ < 1) (k : ℕ) :
    Sladder q k = ∑' j, alphaSeq q (k + 2 * j) * ∏ i ∈ range j, gammaSeq q (k + 2 * i) := by
  unfold Sladder aFrak bProd
  refine tsum_congr (fun j => ?_)
  rw [aTel_bulk]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => bTel_bulk hq _)

/-- `\Sigma_k` is the ladder of \eqref{eq:krec}: `A` against `C`. -/
theorem SigmaLadder_eq (hq : ‖q‖ < 1) (k : ℕ) :
    SigmaLadder q k = ∑' j, ASeq q (k + 2 * j) * ∏ i ∈ range j, CSeq q (k + 2 * i) := by
  unfold SigmaLadder aFrak bProd
  refine tsum_congr (fun j => ?_)
  rw [aTel_travel]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => bTel_travel hq _)

/-- `T_k` is the ladder \eqref{eq:Tladder}. -/
theorem Tladder_eq (hq : ‖q‖ < 1) (k : ℕ) :
    Tladder q k = ∑' j, alphaSeq q (k + 2 * j + 1) * ∏ i ∈ range j, gammaSeq q (k + 2 * i) := by
  unfold Tladder bProd
  refine tsum_congr (fun j => ?_)
  congr 1
  exact Finset.prod_congr rfl (fun i _ => bTel_bulk hq _)

/-! ## The geometric source sums -/

/-- The one geometric sum all three source evaluations reduce to. -/
theorem tsum_geom_shift (hq : ‖q‖ < 1) (C : ℂ) (e d : ℕ) :
    ∑' n : ℕ, C * q ^ (e + (d + 1) * n) = C * q ^ e / (1 - q ^ (d + 1)) := by
  have hQ : ‖q ^ (d + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero d)
  have hrw : ∀ n : ℕ, C * q ^ (e + (d + 1) * n) = (C * q ^ e) * (q ^ (d + 1)) ^ n := by
    intro n; rw [pow_add, ← pow_mul]; ring
  rw [tsum_congr hrw, tsum_mul_left, tsum_geometric_of_norm_lt_one hQ, div_eq_mul_inv]

/-- Travel instance, `c \equiv 1`: `\mathcal C_k = A_k = a_k`. -/
theorem CC_travel (hq : ‖q‖ < 1) (k : ℕ) :
    CC q 0 1 (fun _ => 1) k = aTel q 0 1 k := by
  have hrw : ∀ n : ℕ, q ^ (k * (n + 0)) * (eCo q 0 1 n * 1) = 2 * q ^ (1 + (k + 1) * n) := by
    intro n
    unfold eCo
    calc q ^ (k * (n + 0)) * (2 * q ^ (1 + (n + 0)) * 1)
        = 2 * q ^ (k * (n + 0) + (1 + (n + 0))) := by rw [pow_add]; ring
      _ = 2 * q ^ (1 + (k + 1) * n) := by congr 2; ring
  unfold CC
  rw [tsum_congr hrw, tsum_geom_shift hq 2 1 k]
  unfold aTel
  norm_num

/-- Bulk instance, `c \equiv 1`: `\mathcal C_k = \alpha_k = a_k`. -/
theorem CC_bulk (hq : ‖q‖ < 1) (k : ℕ) :
    CC q 1 0 (fun _ => 1) k = aTel q 1 0 k := by
  have hrw : ∀ n : ℕ, q ^ (k * (n + 1)) * (eCo q 1 0 n * 1) = 2 * q ^ ((k + 1) + (k + 1) * n) := by
    intro n
    unfold eCo
    calc q ^ (k * (n + 1)) * (2 * q ^ (0 + (n + 1)) * 1)
        = 2 * q ^ (k * (n + 1) + (0 + (n + 1))) := by rw [pow_add]; ring
      _ = 2 * q ^ ((k + 1) + (k + 1) * n) := by congr 2; ring
  unfold CC
  rw [tsum_congr hrw, tsum_geom_shift hq 2 (k + 1) k]
  unfold aTel
  norm_num

/-- Bulk instance, `c_s = q^s`: `\mathcal C_k = \alpha_{k+1}`. -/
theorem CC_bulk_geo (hq : ‖q‖ < 1) (k : ℕ) :
    CC q 1 0 (fun n => q ^ (n + 1)) k = aTel q 1 0 (k + 1) := by
  have hrw : ∀ n : ℕ,
      q ^ (k * (n + 1)) * (eCo q 1 0 n * q ^ (n + 1)) = 2 * q ^ ((k + 2) + (k + 2) * n) := by
    intro n
    unfold eCo
    calc q ^ (k * (n + 1)) * (2 * q ^ (0 + (n + 1)) * q ^ (n + 1))
        = 2 * q ^ (k * (n + 1) + (0 + (n + 1)) + (n + 1)) := by rw [pow_add, pow_add]; ring
      _ = 2 * q ^ ((k + 2) + (k + 2) * n) := by congr 2; ring
  unfold CC
  rw [tsum_congr hrw, tsum_geom_shift hq 2 (k + 2) (k + 1)]
  unfold aTel
  norm_num

/-! ## The two ladders coincide at a constant source -/

theorem cFrak_travel (hq : ‖q‖ < 1) (k : ℕ) :
    cFrak q 0 1 (fun _ => 1) k = SigmaLadder q k := by
  unfold cFrak SigmaLadder aFrak
  exact tsum_congr (fun j => by rw [CC_travel hq])

theorem cFrak_bulk (hq : ‖q‖ < 1) (k : ℕ) :
    cFrak q 1 0 (fun _ => 1) k = Sladder q k := by
  unfold cFrak Sladder aFrak
  exact tsum_congr (fun j => by rw [CC_bulk hq])

theorem cFrak_bulk_geo (hq : ‖q‖ < 1) (k : ℕ) :
    cFrak q 1 0 (fun n => q ^ (n + 1)) k = Tladder q k := by
  unfold cFrak Tladder
  refine tsum_congr (fun j => ?_)
  rw [CC_bulk_geo hq, aTel_bulk]

/-! ## Proposition `prop:travelsum` -/

/-- **Proposition `prop:travelsum`.**  If `\Phi \in \ell^1` solves the travel section identity,
`(s_0,\vartheta,\mathbf c) = (0,1,\mathbf 1)`, and `\Sigma_1 \ne 1`, then
`G^T_k = \Sigma_k/(1-\Sigma_1)` for every `k`.  In particular at `k = 0`,
`\sum_{s\ge0}\Phi_s = \Sigma_0/(1-\Sigma_1)`. -/
theorem travelsum {Φ : ℕ → ℂ} (hq : ‖q‖ < 1) (hΦ : Summable fun n => ‖Φ n‖)
    (hsec : SectionId q 0 1 (fun _ => 1) Φ) (ha : SigmaLadder q 1 ≠ 1) (k : ℕ) :
    G q 0 Φ k = SigmaLadder q k / (1 - SigmaLadder q 1) := by
  have hc : ∀ n : ℕ, ‖(1 : ℂ)‖ ≤ 1 := fun _ => by simp
  have ha' : aFrak q 0 1 1 ≠ 1 := ha
  have hne : (1 : ℂ) - SigmaLadder q 1 ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha)
  have h1 : G q 0 Φ 1 = SigmaLadder q 1 / (1 - SigmaLadder q 1) := by
    rw [G_one_solved hq (by norm_num) hΦ hc hsec ha', cFrak_travel hq]
    rfl
  have hk := G_eq hq (by norm_num : (0 : ℕ) + 1 = 1) hΦ hc hsec k
  rw [cFrak_travel hq] at hk
  rw [hk, h1]
  show SigmaLadder q k + SigmaLadder q k * (SigmaLadder q 1 / (1 - SigmaLadder q 1))
      = SigmaLadder q k / (1 - SigmaLadder q 1)
  field_simp
  ring

/-! ## Proposition `prop:bulkdress` -/

/-- **Proposition `prop:bulkdress`, the source `\mathbf c = \mathbf 1`.**
`b_0 = \sum_{s\ge1}\Phi_s = S_0/(1-S_1)` and `t_0 = \sum_{s\ge1}q^s\Phi_s = S_1/(1-S_1)`. -/
theorem bulkdress_b0_t0 {Φ : ℕ → ℂ} (hq : ‖q‖ < 1) (hΦ : Summable fun n => ‖Φ n‖)
    (hsec : SectionId q 1 0 (fun _ => 1) Φ) (ha : Sladder q 1 ≠ 1) :
    G q 1 Φ 0 = Sladder q 0 / (1 - Sladder q 1)
      ∧ G q 1 Φ 1 = Sladder q 1 / (1 - Sladder q 1) := by
  have hc : ∀ n : ℕ, ‖(1 : ℂ)‖ ≤ 1 := fun _ => by simp
  have ha' : aFrak q 1 0 1 ≠ 1 := ha
  have hne : (1 : ℂ) - Sladder q 1 ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha)
  have h1 : G q 1 Φ 1 = Sladder q 1 / (1 - Sladder q 1) := by
    rw [G_one_solved hq (by norm_num) hΦ hc hsec ha', cFrak_bulk hq]
    rfl
  refine ⟨?_, h1⟩
  have hk := G_eq hq (by norm_num : (1 : ℕ) + 0 = 1) hΦ hc hsec 0
  rw [cFrak_bulk hq] at hk
  rw [hk, h1]
  show Sladder q 0 + Sladder q 0 * (Sladder q 1 / (1 - Sladder q 1))
      = Sladder q 0 / (1 - Sladder q 1)
  field_simp
  ring

/-- **Proposition `prop:bulkdress`, the source `c_s = q^s`.**
`t_1 = \sum_{s\ge1}q^s\Psi_s = T_1/(1-S_1)` and
`b_1 = \sum_{s\ge1}\Psi_s = T_0 + S_0T_1/(1-S_1)`. -/
theorem bulkdress_t1_b1 {Ψ : ℕ → ℂ} (hq : ‖q‖ < 1) (hΨ : Summable fun n => ‖Ψ n‖)
    (hsec : SectionId q 1 0 (fun n => q ^ (n + 1)) Ψ) (ha : Sladder q 1 ≠ 1) :
    G q 1 Ψ 1 = Tladder q 1 / (1 - Sladder q 1)
      ∧ G q 1 Ψ 0 = Tladder q 0 + Sladder q 0 * (Tladder q 1 / (1 - Sladder q 1)) := by
  have hc : ∀ n : ℕ, ‖q ^ (n + 1)‖ ≤ 1 := fun n => norm_pow_le_one hq.le _
  have ha' : aFrak q 1 0 1 ≠ 1 := ha
  have h1 : G q 1 Ψ 1 = Tladder q 1 / (1 - Sladder q 1) := by
    rw [G_one_solved hq (by norm_num) hΨ hc hsec ha', cFrak_bulk_geo hq]
    rfl
  refine ⟨h1, ?_⟩
  have hk := G_eq hq (by norm_num : (1 : ℕ) + 0 = 1) hΨ hc hsec 0
  rw [cFrak_bulk_geo hq] at hk
  rw [hk, h1]
  rfl

/-! ## The first "equivalently" clause of Proposition `prop:recip` -/

/-- The scalar form: with `S_e = 1 - S_1 \ne 0`, the reciprocity `t_0 = b_1` written through the
dressing of Proposition `prop:bulkdress` is exactly `T_0S_e + T_1S_0 = S_1`. -/
theorem recip_ladder_iff (S0 S1 T0 T1 : ℂ) (h : (1 : ℂ) - S1 ≠ 0) :
    S1 / (1 - S1) = T0 + S0 * (T1 / (1 - S1)) ↔ T0 * (1 - S1) + T1 * S0 = S1 := by
  constructor
  · intro hh
    field_simp at hh
    first
      | linear_combination hh
      | linear_combination -hh
  · intro hh
    field_simp
    first
      | linear_combination hh
      | linear_combination -hh

/-- **Proposition `prop:recip`, the clause "equivalently `T_0S_e + T_1S_0 = S_1`".**  Given the
two bulk solutions of Proposition `prop:bulkdress`, the reciprocity `t_0 = b_1` and the ladder
identity `T_0S_e + T_1S_0 = S_1` are the same statement.  The reciprocity itself is proved in
`Reciprocity.lean` (`t0_eq_b1`); it is a hypothesis here, not a conclusion. -/
theorem recip_ladder {Φ Ψ : ℕ → ℂ} (hq : ‖q‖ < 1)
    (hΦ : Summable fun n => ‖Φ n‖) (hsecΦ : SectionId q 1 0 (fun _ => 1) Φ)
    (hΨ : Summable fun n => ‖Ψ n‖) (hsecΨ : SectionId q 1 0 (fun n => q ^ (n + 1)) Ψ)
    (ha : Sladder q 1 ≠ 1) :
    G q 1 Φ 1 = G q 1 Ψ 0
      ↔ Tladder q 0 * (1 - Sladder q 1) + Tladder q 1 * Sladder q 0 = Sladder q 1 := by
  have hne : (1 : ℂ) - Sladder q 1 ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha)
  rw [(bulkdress_b0_t0 hq hΦ hsecΦ ha).2, (bulkdress_t1_b1 hq hΨ hsecΨ ha).2]
  exact recip_ladder_iff _ _ _ _ hne

end

end SectionLadders

#print axioms SectionLadders.Sladder_eq
#print axioms SectionLadders.SigmaLadder_eq
#print axioms SectionLadders.Tladder_eq
#print axioms SectionLadders.tsum_geom_shift
#print axioms SectionLadders.CC_travel
#print axioms SectionLadders.CC_bulk
#print axioms SectionLadders.CC_bulk_geo
#print axioms SectionLadders.cFrak_travel
#print axioms SectionLadders.cFrak_bulk
#print axioms SectionLadders.cFrak_bulk_geo
#print axioms SectionLadders.travelsum
#print axioms SectionLadders.bulkdress_b0_t0
#print axioms SectionLadders.bulkdress_t1_b1
#print axioms SectionLadders.recip_ladder_iff
#print axioms SectionLadders.recip_ladder
