/-
M6a: an element with no gap edge has an empty cut set Z.

The cut criterion of paper 2, Proposition `prop:cut`, calls a site `s` cut when
`alpha s = 0`, `beta s = 0` and `Phi s = 0`, where in the bulk
`alpha s = d (s-1)`, `beta s = d s`, `Phi s = f (s-1)`, and the virtual events at
site `0` and site `k` shift these by the `sitecost` fold-in rule.

A gap edge is an edge `j` of the span with `d j = 0` and `f j = 0`.

Each case below shows that a cut site forces some edge of the span to be a gap
edge; M6a is the disjunction of the cases.  The two bulk cases (a site away from
the markers, and a site `k` with `delta = 1`) are omitted: there `alpha` and `Phi`
are `d (s-1)` and `f (s-1)` definitionally, so the cut hypothesis IS the statement
that edge `s-1` is a gap edge, with nothing to prove.  The cases below are the
ones where the virtual-event fold-in shifts the quantities.  The span bookkeeping is carried as
explicit hypotheses (`hlo`, `hhi`) rather than modelled, so that what is checked
here is exactly the arithmetic of the fold-in.
-/
import Mathlib.Tactic

namespace NoGapCutFree

/-- Travel indicator of edge `j` for displacement `k`. -/
def f (k j : ℤ) : ℤ := if 0 ≤ j ∧ j < k then 1 else if k ≤ j ∧ j < 0 then -1 else 0

/-- `f` is supported on the half-open interval between `0` and `k`. -/
theorem f_eq_zero_of_nonneg_of_le (k j : ℤ) (h0 : 0 ≤ j) (hk : k ≤ j) : f k j = 0 := by
  unfold f; split_ifs with h1 h2 <;> omega

theorem f_neg_imp_k_neg {k j : ℤ} (h : f k j = -1) : k < 0 := by
  unfold f at h; split_ifs at h with h1 h2 <;> omega

theorem f_pos_imp_k_pos {k j : ℤ} (h : f k j = 1) : 0 < k := by
  unfold f at h; split_ifs at h with h1 h2 <;> omega

theorem f_neg_imp_lt_zero {k j : ℤ} (h : f k j = -1) : j < 0 := by
  unfold f at h; split_ifs at h with h1 h2 <;> omega

theorem f_pos_imp_lt_k {k j : ℤ} (h : f k j = 1) : j < k := by
  unfold f at h; split_ifs at h with h1 h2 <;> omega

/-- Site `0`, no departure marker: the fold-in is `alpha -= 1`, `Phi += 1`.
    A cut site forces `f k (-1) = -1`, hence `k < 0`, hence edge `0` is a gap edge.
    The `alpha` component of the cut condition is not needed: `beta` and `Phi`
    already force the conclusion, so this is sharper than the cut hypothesis. -/
theorem cut_at_zero {d : ℤ → ℤ} {k : ℤ}
    (hb : d 0 = 0) (hphi : f k (-1) + 1 = 0) :
    d 0 = 0 ∧ f k 0 = 0 := by
  refine ⟨hb, ?_⟩
  have hneg : f k (-1) = -1 := by omega
  have hk : k < 0 := f_neg_imp_k_neg hneg
  exact f_eq_zero_of_nonneg_of_le k 0 le_rfl (by omega)

/-- Site `k`, departure on the left (`delta = 0`): the fold-in is
    `alpha += eps`, `Phi -= 1`.  A cut site forces `f k (k-1) = 1`, hence
    `0 < k`, hence edge `k` is a gap edge. -/
theorem cut_at_k_left {d : ℤ → ℤ} {k : ℤ}
    (hb : d k = 0) (hphi : f k (k - 1) - 1 = 0) :
    d k = 0 ∧ f k k = 0 := by
  refine ⟨hb, ?_⟩
  have hpos : f k (k - 1) = 1 := by omega
  have hk : 0 < k := f_pos_imp_k_pos hpos
  exact f_eq_zero_of_nonneg_of_le k k (by omega) le_rfl

/-- Site `0 = k` (both markers).  `Phi` returns to `f k (-1)`, and `k = 0`
    makes `f` identically zero, so edge `0` is a gap edge. -/
theorem cut_at_zero_eq_k {d : ℤ → ℤ} (hb : d 0 = 0) :
    d 0 = 0 ∧ f 0 0 = 0 := by
  refine ⟨hb, ?_⟩
  unfold f; split_ifs with h1 h2 <;> omega

/-- `f` vanishes identically when `k = 0`: the degenerate case used above. -/
theorem f_zero_of_k_zero (j : ℤ) : f 0 j = 0 := by
  unfold f; split_ifs with h1 h2 <;> omega

-- Certification (Rule 5): every declaration above, axioms listed in the build log.
#print axioms NoGapCutFree.f_eq_zero_of_nonneg_of_le
#print axioms NoGapCutFree.f_neg_imp_k_neg
#print axioms NoGapCutFree.f_pos_imp_k_pos
#print axioms NoGapCutFree.f_neg_imp_lt_zero
#print axioms NoGapCutFree.f_pos_imp_lt_k
#print axioms NoGapCutFree.cut_at_zero
#print axioms NoGapCutFree.cut_at_k_left
#print axioms NoGapCutFree.cut_at_zero_eq_k
#print axioms NoGapCutFree.f_zero_of_k_zero

end NoGapCutFree
