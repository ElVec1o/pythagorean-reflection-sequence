/-
**The `lR + 2c` potential is NOT 1-Lipschitz along the generators.**

The lower half of the metric identity `wordLength g = lR g + 2 * c g` is open.  One
proposed attack is a potential argument: define

    Phi g := g.toPathData.lR + 2 * Elt.c g

and prove `|Phi (s g) - Phi g| <= 1` for each generator `s`.  Induction on `Reaches`
(the shape of `reaches_lR_le`) would then give `wordLength g >= Phi g - Phi one`,
i.e. the open lower bound, sharp up to the base constant.

**This file refutes that attack, at the smallest possible witness.**  `s3 one` -- one
generator step from the identity -- moves `Phi` by exactly `3`:

    Phi one        = 2 + 2 * 0 = 2          (`one_toPathData_lR`, `c_one`)
    Phi (s3 one)   = 3 + 2 * 1 = 5          (`s3one_lR`, `c_s3one`)

while `wordLength (s3 one) <= 1`.  So `Phi` overshoots the word length by at least `4`
one step from the identity, and no additive constant repairs it: `Phi one` already
exceeds `wordLength one = 0` by `2`, in the opposite direction.

The mechanism, and it is not an accident of this witness: `SiteCost.PathData` carries
`hA : A <= 0` and `hB : 0 <= B`, which force the edge `0` into the span of EVERY
element.  For `s3 one` (`kstar = -1`, one deposit at edge `-1`) the walk never crosses
edge `0`, but the span contains it anyway, so

  * `mu 0 = 2` is added to `lR` (the "gap edge" clause), and
  * site `0` becomes INTERIOR to `Ioo A (B+1)`, so `pdCutSites` -- hence `Elt.c` --
    counts it, adding a further `2`.

Both corrections push the same way and neither is present at `one` itself, which is
why the very first `s3` step jumps by `3`.  The accompanying Rust probe
(`code/zeta_probe/tools/nogap/src/bin/lipschitz_check.rs`) measures `max |dPhi| = 3`
over a BFS ball of 3,336,511 elements (depth 30) and an exhaustive structural sweep of
8,299,908 elements, and finds `Phi g - wordLength g` ranging over `[-2, 4]`.

Nothing here contradicts `s1_lR_dist_le` / `s2_lR_dist_le` / `s3_lR_dist_le` /
`s3_c_dist_le`, all of which remain true: those bound the two pieces by `1`, `1`, `10`
and `2` separately.  The attack needed the two to CANCEL to `1`; they do not.
-/
import EltBridge

namespace LipschitzPotential

open EltBridge EltBridge.Elt SiteCost

/-- **The candidate potential.**  `Elt.lR` is `g.toPathData.lR` and `Elt.c` is
`(pdCutSites g.toPathData).card`, both already in `EltBridge`. -/
noncomputable def Phi (g : Elt) : ℕ := g.toPathData.lR + 2 * Elt.c g

/-- **The 1-Lipschitz hypothesis the potential attack needs**, for `s3`. -/
def IsOneLipschitzAtS3 : Prop := ∀ g : Elt, (Phi (s3 g) : ℤ) ≤ (Phi g : ℤ) + 1

/-! ### The identity -/

theorem one_occ : (one : Elt).occ = ({0} : Finset ℤ) := by
  classical
  unfold Elt.occ
  simp [one]

theorem one_A : (one : Elt).A = 0 := by
  classical
  unfold Elt.A
  simp [one_occ]

theorem one_B : (one : Elt).B = 0 := by
  classical
  unfold Elt.B
  simp [one_occ]

/-- **`Elt.c one = 0`.**  The identity's span is the single edge `0`, so the interior
site window `Ioo A (B+1) = Ioo 0 1` is empty and there is nothing to filter. -/
theorem c_one : Elt.c (one : Elt) = 0 := by
  classical
  unfold Elt.c
  rw [pdCutSites_card_eq_abs]
  have hA : (one : Elt).toPathData.A = 0 := one_A
  have hB : (one : Elt).toPathData.B = 0 := one_B
  rw [hA, hB]
  have hIoo : Finset.Ioo (0 : ℤ) (0 + 1) = (∅ : Finset ℤ) := by decide
  rw [hIoo, Finset.filter_empty, Finset.card_empty]

theorem Phi_one : Phi one = 2 := by
  unfold Phi
  rw [one_toPathData_lR, c_one]

/-! ### One `s3` step from the identity

`one.delta = false`, so `s3` takes its second branch: the cursor moves to `-1` and a
deposit of `+eps = +1` lands on the crossed edge `-1`. -/

private theorem one_delta_ne : ¬ ((one : Elt).delta = true) := by decide

theorem s3one_kstar : (s3 (one : Elt)).kstar = -1 := by
  have h : (s3 (one : Elt)).kstar = (one : Elt).kstar - 1 := by
    rw [s3, dif_neg one_delta_ne]
  rw [h]; rfl

theorem s3one_eps : (s3 (one : Elt)).eps = 1 := by
  have h : (s3 (one : Elt)).eps = (one : Elt).eps := by
    rw [s3, dif_neg one_delta_ne]
  rw [h]; rfl

theorem s3one_delta : (s3 (one : Elt)).delta = true := by
  rw [s3, dif_neg one_delta_ne]

theorem s3one_supp : (s3 (one : Elt)).supp = ({-1} : Finset ℤ) := by
  have h : (s3 (one : Elt)).supp = insert ((one : Elt).kstar - 1) (one : Elt).supp := by
    rw [s3, dif_neg one_delta_ne]
  rw [h]
  simp [one]

/-- The deposit function of `s3 one`: `1` at edge `-1`, `0` everywhere else. -/
theorem s3one_d (j : ℤ) : (s3 (one : Elt)).d j = if j = -1 then 1 else 0 := by
  have h : (s3 (one : Elt)).d
      = Function.update (one : Elt).d ((one : Elt).kstar - 1)
          ((one : Elt).d ((one : Elt).kstar - 1) + (one : Elt).eps) := by
    rw [s3, dif_neg one_delta_ne]
  have hk : (one : Elt).kstar - 1 = (-1 : ℤ) := by rfl
  rw [h, hk]
  by_cases hj : j = -1
  · subst hj
    simp [one]
  · rw [Function.update_of_ne hj]
    simp [one, hj]

/-- The travel indicator of `s3 one`: `-1` at edge `-1`, `0` everywhere else. -/
theorem s3one_travel (j : ℤ) :
    travel (s3 (one : Elt)).kstar j = if j = -1 then -1 else 0 := by
  rw [s3one_kstar]
  unfold travel
  by_cases hj : j = -1
  · subst hj; norm_num
  · split_ifs with h1 h2 <;> first | rfl | omega

theorem s3one_occ : (s3 (one : Elt)).occ = ({0, -1} : Finset ℤ) := by
  classical
  unfold Elt.occ
  rw [s3one_supp]
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩) <;> simp [h]
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨h, Or.inl ?_⟩
      rw [h, s3one_d]
      norm_num
theorem s3one_A : (s3 (one : Elt)).A = -1 := by
  classical
  have hmem : (s3 (one : Elt)).A ∈ (s3 (one : Elt)).occ := Finset.min'_mem _ _
  have hle : (s3 (one : Elt)).A ≤ -1 := by
    refine Finset.min'_le _ _ ?_
    rw [s3one_occ]; simp
  rw [s3one_occ] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem s3one_B : (s3 (one : Elt)).B = 0 := by
  classical
  have hmem : (s3 (one : Elt)).B ∈ (s3 (one : Elt)).occ := Finset.max'_mem _ _
  have hge : (0 : ℤ) ≤ (s3 (one : Elt)).B := Elt.zero_le_B _
  rw [s3one_occ] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/-! ### `lR` and `c` at `s3 one`

The span is `[-1, 0]`.  Edge `-1` carries the deposit and the travel step, so
`mu (-1) = 1`; edge `0` carries NEITHER, so `mu 0 = 2` -- yet `PathData.hB` puts it in
the span regardless.  All three site costs vanish. -/

private theorem s3one_mu_neg : (s3 (one : Elt)).toPathData.mu (-1) = 1 := by
  unfold SiteCost.PathData.mu
  have hd : (s3 (one : Elt)).toPathData.d (-1) = 1 := by
    have h := s3one_d (-1); simpa using h
  have ht : travel (s3 (one : Elt)).toPathData.kstar (-1) = -1 := by
    have h := s3one_travel (-1); simpa using h
  rw [hd, ht]
  norm_num

private theorem s3one_mu_zero : (s3 (one : Elt)).toPathData.mu 0 = 2 := by
  unfold SiteCost.PathData.mu
  have hd : (s3 (one : Elt)).toPathData.d 0 = 0 := by
    have h := s3one_d 0; simpa using h
  have ht : travel (s3 (one : Elt)).toPathData.kstar 0 = 0 := by
    have h := s3one_travel 0; simpa using h
  rw [hd, ht]
  norm_num

/-- `vL` vanishes identically at `s3 one`: its `delta` is `true`. -/
private theorem s3one_vL (s : ℤ) : (s3 (one : Elt)).toPathData.vL s = 0 := by
  unfold SiteCost.PathData.vL
  have : (s3 (one : Elt)).toPathData.delta = true := s3one_delta
  rw [this]
  rfl

private theorem s3one_alpha (s : ℤ) :
    (s3 (one : Elt)).toPathData.alphaAt s
      = (if s - 1 = -1 then 1 else 0) - (if s = 0 then 1 else 0) := by
  unfold SiteCost.PathData.alphaAt SiteCost.vArr
  rw [s3one_vL]
  have hd : (s3 (one : Elt)).toPathData.d (s - 1) = if s - 1 = -1 then 1 else 0 := by
    have h := s3one_d (s - 1); simpa using h
  rw [hd]
  push_cast
  ring

private theorem s3one_beta (s : ℤ) :
    (s3 (one : Elt)).toPathData.betaAt s
      = (if s = -1 then 1 else 0) - (if s = -1 then 1 else 0) := by
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
  have hδ : (s3 (one : Elt)).toPathData.delta = true := s3one_delta
  have he : (s3 (one : Elt)).toPathData.eps = 1 := s3one_eps
  have hk : (s3 (one : Elt)).toPathData.kstar = -1 := s3one_kstar
  have hd : (s3 (one : Elt)).toPathData.d s = if s = -1 then 1 else 0 := by
    have h := s3one_d s; simpa using h
  rw [hδ, he, hd, hk]
  by_cases hs : s = -1 <;> simp [hs]

private theorem s3one_siteCost (s : ℤ) : (s3 (one : Elt)).toPathData.siteCost s = 0 := by
  unfold SiteCost.PathData.siteCost
  rw [s3one_alpha, s3one_beta]
  by_cases hs : s = 0
  · subst hs; norm_num
  · by_cases hs1 : s - 1 = -1
    · omega
    · simp [hs, hs1]

/-- **`lR (s3 one) = 3`.**  `1` from edge `-1`, and `2` from the phantom edge `0` that
`PathData.hB` forces into the span. -/
theorem s3one_lR : (s3 (one : Elt)).toPathData.lR = 3 := by
  classical
  unfold SiteCost.PathData.lR
  have hA : (s3 (one : Elt)).toPathData.A = -1 := s3one_A
  have hB : (s3 (one : Elt)).toPathData.B = 0 := s3one_B
  rw [hA, hB]
  have hE : Finset.Icc (-1 : ℤ) 0 = ({-1, 0} : Finset ℤ) := by decide
  have hS : Finset.Icc (-1 : ℤ) (0 + 1) = ({-1, 0, 1} : Finset ℤ) := by decide
  rw [hE, hS]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [s3one_mu_neg, s3one_mu_zero, s3one_siteCost, s3one_siteCost, s3one_siteCost]
  norm_num

/-- **`Elt.c (s3 one) = 1`.**  The forced edge `0` makes site `0` interior, and site
`0` is a cut site: `alpha = beta = 0` and `PhiAt 0 = travel (-1) + 1 = 0`. -/
theorem c_s3one : Elt.c (s3 (one : Elt)) = 1 := by
  classical
  unfold Elt.c
  rw [pdCutSites_card_eq_abs]
  have hA : (s3 (one : Elt)).toPathData.A = -1 := s3one_A
  have hB : (s3 (one : Elt)).toPathData.B = 0 := s3one_B
  rw [hA, hB]
  have hIoo : Finset.Ioo (-1 : ℤ) (0 + 1) = ({0} : Finset ℤ) := by decide
  rw [hIoo]
  have hcut : (s3 (one : Elt)).toPathData.cut 0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [s3one_alpha]; norm_num
    · rw [s3one_beta]; ring
    · unfold SiteCost.PathData.PhiAt SiteCost.PathData.f SiteCost.vArr
      rw [s3one_vL]
      have ht : travel (s3 (one : Elt)).toPathData.kstar (0 - 1) = -1 := by
        have := s3one_travel (0 - 1); simpa using this
      rw [ht]
      norm_num
  rw [Finset.filter_true_of_mem (fun x hx => by
    rw [Finset.mem_singleton] at hx; rw [hx]; exact hcut)]
  exact Finset.card_singleton 0

theorem Phi_s3one : Phi (s3 (one : Elt)) = 5 := by
  unfold Phi
  rw [s3one_lR, c_s3one]

/-! ### The refutation -/

/-- **`Phi` jumps by exactly `3` on the first `s3` step.** -/
theorem Phi_s3one_sub_Phi_one : (Phi (s3 (one : Elt)) : ℤ) = (Phi one : ℤ) + 3 := by
  rw [Phi_s3one, Phi_one]
  norm_num

/-- **The potential attack fails.**  `Phi = lR + 2c` is not 1-Lipschitz along `s3`, so
the induction on `Reaches` that would give `wordLength g >= Phi g - Phi one` does not
run.  The witness is one generator step from the identity. -/
theorem not_isOneLipschitzAtS3 : ¬ IsOneLipschitzAtS3 := by
  intro h
  have := h one
  rw [Phi_s3one, Phi_one] at this
  norm_num at this

/-- **A fortiori: no constant `C` makes `Phi` `C`-Lipschitz with `C < 3`.** -/
theorem lipschitz_constant_ge_three (C : ℤ)
    (h : ∀ g : Elt, (Phi (s3 g) : ℤ) ≤ (Phi g : ℤ) + C) : 3 ≤ C := by
  have := h one
  rw [Phi_s3one, Phi_one] at this
  omega

/-! ### `Elt.c` is not the defect of the metric identity

`Elt.c` was introduced (BLOCK 326-328) as a candidate model for the uninterpreted `c`
of `IsTrueLength`.  It is not one: the identity `wordLength = lR + 2c` fails at `one`
itself, and fails by `4` one step away. -/

/-- `s3 one` is reached in one step, so its word length is at most `1`. -/
theorem wordLength_s3one_le : wordLength (s3 (one : Elt)) ≤ 1 :=
  wordLength_le (Reaches.step (Reaches.refl (SameElt.refl one))
    (Or.inr (Or.inr (SameElt.refl _))))

/-- **The metric identity fails for `Elt.c`, at the identity element.** `Phi one = 2`
but `wordLength one = 0`. -/
theorem not_metric_identity :
    ¬ (∀ g : Elt, Reachable g → wordLength g = g.toPathData.lR + 2 * Elt.c g) := by
  intro h
  have := h one reachable_one
  rw [wordLength_one, one_toPathData_lR, c_one] at this
  omega

/-- **And it fails by at least `4` one step from the identity**, so it is not an
artefact of the base point: `Phi (s3 one) = 5` while `wordLength (s3 one) <= 1`. -/
theorem Phi_overshoots_s3one :
    wordLength (s3 (one : Elt)) + 4 ≤ Phi (s3 (one : Elt)) := by
  have h := wordLength_s3one_le
  rw [Phi_s3one]
  omega

end LipschitzPotential

#print axioms LipschitzPotential.c_one
#print axioms LipschitzPotential.Phi_one
#print axioms LipschitzPotential.s3one_lR
#print axioms LipschitzPotential.c_s3one
#print axioms LipschitzPotential.Phi_s3one
#print axioms LipschitzPotential.Phi_s3one_sub_Phi_one
#print axioms LipschitzPotential.not_isOneLipschitzAtS3
#print axioms LipschitzPotential.lipschitz_constant_ge_three
#print axioms LipschitzPotential.wordLength_s3one_le
#print axioms LipschitzPotential.not_metric_identity
#print axioms LipschitzPotential.Phi_overshoots_s3one
