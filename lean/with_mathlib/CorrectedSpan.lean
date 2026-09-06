/-
  CorrectedSpan.lean
  ==================
  The repair BLOCK 343 specified, done ADDITIVELY.

  `wordLength g = lR g + 2 * c g` is false as formalized: `LipschitzPotential`
  `not_metric_identity` and `TrueLengthUpper.not_isTrueLength_wordLength_c` refute it, at
  the identity element, because `lR one = 2` while `wordLength one = 0`.

  Root cause (BLOCK 343): `Elt.occ := insert 0 (...)` forces edge `0` into every span, so
  `PathData` inherits `hA : A <= 0` and `hB : 0 <= B` and `lR` always charges `mu 0`.  For
  a walk that never crosses edge `0` -- the identity being the extreme case -- `mu 0 = 2`
  is charged for an edge the walk never uses.  `nogap/src/main.rs` instead requires only
  that SITE `0` be in range, i.e. `B >= -1`, so its span may be empty.

  BLOCK 343's stated repair was to weaken the field to `hB : -1 <= B`.  That is invasive:
  it falsifies `pdWidth_pos : 0 < pdWidth P` (an empty span has width `0`) and cascades
  through the `Fin (pdWidth P)` edge type that the whole shield-law development is built
  on -- ~21k lines.

  This file takes the additive route instead, which is available because **`mu` and
  `siteCost` do not depend on `A` or `B`**: they are functions of `kstar`, `d`, `eps`,
  `delta` alone (see `SiteCost.PathData.mu`, `siteCost` in `Realisation.lean`).  So the
  corrected length is the SAME summand summed over the corrected range, and can be defined
  without touching `PathData`.  Nothing existing breaks; `lR` keeps its meaning and the
  shield-law work stands unchanged.

  No `sorry`.
-/

import EltBridge

namespace CorrectedSpan

open EltBridge SiteCost

variable (g : EltBridge.Elt)

/-- The genuinely occupied edges -- `Elt.occ` WITHOUT the forced `insert 0`.  May be
empty, which is exactly the case the current formalization cannot express. -/
noncomputable def occTrue : Finset ℤ :=
  g.supp.filter (fun j => g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0)

/-- Left end of the corrected span; `0` when nothing is occupied. -/
noncomputable def ATrue : ℤ :=
  if h : (occTrue g).Nonempty then (occTrue g).min' h else 0

/-- Right end of the corrected span; `-1` when nothing is occupied, so that the edge
range `Icc ATrue BTrue` is EMPTY and the site range `Icc ATrue (BTrue + 1)` is the single
site `0` -- matching `main.rs`, which requires only site `0` to be in range. -/
noncomputable def BTrue : ℤ :=
  if h : (occTrue g).Nonempty then (occTrue g).max' h else -1

/-- **The corrected relaxed length.**  Same summands as `SiteCost.PathData.lR`, summed
over the corrected span. -/
noncomputable def lRTrue : ℕ :=
  (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j)
    + ∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s

/-! ### The identity element, where the old definition failed -/

theorem occTrue_one : occTrue EltBridge.Elt.one = ∅ := by
  unfold occTrue
  simp [EltBridge.Elt.one]

theorem ATrue_one : ATrue EltBridge.Elt.one = 0 := by
  unfold ATrue
  rw [dif_neg]
  rw [occTrue_one]
  simp

theorem BTrue_one : BTrue EltBridge.Elt.one = -1 := by
  unfold BTrue
  rw [dif_neg]
  rw [occTrue_one]
  simp

/-- **The corrected length of the identity is `0`**, where the old `lR` gave `2`.  This is
the repair working: `wordLength one = 0`, so the metric identity now holds at the point
where `not_metric_identity` refuted it. -/
theorem siteCost_one_zero : EltBridge.Elt.one.toPathData.siteCost 0 = 0 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.one]

theorem lRTrue_one : lRTrue EltBridge.Elt.one = 0 := by
  unfold lRTrue
  rw [ATrue_one, BTrue_one]
  norm_num [siteCost_one_zero]


/-! ### The corrected defect

`pdCutSites` misses one site that `main.rs` counts: the boundary shield.  Its firing
condition was characterised and machine-checked (140/140, BLOCK 343): `kstar = 0`,
`eps = +1`, `delta = false`, no deposit at any edge `<= 0`, and some deposit at an edge
`>= 1`.  Deleting it from the Rust tool costs 28 `M4b` violations at depth 20, so it is
load-bearing, not decoration. -/

open Classical in
/-- `main.rs`'s boundary-shield condition. -/
def ShieldFires : Prop :=
  g.kstar = 0 ∧ g.eps = 1 ∧ g.delta = false ∧
    (∀ j : ℤ, j ≤ 0 → g.d j = 0) ∧ (∃ j : ℤ, 1 ≤ j ∧ g.d j ≠ 0)

open Classical in
/-- **The corrected defect**: cut sites interior to the CORRECTED span, plus the boundary
shield when it fires. -/
noncomputable def cTrue : ℕ :=
  ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card
    + (if ShieldFires g then 1 else 0)

theorem not_shieldFires_one : ¬ ShieldFires EltBridge.Elt.one := by
  rintro ⟨-, -, -, -, ⟨j, -, hj⟩⟩
  exact hj (by simp [EltBridge.Elt.one])

theorem cTrue_one : cTrue EltBridge.Elt.one = 0 := by
  unfold cTrue
  rw [ATrue_one, BTrue_one, if_neg not_shieldFires_one]
  norm_num

/-- **The metric identity holds at the identity element, with the corrected definitions.**
This is exactly the point at which `LipschitzPotential.not_metric_identity` and
`TrueLengthUpper.not_isTrueLength_wordLength_c` refute the uncorrected statement
(`wordLength one = 0` but `lR one = 2`).  With the corrected span and defect both sides
are `0`. -/
theorem metric_identity_one :
    EltBridge.Elt.wordLength EltBridge.Elt.one
      = lRTrue EltBridge.Elt.one + 2 * cTrue EltBridge.Elt.one := by
  rw [EltBridge.Elt.wordLength_one, lRTrue_one, cTrue_one]

end CorrectedSpan

#print axioms CorrectedSpan.occTrue_one
#print axioms CorrectedSpan.ATrue_one
#print axioms CorrectedSpan.BTrue_one
#print axioms CorrectedSpan.siteCost_one_zero
#print axioms CorrectedSpan.lRTrue_one
#print axioms CorrectedSpan.not_shieldFires_one
#print axioms CorrectedSpan.cTrue_one
#print axioms CorrectedSpan.metric_identity_one
