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
import TrueLengthUpper

namespace CorrectedSpan

open EltBridge SiteCost

variable (g : EltBridge.Elt)

/-- The genuinely occupied edges -- `Elt.occ` WITHOUT the forced `insert 0`.  May be
empty, which is exactly the case the current formalization cannot express. -/
noncomputable def occTrue : Finset ℤ :=
  g.supp.filter (fun j => g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0)

/-- Left end of the corrected span.  Clamped at `0`: `main.rs` requires SITE `0` to lie
in the site range `[A, B+1]`, i.e. `A <= 0 <= B + 1`, so the span is the occupied range
EXTENDED to reach site `0` -- not the raw occupied range.  Getting this wrong drops site
`0` for elements occupying only positive edges. -/
noncomputable def ATrue : ℤ :=
  if h : (occTrue g).Nonempty then min 0 ((occTrue g).min' h) else 0

/-- Right end of the corrected span, clamped at `-1` for the same reason.  When nothing
is occupied this gives `A = 0`, `B = -1`, so the edge range `Icc 0 (-1)` is EMPTY and the
site range `Icc 0 0` is the single site `0` -- matching `main.rs`. -/
noncomputable def BTrue : ℤ :=
  if h : (occTrue g).Nonempty then max (-1) ((occTrue g).max' h) else -1

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


/-! ### `gBad`, the element that broke the old definitions

`TrueLengthUpper` found `gBad` (`kstar = 0`, `d 1 = 2`): `lR = 8`, `Elt.c = 0`, and
`Reaches 10`, so the OLD upper bound `wordLength <= lR + 2c` reads `10 <= 8` and fails.
With the corrected span and defect the two sides agree exactly. -/

theorem occTrue_gBad : occTrue EltBridge.Elt.gBad = {1} := by
  unfold occTrue
  ext j
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, -⟩
    simpa [EltBridge.Elt.gBad] using hj
  · rintro rfl
    exact ⟨by simp [EltBridge.Elt.gBad], by simp [EltBridge.Elt.gBad]⟩

theorem ATrue_gBad : ATrue EltBridge.Elt.gBad = 0 := by
  unfold ATrue
  rw [dif_pos (by rw [occTrue_gBad]; exact ⟨1, by simp⟩)]
  simp [occTrue_gBad]

theorem BTrue_gBad : BTrue EltBridge.Elt.gBad = 1 := by
  unfold BTrue
  rw [dif_pos (by rw [occTrue_gBad]; exact ⟨1, by simp⟩)]
  simp [occTrue_gBad]

theorem shieldFires_gBad : ShieldFires EltBridge.Elt.gBad := by
  refine ⟨rfl, rfl, rfl, ?_, ⟨1, le_refl 1, ?_⟩⟩
  · intro j hj
    have : j ≠ 1 := by omega
    simp [EltBridge.Elt.gBad, this]
  · simp [EltBridge.Elt.gBad]


theorem gBad_mu0 : EltBridge.Elt.gBad.toPathData.mu 0 = 2 := by
  unfold SiteCost.PathData.mu
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad, SiteCost.travel_of_kstar_zero]

theorem gBad_mu1 : EltBridge.Elt.gBad.toPathData.mu 1 = 2 := by
  unfold SiteCost.PathData.mu
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad, SiteCost.travel_of_kstar_zero]

theorem gBad_site0 : EltBridge.Elt.gBad.toPathData.siteCost 0 = 0 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad]

theorem gBad_site1 : EltBridge.Elt.gBad.toPathData.siteCost 1 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad]

theorem gBad_site2 : EltBridge.Elt.gBad.toPathData.siteCost 2 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad]

/-- **The corrected relaxed length of `gBad` is `8`.** -/
theorem lRTrue_gBad : lRTrue EltBridge.Elt.gBad = 8 := by
  unfold lRTrue
  rw [ATrue_gBad, BTrue_gBad]
  have h1 : Finset.Icc (0 : ℤ) 1 = ({0, 1} : Finset ℤ) := by decide
  have h2 : Finset.Icc (0 : ℤ) (1 + 1) = ({0, 1, 2} : Finset ℤ) := by decide
  rw [h1, h2]
  simp [gBad_mu0, gBad_mu1, gBad_site0, gBad_site1, gBad_site2]

/-- **The corrected defect of `gBad` is `1`** -- the boundary shield, which `pdCutSites`
misses entirely (`gBad_cutSites : pdCutSites gBad.toPathData = empty`). -/
theorem cTrue_gBad : cTrue EltBridge.Elt.gBad = 1 := by
  unfold cTrue
  rw [ATrue_gBad, BTrue_gBad, if_pos shieldFires_gBad]
  have h : Finset.Ioo (0 : ℤ) (1 + 1) = ({1} : Finset ℤ) := by decide
  rw [h]
  have : ¬ EltBridge.Elt.gBad.toPathData.cut 1 := by
    unfold SiteCost.PathData.cut
    rw [not_and]
    intro _
    rw [not_and]
    intro hb
    exfalso
    revert hb
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, EltBridge.Elt.gBad]
  simp [Finset.filter_singleton, this]

/-- **The corrected identity is consistent at `gBad`**: `lRTrue + 2 * cTrue = 10`, and
`gBad` is reached in `10` steps.  Under the OLD definitions this read `8`, strictly less
than the reachable length -- the violation `TrueLengthUpper` found. -/
theorem gBad_corrected_total :
    lRTrue EltBridge.Elt.gBad + 2 * cTrue EltBridge.Elt.gBad = 10 := by
  rw [lRTrue_gBad, cTrue_gBad]

theorem wordLength_gBad_le_corrected :
    EltBridge.Elt.wordLength EltBridge.Elt.gBad
      ≤ lRTrue EltBridge.Elt.gBad + 2 * cTrue EltBridge.Elt.gBad := by
  rw [gBad_corrected_total]
  exact EltBridge.Elt.wordLength_le EltBridge.Elt.reaches_gBad

end CorrectedSpan

#print axioms CorrectedSpan.occTrue_one
#print axioms CorrectedSpan.ATrue_one
#print axioms CorrectedSpan.BTrue_one
#print axioms CorrectedSpan.siteCost_one_zero
#print axioms CorrectedSpan.lRTrue_one
#print axioms CorrectedSpan.not_shieldFires_one
#print axioms CorrectedSpan.cTrue_one
#print axioms CorrectedSpan.metric_identity_one
#print axioms CorrectedSpan.occTrue_gBad
#print axioms CorrectedSpan.ATrue_gBad
#print axioms CorrectedSpan.BTrue_gBad
#print axioms CorrectedSpan.shieldFires_gBad

#print axioms CorrectedSpan.gBad_mu0
#print axioms CorrectedSpan.gBad_mu1
#print axioms CorrectedSpan.gBad_site0
#print axioms CorrectedSpan.gBad_site1
#print axioms CorrectedSpan.gBad_site2
#print axioms CorrectedSpan.lRTrue_gBad
#print axioms CorrectedSpan.cTrue_gBad
#print axioms CorrectedSpan.gBad_corrected_total
#print axioms CorrectedSpan.wordLength_gBad_le_corrected