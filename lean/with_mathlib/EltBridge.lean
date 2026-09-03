/-
The `g -> configuration` bridge, first half.

`PathData` is the combinatorial object every result in the merge development is
stated about.  Nothing in the development produced one: `GroupElt.lean` carries lamp
configurations and travel but no group element, no word length, and no `lR`.  So the
statements below `M9` are all about configurations, and the qualifier is not
cosmetic -- there was no object a group element could be.

This file supplies the missing object.  An `Elt` is a lamp configuration with a
cursor and finite support -- exactly the data of a group element in the lamplighter
presentation -- and `toPathData` builds its `PathData`, computing the minimal span
`[A, B]` from the support.  The three span obligations `houter`, `hAmin`, `hBmin`
are the content: `A` and `B` must be *minimal*, not merely valid bounds.
-/
import Realisation
import Mathlib.Data.Finset.Max

namespace EltBridge

open SiteCost

/-- **A group element in lamp form**: a cursor `kstar`, a sign `eps`, a side `delta`,
and a finitely supported deposit function carrying the travel parity. -/
structure Elt where
  kstar : ℤ
  eps : ℤ
  delta : Bool
  heps : eps = 1 ∨ eps = -1
  d : ℤ → ℤ
  hpar : ∀ j, (d j - travel kstar j) % 2 = 0
  supp : Finset ℤ
  hsupp : ∀ j, j ∉ supp → d j = 0 ∧ travel kstar j = 0

namespace Elt

variable (g : Elt)

/-- The occupied edges, together with `0`.  Its min and max are the minimal span. -/
noncomputable def occ : Finset ℤ :=
  insert 0 (g.supp.filter (fun j => g.d j ≠ 0 ∨ travel g.kstar j ≠ 0))

theorem zero_mem_occ : (0 : ℤ) ∈ g.occ := Finset.mem_insert_self _ _

theorem occ_nonempty : g.occ.Nonempty := ⟨0, g.zero_mem_occ⟩

/-- An edge carrying a deposit or a travel step is in `occ`. -/
theorem mem_occ_of_ne (j : ℤ) (h : g.d j ≠ 0 ∨ travel g.kstar j ≠ 0) : j ∈ g.occ := by
  classical
  by_cases hj : j ∈ g.supp
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hj, h⟩)
  · rcases h with h | h
    · exact absurd (g.hsupp j hj).1 h
    · exact absurd (g.hsupp j hj).2 h

/-- The left end of the span. -/
noncomputable def A : ℤ := g.occ.min' g.occ_nonempty
/-- The right end of the span. -/
noncomputable def B : ℤ := g.occ.max' g.occ_nonempty

theorem A_le_zero : g.A ≤ 0 := Finset.min'_le _ _ g.zero_mem_occ
theorem zero_le_B : (0 : ℤ) ≤ g.B := Finset.le_max' _ _ g.zero_mem_occ

/-- **Outside the span there is neither deposit nor travel.** -/
theorem outer (j : ℤ) (h : j < g.A ∨ g.B < j) :
    g.d j = 0 ∧ travel g.kstar j = 0 := by
  by_contra hc
  have hne : g.d j ≠ 0 ∨ travel g.kstar j ≠ 0 := by
    rcases Decidable.em (g.d j = 0) with h1 | h1
    · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
    · exact Or.inl h1
  have hmem := g.mem_occ_of_ne j hne
  rcases h with h | h
  · have hle : g.A ≤ j := Finset.min'_le g.occ j hmem
    omega
  · have hle : j ≤ g.B := Finset.le_max' g.occ j hmem
    omega

/-- **`A` is minimal.** -/
theorem A_min : g.A = 0 ∨ g.d g.A ≠ 0 ∨ travel g.kstar g.A ≠ 0 := by
  classical
  have h := Finset.min'_mem g.occ g.occ_nonempty
  simp only [occ, Finset.mem_insert] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_filter.mp h).2

/-- **`B` is minimal.** -/
theorem B_min : g.B = 0 ∨ g.d g.B ≠ 0 ∨ travel g.kstar g.B ≠ 0 := by
  classical
  have h := Finset.max'_mem g.occ g.occ_nonempty
  simp only [occ, Finset.mem_insert] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_filter.mp h).2

/-- **The bridge.**  Every group element in lamp form has a `PathData`. -/
noncomputable def toPathData : PathData where
  kstar := g.kstar
  eps := g.eps
  delta := g.delta
  heps := g.heps
  d := g.d
  hpar := g.hpar
  A := g.A
  B := g.B
  hA := g.A_le_zero
  hB := g.zero_le_B
  houter := g.outer
  hAmin := g.A_min
  hBmin := g.B_min

@[simp] theorem toPathData_d : g.toPathData.d = g.d := rfl
@[simp] theorem toPathData_kstar : g.toPathData.kstar = g.kstar := rfl

/-- **The relaxed length of a group element.**  This is the definition the
development did not have: with `toPathData`, `lR` is now a function of `g`. -/
noncomputable def lR : ℕ := g.toPathData.lR

/-- **The metric formula, as a contract (Rule I7).**

`rem:pairingstatus` records that the optimisation computes the relaxed word length
"verified there and not proved".  It cannot be *stated* in Lean without a word-length
function on group elements, which the development lacks.  This names the obligation:
any candidate relaxed-length function must agree with `lR`.  Discharging it is H1a,
and it needs a presentation and a generating set, neither of which is formalised.

This is deliberately a `Prop`-valued contract and not a theorem.  It is the honest
form of a gap that was previously only prose. -/
def IsRelaxedLength (L : Elt → ℕ) : Prop := ∀ g : Elt, L g = g.lR

/-- The relaxed length is the span mass plus the site costs -- unfolded, so the
contract above is not opaque. -/
theorem lR_eq : g.lR =
    (∑ j ∈ Finset.Icc g.A g.B, g.toPathData.mu j)
      + ∑ s ∈ Finset.Icc g.A (g.B + 1), g.toPathData.siteCost s := rfl

end Elt

end EltBridge

#print axioms EltBridge.Elt.outer
#print axioms EltBridge.Elt.A_min
#print axioms EltBridge.Elt.B_min
#print axioms EltBridge.Elt.toPathData
#print axioms EltBridge.Elt.lR_eq
