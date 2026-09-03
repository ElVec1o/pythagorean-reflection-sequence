/-
  CutComponents.lean
  ==================
  The counting step of Proposition `prop:cut` of `paper/journal/paper2.tex`, section 5.5
  (`sec:sitecost`): the sentence

     "Removing the `|Z|` cut sites disconnects the crossings of the span into at least `|Z|+1`
      classes, no two of which can lie in the same component; one component carries the virtual
      events, so at least `|Z|` are isolated cycles."

  What is formalised here is that sentence and nothing else, over an abstract graph.  The
  hypotheses are the three facts the paper's proof uses about the strand graph of a minimum-cost
  realisation:

  * `hedge`  an edge of the graph joins two crossings whose edges are the two edges `s-1`, `s`
             adjacent to one site `s`, and it joins crossings on *different* edges only when `s`
             is not a cut site (Proposition `prop:cut`, first sentence: at a cut site every
             minimum-cost pairing matches on its own side);
  * `hocc`   every edge of the span carries at least one crossing (Corollary `cor:lRclosed`,
             `m_j >= 1` on the span);
  * `hlow`, `hhigh`
             the cut sites counted are interior to the span.

  The conclusion is an injection of `Fin (|Z|+1)` into the connected components, which is
  "at least `|Z|+1` components" with no finiteness hypothesis anywhere, and, once the two
  virtual events are known to share a component, an injection of `Fin |Z|` into the components
  that avoids it, which is the paper's `c >= |Z|`.

  Two of the three inputs are then supplied against the actual structures of `Realisation.lean`:
  `PathData.cutSet` is `Z`, the cut sites interior to the span, and `cutSet_lt`, `cutSet_le` are
  its two bounds; `Realisation.m_pos_of_min` is the occupancy, every edge of the span of a
  minimum-cost realisation carrying at least one crossing.

  NOT formalised here, and this is what keeps the star on `prop:cut`: the construction of the
  strand graph itself, that is, the pair `(V, G)` together with `pos` and a proof of `Local`.
  `Realisation.pair` stores the multiplicity matrix of the site pairing, not the bijection, so
  the vertex set and the incidence relation this file quantifies over are not yet definable
  against that structure.  `Realisation.cut_no_cross` supplies the mathematical content of
  `Local` at the level of the matrix (`cross = 0` at a cut site); what is missing is the passage
  from that to an incidence relation on crossings.  See the file header of `Realisation.lean`.

  No `sorry`.
-/

import Realisation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Int.Interval

namespace CutComponents

/-! ## The block index of a position -/

section Blocks

variable (Zf : Finset ℤ)

/-- The block index of a position: the number of cut sites at or below it. -/
def gz (t : ℤ) : ℕ := (Zf.filter (fun z => z ≤ t)).card

/-- The block index does not change across a site that is not cut. -/
theorem gz_step_eq {s : ℤ} (hs : s ∉ Zf) : gz Zf s = gz Zf (s - 1) := by
  unfold gz
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hle⟩
    refine ⟨hz, ?_⟩
    by_cases hzs : z = s
    · exact absurd (hzs ▸ hz) hs
    · omega
  · rintro ⟨hz, hle⟩
    exact ⟨hz, by omega⟩

/-- The block index steps by at most one. -/
theorem gz_le_succ (t : ℤ) : gz Zf (t + 1) ≤ gz Zf t + 1 := by
  have hsub : Zf.filter (fun z => z ≤ t + 1) ⊆ insert (t + 1) (Zf.filter (fun z => z ≤ t)) := by
    intro z hz
    simp only [Finset.mem_filter] at hz
    simp only [Finset.mem_insert, Finset.mem_filter]
    by_cases hzt : z ≤ t
    · exact Or.inr ⟨hz.1, hzt⟩
    · exact Or.inl (by omega)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- Below every cut site the block index is `0`. -/
theorem gz_eq_zero {A : ℤ} (h : ∀ z ∈ Zf, A < z) : gz Zf A = 0 := by
  unfold gz
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z hz
  exact not_le.mpr (h z hz)

/-- Above every cut site the block index is `|Z|`. -/
theorem gz_eq_card {B : ℤ} (h : ∀ z ∈ Zf, z ≤ B) : gz Zf B = Zf.card := by
  unfold gz
  rw [Finset.filter_true_of_mem h]

/-- A discrete intermediate value theorem: a sequence starting at `0` and stepping up by at most
one takes every value below its value at `N`. -/
theorem discrete_ivt (h : ℕ → ℕ) (h0 : h 0 = 0) (hstep : ∀ k, h (k + 1) ≤ h k + 1) :
    ∀ (N i : ℕ), i ≤ h N → ∃ k ≤ N, h k = i := by
  intro N
  induction N with
  | zero => intro i hi; exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
      intro i hi
      by_cases hc : i ≤ h n
      · obtain ⟨k, hk, hke⟩ := ih i hc
        exact ⟨k, by omega, hke⟩
      · have hs := hstep n
        exact ⟨n + 1, le_rfl, by omega⟩

/-- **The block index takes every value in `0..|Z|` on the span.** -/
theorem exists_pos_with_gz (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B) (i : ℕ) (hi : i ≤ Zf.card) :
    ∃ t : ℤ, A ≤ t ∧ t ≤ B ∧ gz Zf t = i := by
  have hAN : A + (((B - A).toNat : ℕ) : ℤ) = B := by omega
  have h0 : gz Zf (A + ((0 : ℕ) : ℤ)) = 0 := by
    have hA : A + ((0 : ℕ) : ℤ) = A := by omega
    rw [hA]
    exact gz_eq_zero Zf hlow
  have hstep : ∀ k : ℕ, gz Zf (A + ((k + 1 : ℕ) : ℤ)) ≤ gz Zf (A + (k : ℤ)) + 1 := by
    intro k
    have he : A + ((k + 1 : ℕ) : ℤ) = A + (k : ℤ) + 1 := by omega
    rw [he]
    exact gz_le_succ Zf (A + (k : ℤ))
  have hNv : gz Zf (A + (((B - A).toNat : ℕ) : ℤ)) = Zf.card := by
    rw [hAN]
    exact gz_eq_card Zf hhigh
  obtain ⟨k, hk, hke⟩ :=
    discrete_ivt (fun k : ℕ => gz Zf (A + (k : ℤ))) h0 hstep (B - A).toNat i
      (by simp only [hNv]; exact hi)
  exact ⟨A + (k : ℤ), by omega, by omega, hke⟩

end Blocks

/-! ## The component count -/

section Graph

variable {V : Type*} (G : SimpleGraph V) (pos : V → ℤ) (Zf : Finset ℤ)

/-- The block index of a vertex. -/
def blk (v : V) : ℕ := gz Zf (pos v)

/-- The locality hypothesis on the strand graph: an edge joins two crossings on the two edges
adjacent to one site, and joins crossings on different edges only at a site that is not cut. -/
def Local : Prop :=
  ∀ x y : V, G.Adj x y → ∃ s : ℤ,
    (pos x = s - 1 ∨ pos x = s) ∧ (pos y = s - 1 ∨ pos y = s) ∧ (pos x ≠ pos y → s ∉ Zf)

variable {G pos Zf}

/-- The block index is constant across an edge. -/
theorem blk_adj (hedge : Local G pos Zf) {x y : V} (hxy : G.Adj x y) :
    blk pos Zf x = blk pos Zf y := by
  obtain ⟨s, hx, hy, hs⟩ := hedge x y hxy
  by_cases hp : pos x = pos y
  · unfold blk; rw [hp]
  · have key : gz Zf s = gz Zf (s - 1) := gz_step_eq Zf (hs hp)
    unfold blk
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact key.symm
    · exact key

/-- The block index is constant on connected components. -/
theorem blk_reachable (hedge : Local G pos Zf) {x y : V} (hr : G.Reachable x y) :
    blk pos Zf x = blk pos Zf y := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (blk_adj hedge hadj).trans ih

/-! ### Locality with exceptions

`Local` is stronger than the argument needs.  Everything below it uses locality only
through `blk_adj`: the block index is constant across a graph edge.  An edge that
spans many sites but happens to join ends of equal block index does no harm.

This matters for end types carrying a *virtual* pair -- a strand running the whole
travel interval in one step.  Such an edge is never local, but it always joins ends of
one run, so the conclusion survives. -/

/-- `Local`, except on edges listed by `Exc`. -/
def LocalExcept (G : SimpleGraph V) (pos : V → ℤ) (Zf : Finset ℤ)
    (Exc : V → V → Prop) : Prop :=
  ∀ x y : V, G.Adj x y → Exc x y ∨ (∃ s : ℤ,
    (pos x = s - 1 ∨ pos x = s) ∧ (pos y = s - 1 ∨ pos y = s) ∧ (pos x ≠ pos y → s ∉ Zf))

/-- **The block index is constant across an edge**, given locality except on edges
that already preserve it. -/
theorem blk_adj_except {Exc : V → V → Prop}
    (hedge : LocalExcept G pos Zf Exc)
    (hexc : ∀ x y : V, Exc x y → blk pos Zf x = blk pos Zf y)
    {x y : V} (hxy : G.Adj x y) :
    blk pos Zf x = blk pos Zf y := by
  rcases hedge x y hxy with h | ⟨s, hx, hy, hs⟩
  · exact hexc x y h
  · by_cases hp : pos x = pos y
    · unfold blk; rw [hp]
    · have key : gz Zf s = gz Zf (s - 1) := gz_step_eq Zf (hs hp)
      unfold blk
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact key.symm
      · exact key

/-- **And on connected components.** -/
theorem blk_reachable_except {Exc : V → V → Prop}
    (hedge : LocalExcept G pos Zf Exc)
    (hexc : ∀ x y : V, Exc x y → blk pos Zf x = blk pos Zf y)
    {x y : V} (hr : G.Reachable x y) :
    blk pos Zf x = blk pos Zf y := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (blk_adj_except hedge hexc hadj).trans ih

/-- **`c >= |Z|`, run form, with exceptions.** -/
theorem exists_injective_components_of_runs_except {Exc : V → V → Prop}
    (hedge : LocalExcept G pos Zf Exc)
    (hexc : ∀ x y : V, Exc x y → blk pos Zf x = blk pos Zf y)
    (hruns : ∀ i : ℕ, i ≤ Zf.card → ∃ v : V, blk pos Zf v = i) :
    ∃ F : Fin (Zf.card + 1) → G.ConnectedComponent, Function.Injective F := by
  have hex : ∀ i : Fin (Zf.card + 1), ∃ v : V, blk pos Zf v = (i : ℕ) :=
    fun i => hruns (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  choose v hv using hex
  refine ⟨fun i => G.connectedComponentMk (v i), fun i j hij => ?_⟩
  have hb := blk_reachable_except hedge hexc (SimpleGraph.ConnectedComponent.exact hij)
  rw [hv i, hv j] at hb
  exact Fin.val_injective hb

/-- **`prop:cut`, run form, with exceptions.** -/
theorem exists_injective_components_avoiding_of_runs_except {Exc : V → V → Prop}
    (hedge : LocalExcept G pos Zf Exc)
    (hexc : ∀ x y : V, Exc x y → blk pos Zf x = blk pos Zf y)
    (hruns : ∀ i : ℕ, i ≤ Zf.card → ∃ v : V, blk pos Zf v = i)
    (c0 : G.ConnectedComponent) :
    ∃ F : Fin Zf.card → G.ConnectedComponent, Function.Injective F ∧ ∀ i, F i ≠ c0 := by
  obtain ⟨F, hF⟩ :=
    exists_injective_components_of_runs_except hedge hexc hruns
  by_cases hc : ∃ p : Fin (Zf.card + 1), F p = c0
  · obtain ⟨p, hp⟩ := hc
    refine ⟨fun j => F (p.succAbove j), fun i j hij => ?_, fun j hj => ?_⟩
    · exact Fin.succAbove_right_injective (hF hij)
    · exact Fin.succAbove_ne p j (hF (hj.trans hp.symm))
  · simp only [not_exists] at hc
    exact ⟨fun j => F j.castSucc, fun i j hij => Fin.castSucc_injective _ (hF hij),
      fun j => hc _⟩

/-- **Proposition `prop:cut`, the counting step.**  A graph on the crossings of the span whose
edges are local for the cut set has at least `|Z|+1` connected components. -/
theorem exists_injective_components (hedge : Local G pos Zf) (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ v : V, pos v = t) :
    ∃ F : Fin (Zf.card + 1) → G.ConnectedComponent, Function.Injective F := by
  have hex : ∀ i : Fin (Zf.card + 1), ∃ v : V, blk pos Zf v = (i : ℕ) := by
    intro i
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      exists_pos_with_gz Zf A B hAB hlow hhigh (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
    obtain ⟨v, hv⟩ := hocc t ht1 ht2
    exact ⟨v, by unfold blk; rw [hv]; exact ht3⟩
  choose v hv using hex
  refine ⟨fun i => G.connectedComponentMk (v i), fun i j hij => ?_⟩
  have hb := blk_reachable hedge (SimpleGraph.ConnectedComponent.exact hij)
  rw [hv i, hv j] at hb
  exact Fin.val_injective hb

/-- **Proposition `prop:cut`, `c >= |Z|`.**  Once the two virtual events are known to lie in one
component `c0`, at least `|Z|` components carry neither of them. -/
theorem exists_injective_components_avoiding (hedge : Local G pos Zf) (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ v : V, pos v = t) (c0 : G.ConnectedComponent) :
    ∃ F : Fin Zf.card → G.ConnectedComponent, Function.Injective F ∧ ∀ i, F i ≠ c0 := by
  obtain ⟨F, hF⟩ := exists_injective_components hedge A B hAB hlow hhigh hocc
  by_cases hc : ∃ p : Fin (Zf.card + 1), F p = c0
  · obtain ⟨p, hp⟩ := hc
    refine ⟨fun j => F (p.succAbove j), fun i j hij => ?_, fun j hj => ?_⟩
    · exact Fin.succAbove_right_injective (hF hij)
    · exact Fin.succAbove_ne p j (hF (hj.trans hp.symm))
  · simp only [not_exists] at hc
    exact ⟨fun j => F j.castSucc, fun i j hij => Fin.castSucc_injective _ (hF hij),
      fun j => hc _⟩

/-! ### The run form of the lower bound

`hocc` -- every position in `[A, B]` occupied -- is stronger than the proof needs, and
in the intended application it is **unsatisfiable**: a cut site carries no ends, so the
positions adjacent to it are empty.  All the proof uses `hocc` for is to produce, for
each block index, *some* vertex in that block.  That is the run form below, and it is
satisfiable in the presence of cut sites. -/

/-- **`c >= |Z|`, run form.**  Only that every run carries a vertex. -/
theorem exists_injective_components_of_runs (hedge : Local G pos Zf)
    (hruns : ∀ i : ℕ, i ≤ Zf.card → ∃ v : V, blk pos Zf v = i) :
    ∃ F : Fin (Zf.card + 1) → G.ConnectedComponent, Function.Injective F := by
  have hex : ∀ i : Fin (Zf.card + 1), ∃ v : V, blk pos Zf v = (i : ℕ) :=
    fun i => hruns (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  choose v hv using hex
  refine ⟨fun i => G.connectedComponentMk (v i), fun i j hij => ?_⟩
  have hb := blk_reachable hedge (SimpleGraph.ConnectedComponent.exact hij)
  rw [hv i, hv j] at hb
  exact Fin.val_injective hb

/-- **`prop:cut`, run form.** -/
theorem exists_injective_components_avoiding_of_runs (hedge : Local G pos Zf)
    (hruns : ∀ i : ℕ, i ≤ Zf.card → ∃ v : V, blk pos Zf v = i)
    (c0 : G.ConnectedComponent) :
    ∃ F : Fin Zf.card → G.ConnectedComponent, Function.Injective F ∧ ∀ i, F i ≠ c0 := by
  obtain ⟨F, hF⟩ := exists_injective_components_of_runs hedge hruns
  by_cases hc : ∃ p : Fin (Zf.card + 1), F p = c0
  · obtain ⟨p, hp⟩ := hc
    refine ⟨fun j => F (p.succAbove j), fun i j hij => ?_, fun j hj => ?_⟩
    · exact Fin.succAbove_right_injective (hF hij)
    · exact Fin.succAbove_ne p j (hF (hj.trans hp.symm))
  · simp only [not_exists] at hc
    exact ⟨fun j => F j.castSucc, fun i j hij => Fin.castSucc_injective _ (hF hij),
      fun j => hc _⟩

end Graph


end CutComponents

/-! ## The two inputs that a `Realisation` already supplies -/

namespace SiteCost

instance decCut (P : PathData) (s : ℤ) : Decidable (P.cut s) := by
  unfold PathData.cut
  infer_instance

namespace PathData

variable (P : PathData)

/-- `Z` of Proposition `prop:cut`: the cut sites interior to the span. -/
def cutSet : Finset ℤ := (Finset.Icc (P.A + 1) P.B).filter P.cut

theorem mem_cutSet {s : ℤ} : s ∈ P.cutSet ↔ (P.A + 1 ≤ s ∧ s ≤ P.B) ∧ P.cut s := by
  simp [cutSet, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The cut sites of `Z` lie strictly above the left end of the span. -/
theorem cutSet_lt (s : ℤ) (hs : s ∈ P.cutSet) : P.A < s := by
  have h := (P.mem_cutSet).1 hs
  omega

/-- The cut sites of `Z` lie at or below the right end of the span. -/
theorem cutSet_le (s : ℤ) (hs : s ∈ P.cutSet) : s ≤ P.B := by
  have h := (P.mem_cutSet).1 hs
  omega

end PathData

namespace Realisation

variable {P : PathData} (R : Realisation P)

/-- **Every edge of the span carries a crossing.**  This is the occupancy input `hocc` of
`CutComponents.exists_injective_components`, at the level of the crossing counts. -/
theorem m_pos_of_min (hmin : R.cost = P.lR) {j : ℤ} (hj : P.A ≤ j ∧ j ≤ P.B) : 1 ≤ R.m j := by
  obtain ⟨ha, hb, -, -⟩ := R.rigidity hmin
  exact le_trans (P.mu_pos j) (R.m_ge (by omega))

end Realisation

end SiteCost



#print axioms SiteCost.PathData.mem_cutSet
#print axioms SiteCost.PathData.cutSet_lt
#print axioms SiteCost.PathData.cutSet_le
#print axioms SiteCost.Realisation.m_pos_of_min
#print axioms CutComponents.gz_step_eq
#print axioms CutComponents.gz_le_succ
#print axioms CutComponents.gz_eq_zero
#print axioms CutComponents.gz_eq_card
#print axioms CutComponents.discrete_ivt
#print axioms CutComponents.exists_pos_with_gz
#print axioms CutComponents.blk_adj
#print axioms CutComponents.blk_reachable
#print axioms CutComponents.exists_injective_components
#print axioms CutComponents.exists_injective_components_avoiding
#print axioms CutComponents.exists_injective_components_of_runs
#print axioms CutComponents.exists_injective_components_avoiding_of_runs
#print axioms CutComponents.blk_adj_except
#print axioms CutComponents.exists_injective_components_avoiding_of_runs_except
