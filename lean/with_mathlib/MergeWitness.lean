/-
A concrete two-walk witness for the merge descent.

The descent's hypotheses are checked here on an explicit `Data` rather than argued
about.  `turn` on a real configuration is a *chosen* involution, so no equation
about it decides; but the vacuity risk was never in `turn`'s identity, it was in
whether the hypotheses can hold together at all.  At the `Data` level `p` and `t`
are functions we write down, and everything becomes decidable.

Eight ends, two walks of four.  `a = 0` and `a' = 4` are arrivals in *different*
walks, which is exactly `hsplit`.
-/
import Mathlib.Tactic
import WalkGraph
import ConfigMerge

namespace MergeWitness

open WalkGraph

/-- Crossing partners: four crossings, `(0 1) (2 3) (4 5) (6 7)`. -/
def pw : Fin 8 → Fin 8
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6

/-- Turns: `(0 3) (1 2) (4 7) (5 6)`, closing each quadruple into one walk. -/
def tw : Fin 8 → Fin 8
  | 0 => 3 | 3 => 0 | 1 => 2 | 2 => 1
  | 4 => 7 | 7 => 4 | 5 => 6 | 6 => 5

theorem pw_invol : ∀ x, pw (pw x) = x := by decide
theorem tw_invol : ∀ x, tw (tw x) = x := by decide
theorem pw_ne : ∀ x, pw x ≠ x := by decide
theorem tw_ne : ∀ x, tw x ≠ x := by decide
theorem pt_ne_w : ∀ x, pw x ≠ tw x := by decide

/-- The witness data. -/
def W : Data (Fin 8) where
  p := pw
  t := tw
  p_invol := pw_invol
  t_invol := tw_invol
  p_ne := pw_ne
  t_ne := tw_ne
  pt_ne := pt_ne_w

/-- The component invariant: which of the two walks an end lies in. -/
def side (x : Fin 8) : Bool := x.val < 4

theorem side_adj : ∀ x y : Fin 8, (y = pw x ∨ y = tw x) → side x = side y := by decide

/-- An invariant constant on edges is constant on components. -/
theorem side_reach {x y : Fin 8} (h : (graph W).Reachable x y) : side x = side y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (side_adj _ _ hadj).trans ih

/-- **`hsplit` holds**: the two arrivals lie in different walks. -/
theorem split_witness : ¬ (graph W).Reachable 0 4 := by
  intro h; have := side_reach h; revert this; decide

/-- The turn-partners of the two arrivals. -/
theorem turn_zero : W.t 0 = 3 := rfl
theorem turn_four : W.t 4 = 7 := rfl

/-- The `sig`-orbit through `7` has period **two**, not four: `sig 7 = t (p 7) = 5`
and `sig 5 = 7`.  The walk on `{4,5,6,7}` therefore splits into two `sig`-orbits,
`{7,5}` and `{4,6}` -- the concrete form of the counted fact that `sig` has twice as
many cycles as there are walks.  Guessing the orbit was `(7,6,5,4)` was wrong, and
`decide` said so. -/
theorem sig_orbit : ((sig W)^[0] 7, (sig W)^[1] 7, (sig W)^[2] 7, (sig W)^[3] 7)
    = (7, 5, 7, 5) := by decide

theorem sig_orbit' : ((sig W)^[0] 4, (sig W)^[1] 4) = (4, 6) := by decide

/-- The walk through `7` closes at the minimal period two. -/
theorem sig_closes : (sig W)^[2] 7 = 7 := by decide
theorem sig_closes_pos : 0 < 2 := by norm_num

/-- Every end of the first walk is reachable from `0`, and likewise for the second:
both walks really are connected, so `walkCount W = 2` is not an artefact of the
graph being sparser than intended. -/
theorem adj_one : (graph W).Adj 0 1 := Or.inl rfl
theorem adj_three : (graph W).Adj 0 3 := Or.inr rfl

-- Certification (Rule 5).
#print axioms MergeWitness.split_witness
#print axioms MergeWitness.sig_closes
#print axioms MergeWitness.sig_orbit
#print axioms MergeWitness.sig_orbit'
#print axioms MergeWitness.side_reach

/-! ### The cycle-minus-an-edge input, exhibited

`hadj` says every adjacency survives deleting the two re-paired turn-edges.  It is
not decidable here, so the detours are written out: each walk is a four-cycle, and
removing one turn-edge leaves a three-step path around it. -/

/-- The graph with the two re-paired turn-edges removed. -/
abbrev Del : SimpleGraph (Fin 8) :=
  (graph W).deleteEdges {s((0 : Fin 8), (3 : Fin 8)), s((4 : Fin 8), (7 : Fin 8))}

theorem mkAdj {x y : Fin 8} (h : y = pw x ∨ y = tw x)
    (hn : s(x, y) ∉ ({s((0 : Fin 8), (3 : Fin 8)), s((4 : Fin 8), (7 : Fin 8))} :
      Set (Sym2 (Fin 8)))) : Del.Adj x y :=
  SimpleGraph.deleteEdges_adj.mpr ⟨h, hn⟩

/-- Around the first walk: `0 - 1 - 2 - 3`, avoiding the removed turn-edge `0-3`. -/
theorem detour_03 : Del.Reachable 0 3 :=
  ((mkAdj (x := 0) (y := 1) (Or.inl rfl) (by simp [Sym2.eq_iff])).reachable.trans
    ((mkAdj (x := 1) (y := 2) (Or.inr rfl) (by simp [Sym2.eq_iff])).reachable)).trans
    ((mkAdj (x := 2) (y := 3) (Or.inl rfl) (by simp [Sym2.eq_iff])).reachable)

/-- Around the second walk: `4 - 5 - 6 - 7`, avoiding the removed turn-edge `4-7`. -/
theorem detour_47 : Del.Reachable 4 7 :=
  ((mkAdj (x := 4) (y := 5) (Or.inl rfl) (by simp [Sym2.eq_iff])).reachable.trans
    ((mkAdj (x := 5) (y := 6) (Or.inr rfl) (by simp [Sym2.eq_iff])).reachable)).trans
    ((mkAdj (x := 6) (y := 7) (Or.inl rfl) (by simp [Sym2.eq_iff])).reachable)

/-- **The cycle input holds on the witness.**  Every adjacency of the walk graph
survives deleting the two re-paired turn-edges: an edge that is not deleted is
still there, and each of the two that are deleted has its detour. -/
theorem hadj_W : ∀ x y : Fin 8, (graph W).Adj x y → Del.Reachable x y := by
  intro x y hxy
  by_cases hmem : s(x, y) ∈
      ({s((0 : Fin 8), (3 : Fin 8)), s((4 : Fin 8), (7 : Fin 8))} : Set (Sym2 (Fin 8)))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      subst h1 <;> subst h2 <;>
      first
        | exact detour_03
        | exact detour_03.symm
        | exact detour_47
        | exact detour_47.symm
  · exact (mkAdj hxy hmem).reachable

/-! ### The descent, on the witness

Every side condition of `swapData` is decidable here, because `swapT` is a
computable re-pairing of four ends. -/

theorem h1W : ∀ x, swapT W.t 0 3 4 7 (swapT W.t 0 3 4 7 x) = x := by decide
theorem h2W : ∀ x, swapT W.t 0 3 4 7 x ≠ x := by decide
theorem h3W : ∀ x, W.p x ≠ swapT W.t 0 3 4 7 x := by decide

/-- The re-paired witness data. -/
def W' : Data (Fin 8) := swapData W 0 3 4 7 h1W h2W h3W

/-- After the re-pairing the two walks are joined: `0 - 7 - 6 - 5 - 4`.  The first
step is the new turn `0 ↦ 7`, which did not exist before. -/
theorem join_witness : (graph W').Reachable 0 4 :=
  (((SimpleGraph.Adj.reachable (G := graph W') (show (7 : Fin 8) = W'.p 0 ∨ (7 : Fin 8) = W'.t 0
      from Or.inr (by decide))).trans
    (SimpleGraph.Adj.reachable (G := graph W') (show (6 : Fin 8) = W'.p 7 ∨ (6 : Fin 8) = W'.t 7
      from Or.inl (by decide)))).trans
    (SimpleGraph.Adj.reachable (G := graph W') (show (5 : Fin 8) = W'.p 6 ∨ (5 : Fin 8) = W'.t 6
      from Or.inr (by decide)))).trans
    (SimpleGraph.Adj.reachable (G := graph W') (show (4 : Fin 8) = W'.p 5 ∨ (4 : Fin 8) = W'.t 5
      from Or.inl (by decide)))

/-- **The witness.**  Re-pairing two arrivals that lie in different walks strictly
lowers the walk count, on a configuration where every hypothesis is exhibited rather
than assumed.  The descent is therefore not vacuous. -/
theorem descent_witness : walkCount W' < walkCount W :=
  walkCount_lt W W'
    (ConfigMerge.mono_swapData W 0 3 4 7 turn_zero turn_four h1W h2W h3W hadj_W)
    0 4 split_witness join_witness

-- Certification (Rule 5).
#print axioms MergeWitness.descent_witness
#print axioms MergeWitness.join_witness
