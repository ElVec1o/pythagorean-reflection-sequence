/-
Block additivity, closed end to end: the `blockConcat`-to-`Word` bridge, for lists of blocks
that are all nontrivial in `D_m` (`cor:onset`'s actual usage shape: no block is the identity).

Combines `BlockAdditivity.lean` (the room's Φ-Lipschitz engine: `phi_le_length`,
`geodesic_of_phi_eq`, `phi_eq_of_prod`) and `DmLength.lean` (the general `dl`, valid for every
`m`, via `dl_one`/`dl_L0`/`dl_L1`).
-/
import DmLength
import BlockAdditivity

namespace BlockAdditivity

open Monoid CoxeterTorsion RotationRelations

variable {m : ℕ}

/-- Interleave `{0,1}`-blocks with `x_2` separators: `bs_0 x_2 bs_1 x_2 ... x_2 bs_k`. -/
def blockConcat : List (List Bit) → List Letter
  | []         => []
  | [bs]       => bs.map toLetter
  | bs :: rest => bs.map toLetter ++ (2 : Letter) :: blockConcat rest

theorem blockConcat_cons_cons (bs b2 : List Bit) (rest : List (List Bit)) :
    blockConcat (bs :: b2 :: rest)
      = bs.map toLetter ++ (2 : Letter) :: blockConcat (b2 :: rest) := by
  simp [blockConcat]

/-- Every block is a nontrivial element of `D_m` (the hypothesis `cor:onset` actually needs —
no block, interior or boundary, collapses to the identity). -/
def AllNontrivial (m : ℕ) (bss : List (List Bit)) : Prop :=
  ∀ bs ∈ bss, evD m bs ≠ (1 : DihedralGroup m)

theorem allNontrivial_tail {bs : List Bit} {rest : List (List Bit)}
    (h : AllNontrivial m (bs :: rest)) : AllNontrivial m rest :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem allNontrivial_head {bs : List Bit} {rest : List (List Bit)}
    (h : AllNontrivial m (bs :: rest)) : evD m bs ≠ 1 :=
  h bs (by simp)

theorem sr0_ne_one_factor1 (m : ℕ) : (DihedralGroup.sr 0 : factor m 1) ≠ 1 := by
  show (DihedralGroup.sr 0 : DihedralGroup 1) ≠ 1
  decide

/-- The raw syllable list underlying `blockConcat`: alternating dihedral blocks (index `0`)
and `x_2` separators (index `1`). -/
def wordList (m : ℕ) : List (List Bit) → List (Σ i : Fin 2, factor m i)
  | []         => []
  | [bs]       => [⟨0, evD m bs⟩]
  | bs :: (b2 :: rest) =>
      ⟨0, evD m bs⟩ :: ⟨1, (DihedralGroup.sr 0 : factor m 1)⟩ :: wordList m (b2 :: rest)

theorem wordList_ne_one (m : ℕ) : ∀ bss : List (List Bit), AllNontrivial m bss →
    ∀ p ∈ wordList m bss, p.2 ≠ 1
  | [], _, p, hp => by simp [wordList] at hp
  | [bs], h, p, hp => by
      simp only [wordList, List.mem_singleton] at hp
      subst hp
      exact allNontrivial_head h
  | bs :: (b2 :: rest), h, p, hp => by
      simp only [wordList, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact allNontrivial_head h
      · exact sr0_ne_one_factor1 m
      · exact wordList_ne_one m (b2 :: rest) (allNontrivial_tail h) p hp

/-- `wordList` of a nonempty block list always starts with a dihedral-block syllable
(index `0`), never a separator. -/
theorem wordList_head (m : ℕ) (b2 : List Bit) (rest : List (List Bit)) :
    (wordList m (b2 :: rest)).head? = some ⟨0, evD m b2⟩ := by
  cases rest <;> simp [wordList]

theorem wordList_chain (m : ℕ) : ∀ bss : List (List Bit),
    (wordList m bss).IsChain (fun p p' => p.1 ≠ p'.1)
  | [] => List.isChain_nil
  | [bs] => List.isChain_singleton _
  | bs :: (b2 :: rest) => by
      have h01 : (⟨0, evD m bs⟩ : Σ i : Fin 2, factor m i).1
          ≠ (⟨1, (DihedralGroup.sr 0 : factor m 1)⟩ : Σ i : Fin 2, factor m i).1 := by simp
      rw [wordList, List.isChain_cons]
      refine ⟨?_, ?_⟩
      · rintro y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact h01
      · rw [List.isChain_cons]
        refine ⟨?_, wordList_chain m (b2 :: rest)⟩
        rintro y hy
        rw [wordList_head m b2 rest] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact h01.symm

/-- The `CoprodI.Word` matching `blockConcat`'s structure, for a list of nontrivial blocks. -/
def blockWordGen (m : ℕ) (bss : List (List Bit)) (h : AllNontrivial m bss) :
    CoprodI.Word (factor m) where
  toList := wordList m bss
  ne_one := wordList_ne_one m bss h
  chain_ne := wordList_chain m bss

theorem blockWordGen_prod (m : ℕ) :
    ∀ (bss : List (List Bit)) (h : AllNontrivial m bss),
      CoprodI.Word.prod (blockWordGen m bss h) = ev m (blockConcat bss)
  | [], _ => by simp [blockWordGen, wordList, CoprodI.Word.prod, blockConcat, ev]
  | [bs], _ => by
      have hev := ev_toLetter m bs
      simp only [blockWordGen, wordList, CoprodI.Word.prod, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, emb] at *
      exact hev.symm
  | bs :: (b2 :: rest), h => by
      have hbev : ev m (bs.map toLetter) = (emb m) (evD m bs) := ev_toLetter m bs
      have hsep : (CoprodI.of (DihedralGroup.sr 0 : factor m 1) : W m) = gen m 2 :=
        (gen_two_of (2 : Letter) (by decide) (by decide)).symm
      have hrest := blockWordGen_prod m (b2 :: rest) (allNontrivial_tail h)
      simp only [blockWordGen, wordList, CoprodI.Word.prod, List.map_cons, List.prod_cons] at *
      conv_rhs => rw [blockConcat_cons_cons, ev_append, ev_cons]
      rw [hbev, hsep, hrest]
      rfl

theorem sumCost_blockWordGen (m : ℕ) [NeZero m] :
    ∀ (bss : List (List Bit)) (h : AllNontrivial m bss)
      (_hgeo : ∀ bs ∈ bss, bs.length = dl m (evD m bs)),
      sumCost (dl m) (blockWordGen m bss h) = (blockConcat bss).length
  | [], _, _ => by simp [blockWordGen, wordList, sumCost, blockConcat]
  | [bs], _, hgeo => by
      have hn := hgeo bs (by simp)
      show ((wordList m [bs]).map (cost (dl m))).sum = (blockConcat [bs]).length
      simp only [wordList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, cost_zero, blockConcat, List.length_map]
      omega
  | bs :: (b2 :: rest), h, hgeo => by
      have hn := hgeo bs (by simp)
      have hrest := sumCost_blockWordGen m (b2 :: rest) (allNontrivial_tail h)
        (fun b hb => hgeo b (by simp [hb]))
      have hsepcost : cost (dl m) (⟨(1 : Fin 2), (DihedralGroup.sr 0 : factor m 1)⟩) = 1 := by
        rw [cost_one_idx, if_neg (sr0_ne_one_factor1 m)]
      show ((wordList m (bs :: b2 :: rest)).map (cost (dl m))).sum
        = (blockConcat (bs :: b2 :: rest)).length
      rw [wordList]
      simp only [List.map_cons, List.sum_cons, cost_zero]
      have hrest' : ((wordList m (b2 :: rest)).map (cost (dl m))).sum
          = (blockConcat (b2 :: rest)).length := hrest
      conv_rhs => rw [blockConcat_cons_cons, List.length_append, List.length_cons, List.length_map]
      rw [hsepcost, hrest']
      omega

/-- **The end-to-end result.** A block list, all blocks nontrivial in `D_m` and each already a
`dl`-geodesic (`bs.length = dl m (evD m bs)`), gives a `{x_0,x_1,x_2}`-geodesic word in `W m`
via straight concatenation with `x_2` separators — no range restriction on the blocks. -/
theorem block_additivity (m : ℕ) [NeZero m] (bss : List (List Bit))
    (h : AllNontrivial m bss)
    (hgeo : ∀ bs ∈ bss, bs.length = dl m (evD m bs))
    (v' : List Letter) (hvv : ev m v' = ev m (blockConcat bss)) :
    (blockConcat bss).length ≤ v'.length := by
  have hprod := blockWordGen_prod m bss h
  have hcost := sumCost_blockWordGen m bss h hgeo
  have hpe : phi (dl m) (ev m (blockConcat bss)) = (blockConcat bss).length := by
    rw [phi_eq_of_prod (dl m) hprod, hcost]
  exact geodesic_of_phi_eq (dl m) (dl_one m) (dl_L0 m) (dl_L1 m) hpe v' hvv

end BlockAdditivity

#print axioms BlockAdditivity.block_additivity
