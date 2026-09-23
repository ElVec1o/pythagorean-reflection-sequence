/-
  GapRuns.lean -- room E, seat E3 (the corollary room 62L left open).

  For `kstar ≠ 0`, the corrected defect `CorrectedSpan.cTrue` is a sum over the MAXIMAL GAP
  RUNS of the corrected span:

      cTrue g = ∑_{(l,r) ∈ runs g} (L - shield(l,r)),        L = r - l + 1,

  where a gap edge is one with `d j = 0` and `travel kstar j = 0` (zero deposit, off travel),
  a maximal gap run is an interval `[l, r]` of gap edges inside `[ATrue, BTrue]` whose two
  flanking edges `l-1`, `r+1` are not gap edges, and `shield(l,r) ∈ {0,1}` is `0` exactly when
  one of the two end sites `l`, `r+1` is cut.  Moreover the end sites are matched to Lemma J:

    * both span ends are non-gap edges, so every run is strictly inside the span
      (`ATrue < l`, `r < BTrue`)                                        -- `runs_inside`;
    * the left end site `l` is cut iff it is a Lemma J junction slot with the J condition:
        (l = 0 ∧ kstar < 0 ∧ d(-1) = 1)  ∨  (l = kstar ∧ 0 < kstar ∧ delta = 0 ∧ d(kstar-1) = -eps)
                                                                          -- `cut_left_iff`;
    * the right end site `r+1` is cut iff
        r + 1 = kstar ∧ kstar < 0 ∧ delta = 1 ∧ d kstar = eps          -- `cut_right_iff`;
    * no run has both end sites cut                                     -- `not_both_ends_cut`.

  Everything is stated against the actual `SiteCost.PathData.cut` and the actual
  `CorrectedSpan.cTrue`, via `RJLemmaJ.cut_iff_cutChar`.  No sorry, no native_decide.
-/
import RJLemmaJ

namespace GapRuns

open SiteCost CorrectedSpan

variable (g : EltBridge.Elt)

/-- A gap edge: zero deposit and off travel. -/
def IsGap (j : ℤ) : Prop := g.d j = 0 ∧ travel g.kstar j = 0

open Classical in
/-- The maximal gap runs of the corrected span, as pairs `(l, r)` of first and last edge. -/
noncomputable def runs : Finset (ℤ × ℤ) :=
  ((Finset.Icc (ATrue g) (BTrue g)) ×ˢ (Finset.Icc (ATrue g) (BTrue g))).filter
    (fun p => p.1 ≤ p.2 ∧ (∀ j, p.1 ≤ j → j ≤ p.2 → IsGap g j) ∧
      ¬ IsGap g (p.1 - 1) ∧ ¬ IsGap g (p.2 + 1))

open Classical in
/-- The shield of a run: `0` if one of its end sites is cut, `1` otherwise. -/
noncomputable def shield (p : ℤ × ℤ) : ℕ :=
  if g.toPathData.cut p.1 ∨ g.toPathData.cut (p.2 + 1) then 0 else 1

/-- The length of a run. -/
def runLen (p : ℤ × ℤ) : ℕ := (p.2 - p.1 + 1).toNat

/-! ### Elementary facts -/

theorem travel_eq_zero_iff (k j : ℤ) :
    travel k j = 0 ↔ ¬ (0 ≤ j ∧ j < k) ∧ ¬ (k ≤ j ∧ j < 0) := by
  unfold travel
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h1 h.1⟩
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h2 h.2⟩
  · exact ⟨fun _ => ⟨h1, h2⟩, fun _ => rfl⟩

theorem isGap_iff (j : ℤ) :
    IsGap g j ↔ g.d j = 0 ∧ ¬ (0 ≤ j ∧ j < g.kstar) ∧ ¬ (g.kstar ≤ j ∧ j < 0) := by
  unfold IsGap; rw [travel_eq_zero_iff]

@[simp] theorem tp_eps : g.toPathData.eps = g.eps := rfl
@[simp] theorem tp_delta : g.toPathData.delta = g.delta := rfl

theorem mem_occTrue_iff (j : ℤ) : j ∈ occTrue g ↔ ¬ IsGap g j := by
  unfold occTrue IsGap
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩ ⟨h1, h2⟩
    rcases h with h | h <;> contradiction
  · intro h
    have hs : j ∈ g.supp := by
      by_contra hs; exact h (g.hsupp j hs)
    refine ⟨hs, ?_⟩
    by_contra h'
    push Not at h'
    exact h h'

/-- A travel edge adjacent to the origin is occupied when `kstar ≠ 0`. -/
theorem origin_edge_occ (hk : g.kstar ≠ 0) :
    ∃ e ∈ occTrue g, e = 0 ∨ e = -1 := by
  rcases lt_or_gt_of_ne hk with h | h
  · refine ⟨-1, ?_, Or.inr rfl⟩
    rw [mem_occTrue_iff, isGap_iff]; omega
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [mem_occTrue_iff, isGap_iff]; omega

theorem occTrue_nonempty (hk : g.kstar ≠ 0) : (occTrue g).Nonempty := by
  obtain ⟨e, he, -⟩ := origin_edge_occ g hk
  exact ⟨e, he⟩

/-- For `kstar ≠ 0`, `ATrue` is the least occupied edge (the clamp at `0` is inactive). -/
theorem ATrue_eq_min (hk : g.kstar ≠ 0) :
    ATrue g = (occTrue g).min' (occTrue_nonempty g hk) := by
  unfold ATrue
  rw [dif_pos (occTrue_nonempty g hk)]
  apply min_eq_right
  obtain ⟨e, he, he'⟩ := origin_edge_occ g hk
  have := Finset.min'_le _ e he
  omega

/-- For `kstar ≠ 0`, `BTrue` is the greatest occupied edge (the clamp at `-1` is inactive). -/
theorem BTrue_eq_max (hk : g.kstar ≠ 0) :
    BTrue g = (occTrue g).max' (occTrue_nonempty g hk) := by
  unfold BTrue
  rw [dif_pos (occTrue_nonempty g hk)]
  apply max_eq_right
  obtain ⟨e, he, he'⟩ := origin_edge_occ g hk
  have := Finset.le_max' _ e he
  omega

/-- **The span ends are not gap edges** (`kstar ≠ 0`). -/
theorem not_gap_ATrue (hk : g.kstar ≠ 0) : ¬ IsGap g (ATrue g) := by
  rw [← mem_occTrue_iff, ATrue_eq_min g hk]; exact Finset.min'_mem _ _

theorem not_gap_BTrue (hk : g.kstar ≠ 0) : ¬ IsGap g (BTrue g) := by
  rw [← mem_occTrue_iff, BTrue_eq_max g hk]; exact Finset.max'_mem _ _

theorem mem_runs {p : ℤ × ℤ} :
    p ∈ runs g ↔ (ATrue g ≤ p.1 ∧ p.1 ≤ BTrue g) ∧ (ATrue g ≤ p.2 ∧ p.2 ≤ BTrue g) ∧
      p.1 ≤ p.2 ∧ (∀ j, p.1 ≤ j → j ≤ p.2 → IsGap g j) ∧
      ¬ IsGap g (p.1 - 1) ∧ ¬ IsGap g (p.2 + 1) := by
  classical
  unfold runs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- **Runs lie strictly inside the corrected span**: their flanking edges are span edges. -/
theorem runs_inside (hk : g.kstar ≠ 0) {p : ℤ × ℤ} (hp : p ∈ runs g) :
    ATrue g < p.1 ∧ p.2 < BTrue g := by
  rw [mem_runs] at hp
  obtain ⟨⟨h1, -⟩, ⟨-, h2⟩, hlr, hg, -, -⟩ := hp
  constructor
  · rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hg p.1 le_rfl hlr) (not_gap_ATrue g hk)
  · rcases h2.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hg p.2 hlr le_rfl) (not_gap_BTrue g hk)

/-! ### Local cut facts (from Lemma J) -/

/-- Every cut site has a gap edge on at least one side (`kstar ≠ 0`). -/
theorem cut_adj_gap (hk : g.kstar ≠ 0) (s : ℤ) (hc : g.toPathData.cut s) :
    IsGap g (s - 1) ∨ IsGap g s := by
  rw [RJLemmaJ.cut_iff_cutChar] at hc
  unfold RJLemmaJ.cutChar at hc
  simp only [EltBridge.Elt.toPathData_d, EltBridge.Elt.toPathData_kstar, tp_eps, tp_delta] at hc
  rw [isGap_iff, isGap_iff]
  split_ifs at hc with h0 hks
  · subst h0
    rcases hc with ⟨hk', -, hd0⟩ | ⟨hk', -⟩
    · right; omega
    · exact absurd hk' hk
  · subst hks
    rcases hc with ⟨hk', -, -, hd⟩ | ⟨hk', -, -, hd⟩
    · right; omega
    · left; omega
  · obtain ⟨hd1, -, ht⟩ := hc
    rw [travel_eq_zero_iff] at ht
    left; omega

/-- A site with gap edges on both sides is cut (`kstar ≠ 0`): it cannot be `0` or `kstar`,
since one of the two edges there is a travel edge, so the bulk rule applies. -/
theorem cut_of_gap_gap (hk : g.kstar ≠ 0) (s : ℤ) (h1 : IsGap g (s - 1)) (h2 : IsGap g s) :
    g.toPathData.cut s := by
  rw [isGap_iff] at h1 h2
  have hs0 : s ≠ 0 := by intro h; subst h; omega
  have hsk : s ≠ g.kstar := by intro h; subst h; omega
  rw [RJLemmaJ.bulk_cut g.toPathData s hs0 hsk]
  simp only [EltBridge.Elt.toPathData_d, EltBridge.Elt.toPathData_kstar]
  rw [travel_eq_zero_iff]
  omega

/-- **Left end of a run = Lemma J junction slot.**  For a run `(l, r)` (`kstar ≠ 0`), the end
site `l` is cut iff it is site `0` with `kstar < 0` and `d(-1) = 1` (Lemma J (b)), or site
`kstar` with `kstar > 0`, `delta = 0` and `d(kstar-1) = -eps` (Lemma J (c)).  The remaining
parts of the J conditions (`d 0 = 0`, resp. `d kstar = 0`) hold automatically on a run. -/
theorem cut_left_iff (hk : g.kstar ≠ 0) {p : ℤ × ℤ} (hp : p ∈ runs g) :
    g.toPathData.cut p.1 ↔
      (p.1 = 0 ∧ g.kstar < 0 ∧ g.d (-1) = 1) ∨
      (p.1 = g.kstar ∧ 0 < g.kstar ∧ g.delta = false ∧ g.d (g.kstar - 1) = -g.eps) := by
  rw [mem_runs] at hp
  obtain ⟨-, -, hlr, hg, hL, -⟩ := hp
  have hl := hg p.1 le_rfl hlr
  obtain ⟨l, r⟩ := p
  simp only at hl hL hlr ⊢
  rw [isGap_iff] at hl hL
  rw [RJLemmaJ.cut_iff_cutChar]
  unfold RJLemmaJ.cutChar
  simp only [EltBridge.Elt.toPathData_d, EltBridge.Elt.toPathData_kstar, tp_eps, tp_delta]
  split_ifs with h0 hks
  · subst h0
    constructor
    · rintro (⟨hk', hd, -⟩ | ⟨hk', -⟩)
      · exact Or.inl ⟨rfl, hk', hd⟩
      · exact absurd hk' hk
    · rintro (⟨-, hk', hd⟩ | ⟨h, -⟩)
      · exact Or.inl ⟨hk', hd, hl.1⟩
      · exact absurd h.symm hk
  · subst hks
    constructor
    · rintro (⟨hk', hδ, hd, -⟩ | ⟨hk', -, -, hd⟩)
      · exact Or.inr ⟨rfl, hk', hδ, hd⟩
      · exfalso; apply hL; refine ⟨hd, ?_, ?_⟩ <;> omega
    · rintro (⟨h, -⟩ | ⟨-, hk', hδ, hd⟩)
      · exact absurd h h0
      · exact Or.inl ⟨hk', hδ, hd, hl.1⟩
  · constructor
    · rintro ⟨hd1, -, ht⟩
      rw [travel_eq_zero_iff] at ht
      exfalso; apply hL; exact ⟨hd1, ht⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h h0
      · exact absurd h hks

/-- **Right end of a run = Lemma J junction slot.**  The end site `r+1` is cut iff it is site
`kstar` with `kstar < 0`, `delta = 1` and `d kstar = eps` (Lemma J (d)); site `0` can never be
the cut right end of a run, and neither can a bulk site. -/
theorem cut_right_iff (hk : g.kstar ≠ 0) {p : ℤ × ℤ} (hp : p ∈ runs g) :
    g.toPathData.cut (p.2 + 1) ↔
      (p.2 + 1 = g.kstar ∧ g.kstar < 0 ∧ g.delta = true ∧ g.d g.kstar = g.eps) := by
  rw [mem_runs] at hp
  obtain ⟨-, -, hlr, hg, -, hR⟩ := hp
  have hr := hg p.2 hlr le_rfl
  obtain ⟨l, r⟩ := p
  simp only at hr hR hlr ⊢
  rw [isGap_iff] at hr hR
  rw [RJLemmaJ.cut_iff_cutChar]
  unfold RJLemmaJ.cutChar
  simp only [EltBridge.Elt.toPathData_d, EltBridge.Elt.toPathData_kstar, tp_eps, tp_delta]
  have hr' : r + 1 - 1 = r := by ring
  split_ifs with h0 hks
  · constructor
    · rintro (⟨hk', -, hd0⟩ | ⟨hk', -⟩)
      · exfalso; apply hR; rw [h0]; refine ⟨hd0, ?_, ?_⟩ <;> omega
      · exact absurd hk' hk
    · rintro ⟨h, -⟩; exact absurd (h0 ▸ h).symm hk
  · rw [← hks]
    constructor
    · rintro (⟨hk', -, -, hd⟩ | ⟨hk', hδ, hd, -⟩)
      · exfalso; apply hR; refine ⟨hd, ?_, ?_⟩ <;> omega
      · exact ⟨rfl, by omega, hδ, hd⟩
    · rintro ⟨-, hk', hδ, hd⟩
      right; refine ⟨by omega, hδ, hd, ?_⟩
      rw [hr']; exact hr.1
  · constructor
    · rintro ⟨-, hd2, ht⟩
      rw [travel_eq_zero_iff, hr'] at ht
      exfalso; apply hR; refine ⟨hd2, ?_, ?_⟩ <;> omega
    · rintro ⟨h, -⟩; exact absurd h hks

/-- **At most one end of a run is cut**, so `shield ∈ {0,1}` is well defined as `L` minus the
cut count. -/
theorem not_both_ends_cut (hk : g.kstar ≠ 0) {p : ℤ × ℤ} (hp : p ∈ runs g) :
    ¬ (g.toPathData.cut p.1 ∧ g.toPathData.cut (p.2 + 1)) := by
  rintro ⟨h1, h2⟩
  have hlr := ((mem_runs g).1 hp).2.2.1
  rw [cut_left_iff g hk hp] at h1
  rw [cut_right_iff g hk hp] at h2
  omega

/-! ### Runs cover the cut sites, and their site-closures are disjoint -/

/-- Every gap edge of the span lies in a maximal run (`kstar ≠ 0`). -/
theorem exists_run (hk : g.kstar ≠ 0) (j : ℤ) (hA : ATrue g ≤ j) (hB : j ≤ BTrue g)
    (hj : IsGap g j) : ∃ p ∈ runs g, p.1 ≤ j ∧ j ≤ p.2 := by
  classical
  set Sl := (Finset.Icc (ATrue g) j).filter (fun i => ∀ t, i ≤ t → t ≤ j → IsGap g t) with hSl
  set Sr := (Finset.Icc j (BTrue g)).filter (fun i => ∀ t, j ≤ t → t ≤ i → IsGap g t) with hSr
  have hjl : j ∈ Sl := by
    rw [hSl, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hA, le_rfl⟩, fun t h1 h2 => by rw [show t = j by omega]; exact hj⟩
  have hjr : j ∈ Sr := by
    rw [hSr, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hB⟩, fun t h1 h2 => by rw [show t = j by omega]; exact hj⟩
  set l := Sl.min' ⟨j, hjl⟩ with hl
  set r := Sr.max' ⟨j, hjr⟩ with hr
  have hlmem : l ∈ Sl := Finset.min'_mem _ _
  have hrmem : r ∈ Sr := Finset.max'_mem _ _
  rw [hSl, Finset.mem_filter, Finset.mem_Icc] at hlmem
  rw [hSr, Finset.mem_filter, Finset.mem_Icc] at hrmem
  obtain ⟨⟨hAl, hlj⟩, hlg⟩ := hlmem
  obtain ⟨⟨hjr', hrB⟩, hrg⟩ := hrmem
  have hlA : ATrue g < l := by
    rcases hAl.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hlg l le_rfl hlj) (not_gap_ATrue g hk)
  have hrB' : r < BTrue g := by
    rcases hrB.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hrg r hjr' le_rfl) (not_gap_BTrue g hk)
  refine ⟨(l, r), ?_, hlj, hjr'⟩
  rw [mem_runs]
  refine ⟨⟨hAl, by omega⟩, ⟨by omega, hrB⟩, by omega, ?_, ?_, ?_⟩
  · intro t h1 h2
    rcases le_total t j with h | h
    · exact hlg t h1 h
    · exact hrg t h h2
  · intro hg
    have hmem : l - 1 ∈ Sl := by
      rw [hSl, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, fun t h1 h2 => ?_⟩
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact hg
      · exact hlg t (by omega) h2
    have := Finset.min'_le Sl (l - 1) hmem
    rw [← hl] at this
    omega
  · intro hg
    have hmem : r + 1 ∈ Sr := by
      rw [hSr, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, fun t h1 h2 => ?_⟩
      rcases eq_or_lt_of_le h2 with h | h
      · rw [h]; exact hg
      · exact hrg t h1 (by omega)
    have := Finset.le_max' Sr (r + 1) hmem
    rw [← hr] at this
    omega

/-- Two runs whose closed site ranges `[l, r+1]` meet are equal. -/
theorem run_eq_of_overlap {p q : ℤ × ℤ} (hp : p ∈ runs g) (hq : q ∈ runs g) (s : ℤ)
    (hs1 : p.1 ≤ s ∧ s ≤ p.2 + 1) (hs2 : q.1 ≤ s ∧ s ≤ q.2 + 1) : p = q := by
  rw [mem_runs] at hp hq
  obtain ⟨-, -, hp1, hpg, hpL, hpR⟩ := hp
  obtain ⟨-, -, hq1, hqg, hqL, hqR⟩ := hq
  have hl : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exfalso
      by_cases hx : q.1 - 1 ≤ p.2
      · exact hqL (hpg _ (by omega) hx)
      · omega
    · exact h
    · exfalso
      by_cases hx : p.1 - 1 ≤ q.2
      · exact hpL (hqg _ (by omega) hx)
      · omega
  have hr : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · exact absurd (hqg _ (by omega) (by omega)) hpR
    · exact h
    · exact absurd (hpg _ (by omega) (by omega)) hqR
  exact Prod.ext hl hr

/-! ### Per-run count -/

open Classical in
/-- A run `[l, r]` contributes its `r - l = L - 1` interior sites, all cut, plus its cut end
sites. -/
theorem run_count (hk : g.kstar ≠ 0) (l r : ℤ) (hlr : l ≤ r)
    (hg : ∀ j, l ≤ j → j ≤ r → IsGap g j) :
    ((Finset.Icc l (r + 1)).filter g.toPathData.cut).card =
      (r - l).toNat + (if g.toPathData.cut l then 1 else 0)
        + (if g.toPathData.cut (r + 1) then 1 else 0) := by
  have hI : Finset.Icc l (r + 1) = insert l (insert (r + 1) (Finset.Ioo l (r + 1))) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]; omega
  have hint : (Finset.Ioo l (r + 1)).filter g.toPathData.cut = Finset.Ioo l (r + 1) := by
    apply Finset.filter_true_of_mem
    intro s hs
    rw [Finset.mem_Ioo] at hs
    exact cut_of_gap_gap g hk s (hg _ (by omega) (by omega)) (hg _ (by omega) (by omega))
  have hcard : (Finset.Ioo l (r + 1)).card = (r - l).toNat := by
    rw [Int.card_Ioo]; congr 1; ring
  have hn1 : r + 1 ∉ Finset.Ioo l (r + 1) := by simp
  have hn2 : l ∉ Finset.Ioo l (r + 1) := by simp
  have hn3 : l ≠ r + 1 := by omega
  rw [hI, Finset.filter_insert, Finset.filter_insert, hint]
  by_cases h1 : g.toPathData.cut l <;> by_cases h2 : g.toPathData.cut (r + 1) <;>
    simp only [h1, h2, if_true, if_false] <;>
    simp [Finset.card_insert_of_notMem, hn1, hn2, hn3, hcard]

/-! ### The corollary -/

open Classical in
/-- **Room 62L corollary, count form.**  For `kstar ≠ 0`,

  `cTrue g = ∑_{(l,r) ∈ runs g} ((L - 1) + [cut l] + [cut (r+1)])`,  `L - 1 = r - l`. -/
theorem cTrue_eq_sum_runs (hk : g.kstar ≠ 0) :
    cTrue g = ∑ p ∈ runs g,
      ((p.2 - p.1).toNat + (if g.toPathData.cut p.1 then 1 else 0)
        + (if g.toPathData.cut (p.2 + 1) then 1 else 0)) := by
  classical
  have h0 : cTrue g = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
    unfold cTrue
    rw [if_neg (fun h => hk h.1.1), add_zero]
  have hU : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut =
      (runs g).biUnion (fun p => (Finset.Icc p.1 (p.2 + 1)).filter g.toPathData.cut) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hA, hB⟩, hc⟩
      rcases cut_adj_gap g hk s hc with hg | hg
      · obtain ⟨p, hp, h1, h2⟩ := exists_run g hk (s - 1) (by omega) (by omega) hg
        exact ⟨p, hp, ⟨by omega, by omega⟩, hc⟩
      · obtain ⟨p, hp, h1, h2⟩ := exists_run g hk s (by omega) (by omega) hg
        exact ⟨p, hp, ⟨by omega, by omega⟩, hc⟩
    · rintro ⟨p, hp, ⟨h1, h2⟩, hc⟩
      have := runs_inside g hk hp
      exact ⟨⟨by omega, by omega⟩, hc⟩
  rw [h0, hU, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' := (mem_runs g).1 hp
    exact run_count g hk p.1 p.2 hp'.2.2.1 hp'.2.2.2.1
  · intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs1 hs2
    exact hpq (run_eq_of_overlap g hp hq s hs1.1 hs2.1)

/-- **Room 62L corollary, `L - shield` form.**  For `kstar ≠ 0`,

  `cTrue g = ∑_{runs} (L - shield)`,

with `L = r - l + 1` the run length and `shield = 0` iff an end site of the run is cut (which,
by `cut_left_iff` / `cut_right_iff`, happens only at a Lemma J junction slot), else `1`. -/
theorem cTrue_eq_sum_L_sub_shield (hk : g.kstar ≠ 0) :
    cTrue g = ∑ p ∈ runs g, (runLen p - shield g p) := by
  classical
  rw [cTrue_eq_sum_runs g hk]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hlr := ((mem_runs g).1 hp).2.2.1
  have hnb := not_both_ends_cut g hk hp
  have key : (p.2 - p.1 + 1).toNat = (p.2 - p.1).toNat + 1 := by omega
  unfold runLen shield
  by_cases h1 : g.toPathData.cut p.1 <;> by_cases h2 : g.toPathData.cut (p.2 + 1)
  · exact absurd ⟨h1, h2⟩ hnb
  · simp [h1, h2, key]
  · simp [h1, h2, key]
  · simp [h1, h2, key]

/-- **Same, with the shield read off Lemma J.**  The run's contribution is `L` when one of its
ends is a junction slot satisfying the J condition, and `L - 1` otherwise. -/
theorem cTrue_eq_sum_junction (hk : g.kstar ≠ 0) :
    cTrue g = ∑ p ∈ runs g,
      (runLen p - (if (p.1 = 0 ∧ g.kstar < 0 ∧ g.d (-1) = 1) ∨
          (p.1 = g.kstar ∧ 0 < g.kstar ∧ g.delta = false ∧ g.d (g.kstar - 1) = -g.eps) ∨
          (p.2 + 1 = g.kstar ∧ g.kstar < 0 ∧ g.delta = true ∧ g.d g.kstar = g.eps)
        then 0 else 1)) := by
  classical
  rw [cTrue_eq_sum_L_sub_shield g hk]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  unfold shield
  congr 1
  exact if_congr (by rw [cut_left_iff g hk hp, cut_right_iff g hk hp, or_assoc]) rfl rfl

end GapRuns

#print axioms GapRuns.travel_eq_zero_iff
#print axioms GapRuns.isGap_iff
#print axioms GapRuns.mem_occTrue_iff
#print axioms GapRuns.origin_edge_occ
#print axioms GapRuns.occTrue_nonempty
#print axioms GapRuns.ATrue_eq_min
#print axioms GapRuns.BTrue_eq_max
#print axioms GapRuns.not_gap_ATrue
#print axioms GapRuns.not_gap_BTrue
#print axioms GapRuns.mem_runs
#print axioms GapRuns.runs_inside
#print axioms GapRuns.cut_adj_gap
#print axioms GapRuns.cut_of_gap_gap
#print axioms GapRuns.cut_left_iff
#print axioms GapRuns.cut_right_iff
#print axioms GapRuns.not_both_ends_cut
#print axioms GapRuns.exists_run
#print axioms GapRuns.run_eq_of_overlap
#print axioms GapRuns.run_count
#print axioms GapRuns.cTrue_eq_sum_runs
#print axioms GapRuns.cTrue_eq_sum_L_sub_shield
#print axioms GapRuns.cTrue_eq_sum_junction
