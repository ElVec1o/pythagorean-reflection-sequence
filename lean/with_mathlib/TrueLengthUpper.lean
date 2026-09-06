/-
  TrueLengthUpper.lean
  ====================
  **The UPPER half of the metric identity, and only the upper half.**

  `paper/journal/merged_novel_paper.tex`, remark "what is not claimed" (~line 136):

      "The lower bound of the metric identity  ell_T = ell_R + 2c  is open;
       only the upper bound is PROVED."

  A 2026-08-09 retraction found the previous lower-bound chain circular
  (`thm:Bproved` is FALSE).  Nothing in this file touches the lower bound, and a green
  `lake build` on this file must NOT be read as evidence for the identity.

  What this file adds to `EltBridge`:

  * a COUNTED reachability toolkit.  `EltBridge`'s reachability development
    (`reachable_of_trivial`, `reachable_single_correction_int`,
    `reachable_multi_correction_int`) proves `Reachable g = exists n, Reaches n g` and
    never tracks `n`, so it yields no bound on `wordLength` at all.  `Reaches.s1`,
    `Reaches.s2`, `Reaches.s3`, `Reaches.feps`, `Reaches.roundTrip` below are the same
    moves with their step counts, and they are what an upper bound needs.

  * `wordLength_le_lR_add_two_c_of_trivial`: the target inequality
    `wordLength g <= lR g + 2 * c g`, PROVED on the explicit class `kstar = 0`,
    `d = 0` (four group elements, `one`, `s1 one`, `s2 one`, `s1 (s2 one)`).

  * `wordLength_trav_le`: the same inequality on an INFINITE explicit class, the
    pure-travel elements `trav n` (cursor at `n + 1`, `eps = -1`, `delta = false`,
    deposits exactly the travel indicator, so GAP-FREE).  There it is an equality:
    `Reaches (2 * n + 2) (trav n)` by an explicit word `s2 s3 (s1 s3)^n`, and
    `lR (trav n) = 2 * n + 2`, `c (trav n) = 0`.

  * `witElt` and `witNeg` re-checked as witnesses, both TIGHT:
    `Reaches 4 witElt` with `lR witElt = 4`, `c witElt = 0`  (4 <= 4 + 0);
    `Reaches 16 witNeg` with `lR witNeg = 14`, `c witNeg = 1`  (16 <= 14 + 2).
    `witNeg` is the one with a non-zero defect, so it is the check that the `2 * c`
    term is carrying weight rather than being carried.

  * `not_isTrueLength_wordLength_c`: the metric identity itself, `IsTrueLength
    wordLength c`, is FALSE in Lean already at `one` -- `wordLength one = 0` while
    `lR one = 2` (`one_toPathData_lR`) and `c one = 0`.  That is the `+2` artifact
    of `mu` reading `2` at a coordinate with neither deposit nor travel, and it is a
    separate defect of the pairing from the `gBad` one below.

  * **`gBad`, a counterexample to the inequality in its unrestricted form.**  With
    `Elt.c := (pdCutSites _).card` -- the `|Z|` of `prop:cut`, which is the only defect
    the Lean development defines -- the sentence `forall g, wordLength g <= lR g + 2 * c g`
    is FALSE.  `gBad` is the element `kstar = 0`, `eps = 1`, `delta = false`,
    `d = 2 . [j = 1]`.  This file proves `lR gBad = 8` and `c gBad = 0`, so the
    inequality would force `wordLength gBad <= 8`; it also proves `Reaches 10 gBad` by
    exhibiting the word.  An exhaustive BFS over the Cayley graph of `{s1,s2,s3}`
    (`code/zeta_probe/tools/nogap/src/bin/truelen_check.rs`, depth 17, 13963 elements)
    reports `wordLength gBad = 10`, i.e. no word of length `<= 8` exists.  The BFS half
    of that is NOT formalised here and is not claimed to be: certifying it in Lean is
    the open lower-bound direction.

    The census also says exactly where the boundary is.  Writing "gap edge" for a
    `j` in the span with `d j = 0` and `travel j = 0` (the case `mu` forces to `2`),
    and `D = wordLength - (lR + 2 * c)`, over all 13963 elements of word length
    at most 17:

        gap-free      7588 elements   D = 0 for every one of them  (the identity, EXACT)
        with a gap    3073            D = -4    upper bound holds, slack 4
                      1932            D = -2    upper bound holds, slack 2
                      1360            D =  0
                        10            D = +2    UPPER BOUND FAILS

    So `Elt.c = |Z|` is the right defect precisely on the gap-free class, which is
    `thm:nogap`'s hypothesis, and is the wrong one off it.  A general upper bound must
    either restrict to gap-free elements or replace `Elt.c` by the true component
    defect, which BLOCK 331 already recorded as unidentified.

    PRIOR ART, same night, independent: BLOCK 343 (`LipschitzPotential.lean`) found the
    SAME element as its "smallest undershoot" (`d 1 = -2`, the sign-flipped `gBad`) while
    testing whether `lR + 2c` is a 1-Lipschitz potential, and diagnosed the root cause
    this file's gap-free/gap split measures from the outside: `SiteCost.PathData` carries
    `hA : A <= 0` and `hB : 0 <= B`, so edge `0` is in the span of EVERY element, and
    `mu` then charges `2` for it whenever it is a gap edge.  That is why the failures
    all carry a gap edge, and why `one` itself has `lR = 2` rather than `0`.  This file
    is the counterexample formalised on the other side of the identity -- `lR gBad`,
    `c gBad` and an explicit length-`10` word, none of which BLOCK 343 has -- plus the
    two classes on which the upper bound is provable as stated.

  No `sorry`, no `native_decide`.
-/

import EltBridge

open SiteCost

namespace EltBridge
namespace Elt

/-! ## 1. The counted reachability toolkit

`EltBridge` has `reachable_s1`/`reachable_s2`/`reachable_s3`, which forget the count.
These are the same three moves with the count kept, and they are the only reason an
upper bound on `wordLength` is reachable at all. -/

/-- One `s1` step. -/
theorem Reaches.s1 {n : ℕ} {g : Elt} (h : Reaches n g) : Reaches (n + 1) (Elt.s1 g) :=
  Reaches.step h (Or.inl (SameElt.refl _))

/-- One `s2` step. -/
theorem Reaches.s2 {n : ℕ} {g : Elt} (h : Reaches n g) : Reaches (n + 1) (Elt.s2 g) :=
  Reaches.step h (Or.inr (Or.inl (SameElt.refl _)))

/-- One `s3` step. -/
theorem Reaches.s3 {n : ℕ} {g : Elt} (h : Reaches n g) : Reaches (n + 1) (Elt.s3 g) :=
  Reaches.step h (Or.inr (Or.inr (SameElt.refl _)))

/-- The sign flip `feps = s1 . s2` costs exactly two steps. -/
theorem Reaches.feps {n : ℕ} {g : Elt} (h : Reaches n g) : Reaches (n + 2) (Elt.feps g) :=
  h.s2.s1

/-- The round trip of `roundTrip_left` costs exactly four steps. -/
theorem Reaches.roundTrip {n : ℕ} {g : Elt} (h : Reaches n g) :
    Reaches (n + 4) (Elt.s3 (Elt.s1 (Elt.s2 (Elt.s3 g)))) :=
  h.s3.s2.s1.s3

/-- `Reaches 0 one`. -/
theorem Reaches.one : Reaches 0 Elt.one := Reaches.refl (SameElt.refl _)

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-! ## 2. The target inequality on the trivial class

The class is `kstar = 0` and `d = 0`: four group elements, distinguished by
`(eps, delta)`.  `reachable_of_trivial` already shows they are words; the point here is
the COUNT, which it discards.  With the count, `wordLength <= 2`, and `lR` of such an
element is at least `2` because its span is the single edge `0`, which carries neither
deposit nor travel and so is exactly the coordinate `SiteCost.PathData.mu` forces to
`2`.  So the target inequality holds on this class -- with slack `2` at `one` itself,
the slack `one_toPathData_lR` records. -/

/-- **Counted `reachable_of_trivial`.**  Every element with the cursor at `0` and no
deposits is a word of length at most `2`. -/
theorem reaches_two_of_trivial (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    ∃ n ≤ 2, Reaches n g := by
  rcases g.heps with he | he
  · by_cases hδ : g.delta = true
    · exact ⟨1, by omega, Reaches.congr (Reaches.one.s1)
        ⟨by simp [one, Elt.s1, hk], by simp [one, Elt.s1, he],
         by simp [one, Elt.s1, hδ], by simp [one, Elt.s1, hd]⟩⟩
    · simp only [Bool.not_eq_true] at hδ
      exact ⟨0, by omega, Reaches.congr Reaches.one
        ⟨by simp [one, hk], by simp [one, he], by simp [one, hδ], by simp [one, hd]⟩⟩
  · by_cases hδ : g.delta = true
    · exact ⟨1, by omega, Reaches.congr (Reaches.one.s2)
        ⟨by simp [one, Elt.s2, hk], by simp [one, Elt.s2, he],
         by simp [one, Elt.s2, hδ], by simp [one, Elt.s2, hd]⟩⟩
    · simp only [Bool.not_eq_true] at hδ
      exact ⟨2, by omega, Reaches.congr (Reaches.one.s2.s1)
        ⟨by simp [one, Elt.s1, Elt.s2, hk], by simp [one, Elt.s1, Elt.s2, he],
         by simp [one, Elt.s1, Elt.s2, hδ], by simp [one, Elt.s1, Elt.s2, hd]⟩⟩

/-- **`wordLength <= 2` on the trivial class.** -/
theorem wordLength_le_two_of_trivial (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    wordLength g ≤ 2 := by
  obtain ⟨n, hn2, hn⟩ := reaches_two_of_trivial g hk hd
  exact le_trans (wordLength_le hn) hn2

/-- The span of a trivial element is the single edge `0`. -/
theorem trivial_occ (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    g.occ = ({0} : Finset ℤ) := by
  classical
  have hfil : g.supp.filter (fun j => g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    rw [hk, hd]
    simp [SiteCost.travel_of_kstar_zero]
  unfold occ
  rw [hfil]
  rfl

theorem trivial_A (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) : g.A = 0 := by
  have h : g.A ∈ g.occ := Finset.min'_mem _ _
  rw [trivial_occ g hk hd, Finset.mem_singleton] at h
  exact h

theorem trivial_B (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) : g.B = 0 := by
  have h : g.B ∈ g.occ := Finset.max'_mem _ _
  rw [trivial_occ g hk hd, Finset.mem_singleton] at h
  exact h

/-- **`2 <= lR` on the trivial class.**  The single span edge carries neither deposit
nor travel, so `mu` reads `2` there. -/
theorem two_le_lR_of_trivial (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    2 ≤ g.lR := by
  have hmu : g.toPathData.mu 0 = 2 := by
    unfold SiteCost.PathData.mu
    simp [Elt.toPathData, hk, hd, SiteCost.travel_of_kstar_zero]
  have hsum : ∑ j ∈ Finset.Icc g.toPathData.A g.toPathData.B, g.toPathData.mu j = 2 := by
    rw [toPathData_A, toPathData_B, trivial_A g hk hd, trivial_B g hk hd,
      Finset.Icc_self]
    simpa using hmu
  unfold Elt.lR SiteCost.PathData.lR
  omega

/-- **The target inequality, PROVED on the trivial class.**  This is the upper half of
`ell_T = ell_R + 2c` -- the lower half is open (see the file header). -/
theorem wordLength_le_lR_add_two_c_of_trivial (g : Elt)
    (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    wordLength g ≤ g.lR + 2 * c g := by
  have h1 := wordLength_le_two_of_trivial g hk hd
  have h2 := two_le_lR_of_trivial g hk hd
  omega

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-! ## 3. `gBad`: the unrestricted inequality is FALSE

`gBad` is the cursor back at `0` with a single deposit `2` at edge `1`.  Its span is
`[0,1]`; edge `0` carries neither deposit nor travel, so it is a *gap edge* and `mu`
reads `2` there.  Then `lR gBad = 8` and `c gBad = 0`, so
`wordLength gBad <= lR gBad + 2 * c gBad` would say `wordLength gBad <= 8`.  The
exhaustive BFS of `truelen_check.rs` says `wordLength gBad = 10`.  The word of length
`10` is exhibited below; the BFS half (that `8` is impossible) is the open lower-bound
direction and is NOT formalised. -/

/-- The counterexample element: `kstar = 0`, `eps = 1`, `delta = false`, `d = 2 . [j=1]`. -/
noncomputable def gBad : Elt where
  kstar := 0
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun j => if j = 1 then 2 else 0
  hpar := by
    intro j
    rw [SiteCost.travel_of_kstar_zero]
    by_cases h : j = 1 <;> simp [h]
  supp := {1}
  hsupp := by
    intro j hj
    have h1 : j ≠ 1 := by intro hc; exact hj (by simp [hc])
    exact ⟨by simp [h1], SiteCost.travel_of_kstar_zero j⟩

/-- The geodesic word for `gBad`, read left to right: `s1 s3 s2 s3 s1 s2 s3 s1 s3 s1`. -/
noncomputable def wBad : Elt :=
  s1 (s3 (s1 (s3 (s2 (s1 (s3 (s2 (s3 (s1 one)))))))))

theorem reaches_wBad : Reaches 10 wBad :=
  Reaches.one.s1.s3.s2.s3.s1.s2.s3.s1.s3.s1

theorem wBad_kstar : wBad.kstar = 0 := by
  simp [wBad, s1, s2, s3, one]

theorem wBad_eps : wBad.eps = 1 := by
  simp [wBad, s1, s2, s3, one]

theorem wBad_delta : wBad.delta = false := by
  simp [wBad, s1, s2, s3, one]

theorem wBad_d : wBad.d = fun j => if j = 1 then 2 else 0 := by
  funext j
  by_cases h1 : j = 1
  · subst h1
    norm_num [wBad, s1, s2, s3, one, Function.update_apply]
  · by_cases h0 : j = 0
    · subst h0
      norm_num [wBad, s1, s2, s3, one, Function.update_apply]
    · norm_num [wBad, s1, s2, s3, one, Function.update_apply, h0, h1]

end Elt
end EltBridge

namespace EltBridge
namespace Elt

theorem wBad_sameElt : SameElt wBad gBad :=
  ⟨by rw [wBad_kstar]; rfl, by rw [wBad_eps]; rfl, by rw [wBad_delta]; rfl,
   by rw [wBad_d]; rfl⟩

/-- **`gBad` is a word of length `10`.** -/
theorem reaches_gBad : Reaches 10 gBad := Reaches.congr reaches_wBad wBad_sameElt

theorem wordLength_gBad_le : wordLength gBad ≤ 10 := wordLength_le reaches_gBad

/-! ### The span, `lR` and `c` of `gBad` -/

theorem gBad_occ : gBad.occ = ({0, 1} : Finset ℤ) := by
  classical
  ext x
  simp only [occ, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · simp [h]
    · simpa [gBad] using Or.inr h
  · rintro (h | h) <;> subst h
    · exact Or.inl rfl
    · exact Or.inr ⟨by simp [gBad], Or.inl (by simp [gBad])⟩

theorem gBad_A : gBad.A = 0 := by
  have hm : gBad.A ∈ gBad.occ := Finset.min'_mem _ _
  have hle : gBad.A ≤ 0 := Finset.min'_le _ _ (by rw [gBad_occ]; simp)
  rw [gBad_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem gBad_B : gBad.B = 1 := by
  have hm : gBad.B ∈ gBad.occ := Finset.max'_mem _ _
  have hle : (1 : ℤ) ≤ gBad.B := Finset.le_max' _ _ (by rw [gBad_occ]; simp)
  rw [gBad_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

@[simp] theorem gBad_pd_A : gBad.toPathData.A = 0 := gBad_A
@[simp] theorem gBad_pd_B : gBad.toPathData.B = 1 := gBad_B

theorem gBad_width : pdWidth gBad.toPathData = 2 := by
  unfold pdWidth
  rw [gBad_pd_A, gBad_pd_B]
  rfl

/-- **`gBad` has no cut site**, so `c gBad = 0`.  The only interior site of its span is
site `1`, and `beta` there is the deposit `2`. -/
theorem gBad_cutSites : pdCutSites gBad.toPathData = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_pdCutSites, gBad_width] at hs
  obtain ⟨⟨h1, h2⟩, hcut⟩ := hs
  have hs1 : s = 1 := by omega
  subst hs1
  obtain ⟨-, hb, -⟩ := hcut
  rw [gBad_pd_A] at hb
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD at hb
  norm_num [gBad, Elt.toPathData] at hb

theorem gBad_c : c gBad = 0 := by
  unfold c
  rw [gBad_cutSites]
  rfl

end Elt
end EltBridge

namespace EltBridge
namespace Elt

/-- `mu` at the gap edge `0` of `gBad`: neither deposit nor travel, so `2`. -/
theorem gBad_mu0 : gBad.toPathData.mu 0 = 2 := by
  unfold SiteCost.PathData.mu
  simp [Elt.toPathData, gBad, SiteCost.travel_of_kstar_zero]

theorem gBad_mu1 : gBad.toPathData.mu 1 = 2 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, gBad, SiteCost.travel_of_kstar_zero]

theorem gBad_site0 : gBad.toPathData.siteCost 0 = 0 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, gBad]

theorem gBad_site1 : gBad.toPathData.siteCost 1 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, gBad]

theorem gBad_site2 : gBad.toPathData.siteCost 2 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, gBad]

/-- **`lR gBad = 8`.**  Two edges at `mu = 2` each (edge `0` is a gap edge, edge `1`
carries the deposit `2`) and site costs `0, 2, 2`. -/
theorem gBad_lR : gBad.lR = 8 := by
  have hIcc1 : Finset.Icc (0 : ℤ) 1 = ({0, 1} : Finset ℤ) := by decide
  have hIcc2 : Finset.Icc (0 : ℤ) (1 + 1) = ({0, 1, 2} : Finset ℤ) := by decide
  unfold Elt.lR SiteCost.PathData.lR
  rw [toPathData_A, toPathData_B, gBad_A, gBad_B, hIcc1, hIcc2]
  norm_num [gBad_mu0, gBad_mu1, gBad_site0, gBad_site1, gBad_site2]

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-! ## 4. What the counterexample says

`UpperBound` is the sentence this file's target would be if it held for every `g`.  It
does not: it forces `wordLength gBad <= 8`, while the exhaustive BFS over the Cayley
graph of `{s1, s2, s3}` (`truelen_check.rs`) reports `wordLength gBad = 10`, and
`reaches_gBad` above exhibits the length-`10` word.  The BFS half is not formalised --
proving `9 <= wordLength gBad` is a LOWER bound on `wordLength`, i.e. the open
direction.

The identity itself is refutable in Lean outright, and already at `one`: `wordLength`
is `0` there while `lR` is `2` (`one_toPathData_lR`) and `c` is `0`. -/

/-- The unrestricted upper bound, as a sentence. -/
def UpperBound : Prop := ∀ g : Elt, wordLength g ≤ g.lR + 2 * c g

/-- **What `UpperBound` would force at `gBad`**: a word of length at most `8`.  The BFS
says the shortest is `10`. -/
theorem upperBound_forces_gBad_le_eight (h : UpperBound) : wordLength gBad ≤ 8 := by
  have hg := h gBad
  rw [gBad_lR, gBad_c] at hg
  omega

theorem one_A : one.A = 0 := trivial_A one rfl rfl
theorem one_B : one.B = 0 := trivial_B one rfl rfl

theorem one_width : pdWidth one.toPathData = 1 := by
  unfold pdWidth
  rw [toPathData_A, toPathData_B, one_A, one_B]
  rfl

theorem one_cutSites : pdCutSites one.toPathData = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨h1, h2⟩ := pdCutSites_interior _ hs
  rw [one_width] at h2
  omega

theorem one_c : c one = 0 := by
  unfold c
  rw [one_cutSites]
  rfl

/-- **The metric identity is FALSE for `wordLength` against `c = |Z|`**, already at the
identity: `wordLength one = 0` but `lR one + 2 * c one = 2`.  This is the `+2` artifact
`one_toPathData_lR` records -- `mu` reads `2` at a coordinate with neither deposit nor
travel, and `one`'s only span edge is such a coordinate. -/
theorem not_isTrueLength_wordLength_c : ¬ IsTrueLength wordLength c := by
  intro h
  have h1 := h one
  rw [wordLength_one, one_c] at h1
  have h2 : one.lR = 2 := one_toPathData_lR
  omega

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-! ## 5. The named witnesses

`witElt` and `witNeg` are `EltBridge`'s two concrete group elements.  Both satisfy the
target inequality, and both satisfy it TIGHTLY -- with equality -- which is what makes
them non-vacuous checks rather than slack ones. -/

/-- The word for `witElt`, read left to right: `s2 s3 s1 s2`. -/
noncomputable def wWit : Elt := s2 (s1 (s3 (s2 one)))

theorem reaches_wWit : Reaches 4 wWit := Reaches.one.s2.s3.s1.s2

theorem wWit_kstar : wWit.kstar = 1 := by simp [wWit, s1, s2, s3, one]
theorem wWit_eps : wWit.eps = 1 := by simp [wWit, s1, s2, s3, one]
theorem wWit_delta : wWit.delta = false := by simp [wWit, s1, s2, s3, one]

theorem wWit_d : wWit.d = fun j => if j = 0 then 1 else 0 := by
  funext j
  by_cases h0 : j = 0
  · subst h0; norm_num [wWit, s1, s2, s3, one, Function.update_apply]
  · norm_num [wWit, s1, s2, s3, one, Function.update_apply, h0]

theorem wWit_sameElt : SameElt wWit witElt :=
  ⟨by rw [wWit_kstar]; rfl, by rw [wWit_eps]; rfl, by rw [wWit_delta]; rfl,
   by rw [wWit_d]; rfl⟩

/-- **`witElt` is a word of length `4`.** -/
theorem reaches_witElt : Reaches 4 witElt := Reaches.congr reaches_wWit wWit_sameElt

theorem witElt_c : c witElt = 0 := by
  unfold c
  rw [witElt_cutSites]
  rfl

theorem witElt_mu0 : witElt.toPathData.mu 0 = 1 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, witElt, SiteCost.travel]

theorem witElt_site0 : witElt.toPathData.siteCost 0 = 1 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witElt]

theorem witElt_site1 : witElt.toPathData.siteCost 1 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witElt]

/-- **`lR witElt = 4`.** -/
theorem witElt_lR : witElt.lR = 4 := by
  have hIcc0 : Finset.Icc (0 : ℤ) 0 = ({0} : Finset ℤ) := Finset.Icc_self 0
  have hIcc1 : Finset.Icc (0 : ℤ) (0 + 1) = ({0, 1} : Finset ℤ) := by decide
  unfold Elt.lR SiteCost.PathData.lR
  rw [toPathData_A, toPathData_B, witElt_A, witElt_B, hIcc0, hIcc1]
  norm_num [witElt_mu0, witElt_site0, witElt_site1]

/-- **The target inequality at `witElt`, tight.** -/
theorem wordLength_witElt_le : wordLength witElt ≤ witElt.lR + 2 * c witElt := by
  have h := wordLength_le reaches_witElt
  rw [witElt_lR, witElt_c]
  omega

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-- The word for `witNeg`, read left to right:
`s1 s3 s1 s3 s2 s3 s1 s2 s3 s1 s3 s1 s3 s2 s3 s2`. -/
noncomputable def wNeg : Elt :=
  s2 (s3 (s2 (s3 (s1 (s3 (s1 (s3 (s2 (s1 (s3 (s2 (s3 (s1 (s3 (s1 one)))))))))))))))

theorem reaches_wNeg : Reaches 16 wNeg :=
  Reaches.one.s1.s3.s1.s3.s2.s3.s1.s2.s3.s1.s3.s1.s3.s2.s3.s2

theorem wNeg_kstar : wNeg.kstar = -1 := by simp [wNeg, s1, s2, s3, one]
theorem wNeg_eps : wNeg.eps = 1 := by simp [wNeg, s1, s2, s3, one]
theorem wNeg_delta : wNeg.delta = false := by simp [wNeg, s1, s2, s3, one]

theorem wNeg_d : wNeg.d = fun j => if j = -1 then -1 else if j = 2 then 2 else 0 := by
  funext j
  by_cases hm : j = -1
  · subst hm; norm_num [wNeg, s1, s2, s3, one, Function.update_apply]
  · by_cases h2 : j = 2
    · subst h2; norm_num [wNeg, s1, s2, s3, one, Function.update_apply]
    · by_cases h0 : j = 0
      · subst h0; norm_num [wNeg, s1, s2, s3, one, Function.update_apply]
      · by_cases h1 : j = 1
        · subst h1; norm_num [wNeg, s1, s2, s3, one, Function.update_apply]
        · norm_num [wNeg, s1, s2, s3, one, Function.update_apply, hm, h2, h0, h1]

theorem wNeg_sameElt : SameElt wNeg witNeg :=
  ⟨by rw [wNeg_kstar]; rfl, by rw [wNeg_eps]; rfl, by rw [wNeg_delta]; rfl,
   by rw [wNeg_d]; rfl⟩

/-- **`witNeg` is a word of length `16`.** -/
theorem reaches_witNeg : Reaches 16 witNeg := Reaches.congr reaches_wNeg wNeg_sameElt

theorem witNeg_c : c witNeg = 1 := by
  unfold c
  rw [witNeg_cutSites]
  rfl

end Elt
end EltBridge


namespace EltBridge
namespace Elt

theorem witNeg_mu_neg1 : witNeg.toPathData.mu (-1) = 1 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, witNeg, SiteCost.travel]

theorem witNeg_mu0 : witNeg.toPathData.mu 0 = 2 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, witNeg, SiteCost.travel]

theorem witNeg_mu1 : witNeg.toPathData.mu 1 = 2 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, witNeg, SiteCost.travel]

theorem witNeg_mu2 : witNeg.toPathData.mu 2 = 2 := by
  unfold SiteCost.PathData.mu
  norm_num [Elt.toPathData, witNeg, SiteCost.travel]

theorem witNeg_site_neg1 : witNeg.toPathData.siteCost (-1) = 1 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witNeg]

theorem witNeg_site0 : witNeg.toPathData.siteCost 0 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witNeg]

theorem witNeg_site1 : witNeg.toPathData.siteCost 1 = 0 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witNeg]

theorem witNeg_site2 : witNeg.toPathData.siteCost 2 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witNeg]

theorem witNeg_site3 : witNeg.toPathData.siteCost 3 = 2 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  norm_num [Elt.toPathData, witNeg]

/-- **`lR witNeg = 14`.**  Four span edges (`1, 2, 2, 2`: edges `0` and `1` are gap
edges) and site costs `1, 2, 0, 2, 2`. -/
theorem witNeg_lR : witNeg.lR = 14 := by
  have hIcc1 : Finset.Icc (-1 : ℤ) 2 = ({-1, 0, 1, 2} : Finset ℤ) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  have hIcc2 : Finset.Icc (-1 : ℤ) (2 + 1) = ({-1, 0, 1, 2, 3} : Finset ℤ) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  unfold Elt.lR SiteCost.PathData.lR
  rw [toPathData_A, toPathData_B, witNeg_A, witNeg_B, hIcc1, hIcc2]
  norm_num [witNeg_mu_neg1, witNeg_mu0, witNeg_mu1, witNeg_mu2,
    witNeg_site_neg1, witNeg_site0, witNeg_site1, witNeg_site2, witNeg_site3]

/-- **The target inequality at `witNeg`, tight**: `16 <= 14 + 2 * 1`.  This is the one
witness with a non-zero defect, so it is the check that the `2 * c` term is doing work
rather than being carried along. -/
theorem wordLength_witNeg_le : wordLength witNeg ≤ witNeg.lR + 2 * c witNeg := by
  have h := wordLength_le reaches_witNeg
  rw [witNeg_lR, witNeg_c]
  omega

end Elt
end EltBridge


namespace EltBridge
namespace Elt

/-! ## 6. An INFINITE class on which the target inequality holds

`trav n` is the pure-travel element: cursor at `n + 1`, `eps = -1`, `delta = false`, and
deposits exactly the travel indicator (`1` on each edge `0 .. n`, `0` elsewhere).  It is
GAP-FREE -- every span edge carries travel -- which is the class the census singles out
(see the file header).  Here `wordLength (trav n) <= 2 * n + 2 = lR (trav n)` and
`c (trav n) = 0`, so the inequality holds, with equality.

The word is `s2 s3 (s1 s3)^n`: `s2` sets the sign, and each `s1 s3` walks the cursor one
edge to the right, depositing as it crosses. -/

/-- The pure-travel family, as words. -/
noncomputable def trav : ℕ → Elt
  | 0 => s3 (s2 one)
  | (n + 1) => s3 (s1 (trav n))

theorem reaches_trav : ∀ n : ℕ, Reaches (2 * n + 2) (trav n)
  | 0 => Reaches.one.s2.s3
  | (n + 1) => by
      have h := (reaches_trav n).s1.s3
      have he : 2 * n + 2 + 1 + 1 = 2 * (n + 1) + 2 := by omega
      rw [he] at h
      exact h

theorem trav_spec (n : ℕ) :
    (trav n).kstar = (n : ℤ) + 1 ∧ (trav n).eps = -1 ∧ (trav n).delta = false ∧
      (trav n).d = fun j => if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        [skip; skip; skip; funext j] <;>
        norm_num [trav, s3, s2, one, Function.update_apply] <;> omega
  | succ n ih =>
      obtain ⟨hk, he, hdel, hd⟩ := ih
      have h1 : (s1 (trav n)).delta = true := by
        show (!(trav n).delta) = true
        rw [hdel]; rfl
      have hkk : (s1 (trav n)).kstar = (n : ℤ) + 1 := hk
      have hee : (s1 (trav n)).eps = -1 := he
      have hdd : (s1 (trav n)).d = fun j => if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := hd
      have hval : (s1 (trav n)).d ((s1 (trav n)).kstar) = 0 := by
        rw [hdd, hkk]; norm_num
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (s3 (s1 (trav n))).kstar = _
        rw [s3, dif_pos h1]
        show (s1 (trav n)).kstar + 1 = ((n : ℤ) + 1) + 1
        rw [hkk]
      · show (s3 (s1 (trav n))).eps = _
        rw [s3, dif_pos h1]
        exact hee
      · show (s3 (s1 (trav n))).delta = false
        rw [s3, dif_pos h1]
      · show (s3 (s1 (trav n))).d = _
        rw [s3, dif_pos h1]
        show Function.update (s1 (trav n)).d ((s1 (trav n)).kstar)
          ((s1 (trav n)).d ((s1 (trav n)).kstar) - (s1 (trav n)).eps) = _
        rw [hval, hee, hkk, hdd]
        funext j
        rw [Function.update_apply]
        push_cast
        by_cases hj : j = (n : ℤ) + 1 <;> simp [hj] <;> omega

theorem trav_kstar (n : ℕ) : (trav n).kstar = (n : ℤ) + 1 := (trav_spec n).1
theorem trav_eps (n : ℕ) : (trav n).eps = -1 := (trav_spec n).2.1
theorem trav_delta (n : ℕ) : (trav n).delta = false := (trav_spec n).2.2.1
theorem trav_d (n : ℕ) :
    (trav n).d = fun j => if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := (trav_spec n).2.2.2

/-- The travel indicator of `trav n` is its deposit function. -/
theorem trav_travel (n : ℕ) (j : ℤ) :
    SiteCost.travel (trav n).kstar j = if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
  rw [trav_kstar]
  unfold SiteCost.travel
  split_ifs <;> omega

end Elt
end EltBridge


namespace EltBridge
namespace Elt

theorem trav_occ (n : ℕ) : (trav n).occ = Finset.Icc (0 : ℤ) (n : ℤ) := by
  classical
  ext x
  simp only [occ, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact ⟨le_refl 0, Int.natCast_nonneg n⟩
    · rw [trav_d, trav_travel] at h
      by_contra hc
      have hx : ¬ (0 ≤ x ∧ x < (n : ℤ) + 1) := by omega
      simp only [if_neg hx, ne_eq, not_true_eq_false, or_self] at h
  · intro hx
    right
    have hne : (trav n).d x ≠ 0 := by
      rw [trav_d]
      simp only []
      rw [if_pos (by omega : 0 ≤ x ∧ x < (n : ℤ) + 1)]
      norm_num
    refine ⟨?_, Or.inl hne⟩
    by_contra hns
    exact hne ((trav n).hsupp x hns).1

theorem trav_A (n : ℕ) : (trav n).A = 0 := by
  have hm : (trav n).A ∈ (trav n).occ := Finset.min'_mem _ _
  have hle : (trav n).A ≤ 0 := (trav n).A_le_zero
  rw [trav_occ, Finset.mem_Icc] at hm
  omega

theorem trav_B (n : ℕ) : (trav n).B = (n : ℤ) := by
  have hm : (trav n).B ∈ (trav n).occ := Finset.max'_mem _ _
  have hle : (n : ℤ) ≤ (trav n).B := by
    refine Finset.le_max' _ _ ?_
    rw [trav_occ, Finset.mem_Icc]
    exact ⟨Int.natCast_nonneg n, le_refl _⟩
  rw [trav_occ, Finset.mem_Icc] at hm
  omega

theorem trav_mu (n : ℕ) (j : ℤ) (h0 : 0 ≤ j) (h1 : j ≤ (n : ℤ)) :
    (trav n).toPathData.mu j = 1 := by
  have hd' : (trav n).toPathData.d j = if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
    rw [toPathData_d, trav_d]
  have ht : SiteCost.travel (trav n).toPathData.kstar j
      = if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
    rw [toPathData_kstar]; exact trav_travel n j
  unfold SiteCost.PathData.mu
  rw [hd', ht, if_pos (by omega : 0 ≤ j ∧ j < (n : ℤ) + 1)]
  norm_num

theorem trav_site (n : ℕ) (s : ℤ) (h0 : 0 ≤ s) (h1 : s ≤ (n : ℤ)) :
    (trav n).toPathData.siteCost s = 1 := by
  have hk' : (trav n).toPathData.kstar = (n : ℤ) + 1 := trav_kstar n
  have hd' : ∀ j : ℤ, (trav n).toPathData.d j = if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
    intro j; rw [toPathData_d, trav_d]
  have he' : (trav n).toPathData.eps = -1 := trav_eps n
  have hdel' : (trav n).toPathData.delta = false := trav_delta n
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  rw [hd' (s - 1), hd' s, he']
  simp only [hdel', Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem trav_site_top (n : ℕ) : (trav n).toPathData.siteCost ((n : ℤ) + 1) = 0 := by
  have hk' : (trav n).toPathData.kstar = (n : ℤ) + 1 := trav_kstar n
  have hd' : ∀ j : ℤ, (trav n).toPathData.d j = if 0 ≤ j ∧ j < (n : ℤ) + 1 then 1 else 0 := by
    intro j; rw [toPathData_d, trav_d]
  have he' : (trav n).toPathData.eps = -1 := trav_eps n
  have hdel' : (trav n).toPathData.delta = false := trav_delta n
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  rw [hd' ((n : ℤ) + 1 - 1), hd' ((n : ℤ) + 1), he']
  simp only [hdel', Bool.false_eq_true, if_false]
  split_ifs <;> omega

end Elt
end EltBridge

namespace EltBridge
namespace Elt

/-- **`lR (trav n) = 2 * n + 2`.**  Each of the `n + 1` span edges has `mu = 1`, and
each of the sites `0 .. n` costs `1` while the top site `n + 1` costs `0`. -/
theorem trav_lR (n : ℕ) : (trav n).lR = 2 * n + 2 := by
  have hsum1 : ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), (trav n).toPathData.mu j = n + 1 := by
    rw [Finset.sum_congr rfl
      (fun j hj => trav_mu n j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Int.card_Icc]
    omega
  have hmem : ((n : ℤ) + 1) ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1) := by
    rw [Finset.mem_Icc]; omega
  have herase :
      (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).erase ((n : ℤ) + 1) = Finset.Icc (0 : ℤ) (n : ℤ) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hsum2 :
      ∑ s ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), (trav n).toPathData.siteCost s = n + 1 := by
    rw [← Finset.sum_erase_add _ _ hmem, herase, trav_site_top,
      Finset.sum_congr rfl
        (fun s hs => trav_site n s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Int.card_Icc]
    omega
  unfold Elt.lR SiteCost.PathData.lR
  rw [toPathData_A, toPathData_B, trav_A, trav_B, hsum1, hsum2]
  omega

theorem trav_width (n : ℕ) : pdWidth (trav n).toPathData = n + 1 := by
  unfold pdWidth
  rw [toPathData_A, toPathData_B, trav_A, trav_B]
  omega

/-- **`trav n` has no cut site.**  Every interior site of its span costs `1`, and a cut
site costs `0`. -/
theorem trav_cutSites (n : ℕ) : pdCutSites (trav n).toPathData = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_pdCutSites, trav_width] at hs
  obtain ⟨⟨h1, h2⟩, hcut⟩ := hs
  unfold pdCutAt at hcut
  rw [toPathData_A, trav_A, zero_add] at hcut
  obtain ⟨ha, hb, -⟩ := hcut
  have hsc : (trav n).toPathData.siteCost s = 0 := by
    unfold SiteCost.PathData.siteCost
    rw [ha, hb]
    rfl
  have h1' := trav_site n s (by omega) (by omega)
  omega

theorem trav_c (n : ℕ) : c (trav n) = 0 := by
  unfold c
  rw [trav_cutSites]
  rfl

/-- **The target inequality on the pure-travel family**, for every `n`, with equality.
This is an INFINITE, gap-free, explicitly described class -- the class on which the
census finds the identity exact. -/
theorem wordLength_trav_le (n : ℕ) :
    wordLength (trav n) ≤ (trav n).lR + 2 * c (trav n) := by
  have h := wordLength_le (reaches_trav n)
  rw [trav_lR, trav_c]
  omega

end Elt
end EltBridge

/-! ## Axiom certification: every declaration above. -/

#print axioms EltBridge.Elt.Reaches.s1
#print axioms EltBridge.Elt.Reaches.s2
#print axioms EltBridge.Elt.Reaches.s3
#print axioms EltBridge.Elt.Reaches.feps
#print axioms EltBridge.Elt.Reaches.roundTrip
#print axioms EltBridge.Elt.Reaches.one
#print axioms EltBridge.Elt.reaches_two_of_trivial
#print axioms EltBridge.Elt.wordLength_le_two_of_trivial
#print axioms EltBridge.Elt.trivial_occ
#print axioms EltBridge.Elt.trivial_A
#print axioms EltBridge.Elt.trivial_B
#print axioms EltBridge.Elt.two_le_lR_of_trivial
#print axioms EltBridge.Elt.wordLength_le_lR_add_two_c_of_trivial
#print axioms EltBridge.Elt.gBad
#print axioms EltBridge.Elt.wBad
#print axioms EltBridge.Elt.reaches_wBad
#print axioms EltBridge.Elt.wBad_kstar
#print axioms EltBridge.Elt.wBad_eps
#print axioms EltBridge.Elt.wBad_delta
#print axioms EltBridge.Elt.wBad_d
#print axioms EltBridge.Elt.wBad_sameElt
#print axioms EltBridge.Elt.reaches_gBad
#print axioms EltBridge.Elt.wordLength_gBad_le
#print axioms EltBridge.Elt.gBad_occ
#print axioms EltBridge.Elt.gBad_A
#print axioms EltBridge.Elt.gBad_B
#print axioms EltBridge.Elt.gBad_width
#print axioms EltBridge.Elt.gBad_cutSites
#print axioms EltBridge.Elt.gBad_c
#print axioms EltBridge.Elt.gBad_mu0
#print axioms EltBridge.Elt.gBad_mu1
#print axioms EltBridge.Elt.gBad_site0
#print axioms EltBridge.Elt.gBad_site1
#print axioms EltBridge.Elt.gBad_site2
#print axioms EltBridge.Elt.gBad_lR
#print axioms EltBridge.Elt.UpperBound
#print axioms EltBridge.Elt.upperBound_forces_gBad_le_eight
#print axioms EltBridge.Elt.one_A
#print axioms EltBridge.Elt.one_B
#print axioms EltBridge.Elt.one_width
#print axioms EltBridge.Elt.one_cutSites
#print axioms EltBridge.Elt.one_c
#print axioms EltBridge.Elt.not_isTrueLength_wordLength_c
#print axioms EltBridge.Elt.wWit
#print axioms EltBridge.Elt.reaches_wWit
#print axioms EltBridge.Elt.wWit_kstar
#print axioms EltBridge.Elt.wWit_eps
#print axioms EltBridge.Elt.wWit_delta
#print axioms EltBridge.Elt.wWit_d
#print axioms EltBridge.Elt.wWit_sameElt
#print axioms EltBridge.Elt.reaches_witElt
#print axioms EltBridge.Elt.witElt_c
#print axioms EltBridge.Elt.witElt_mu0
#print axioms EltBridge.Elt.witElt_site0
#print axioms EltBridge.Elt.witElt_site1
#print axioms EltBridge.Elt.witElt_lR
#print axioms EltBridge.Elt.wordLength_witElt_le
#print axioms EltBridge.Elt.wNeg
#print axioms EltBridge.Elt.reaches_wNeg
#print axioms EltBridge.Elt.wNeg_kstar
#print axioms EltBridge.Elt.wNeg_eps
#print axioms EltBridge.Elt.wNeg_delta
#print axioms EltBridge.Elt.wNeg_d
#print axioms EltBridge.Elt.wNeg_sameElt
#print axioms EltBridge.Elt.reaches_witNeg
#print axioms EltBridge.Elt.witNeg_c
#print axioms EltBridge.Elt.witNeg_mu_neg1
#print axioms EltBridge.Elt.witNeg_mu0
#print axioms EltBridge.Elt.witNeg_mu1
#print axioms EltBridge.Elt.witNeg_mu2
#print axioms EltBridge.Elt.witNeg_site_neg1
#print axioms EltBridge.Elt.witNeg_site0
#print axioms EltBridge.Elt.witNeg_site1
#print axioms EltBridge.Elt.witNeg_site2
#print axioms EltBridge.Elt.witNeg_site3
#print axioms EltBridge.Elt.witNeg_lR
#print axioms EltBridge.Elt.wordLength_witNeg_le
#print axioms EltBridge.Elt.trav
#print axioms EltBridge.Elt.reaches_trav
#print axioms EltBridge.Elt.trav_spec
#print axioms EltBridge.Elt.trav_kstar
#print axioms EltBridge.Elt.trav_eps
#print axioms EltBridge.Elt.trav_delta
#print axioms EltBridge.Elt.trav_d
#print axioms EltBridge.Elt.trav_travel
#print axioms EltBridge.Elt.trav_occ
#print axioms EltBridge.Elt.trav_A
#print axioms EltBridge.Elt.trav_B
#print axioms EltBridge.Elt.trav_mu
#print axioms EltBridge.Elt.trav_site
#print axioms EltBridge.Elt.trav_site_top
#print axioms EltBridge.Elt.trav_lR
#print axioms EltBridge.Elt.trav_width
#print axioms EltBridge.Elt.trav_cutSites
#print axioms EltBridge.Elt.trav_c
#print axioms EltBridge.Elt.wordLength_trav_le
