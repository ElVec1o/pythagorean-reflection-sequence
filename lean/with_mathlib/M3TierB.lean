/-
M3TierB.lean
============
Formalization-debt paydown (2026-09-28): Tier-B items from paper2.tex Appendix M3'.

Formalizes the combinatorial/structural part of M3:lem:classes and M3:lem:local
that is accessible without formal power series:

  * M3:lem:classes (PARTIAL):
    - `occTrue`, `ATrue`, `BTrue`, `lRTrue`, `cTrue` are constant on SameElt-classes.
    - The injective map from SameElt-classes to G = (k,ε,δ,d) is immediate from the
      definition of SameElt.  Surjectivity (constructing an Elt from a valid tuple)
      is deferred — it requires defining the abstract type G and an explicit constructor.

  * M3:lem:local (PARTIAL):
    - At a non-junction site (s ≠ 0 and s ≠ kstar): alphaAt s = d(s-1), betaAt s = d(s),
      siteCost s = max|d(s-1)| |d(s)|.
    - PhiAt s = f(s-1) at non-junction sites.
    - Travel-interior sites (where f(s-1) ≠ 0) are never cuts.

No `sorry`.
-/
import CorrectedSpan
import Realisation

open EltBridge SiteCost CorrectedSpan
open EltBridge.Elt  -- brings SameElt, one, s1, s2, s3 into scope

namespace M3TierB

-- ─────────────────────────────────────────────────────────────────────────────
-- M3:lem:classes: occTrue/lRTrue/cTrue constant on SameElt-classes
-- ─────────────────────────────────────────────────────────────────────────────

/-- `occTrue g` depends only on `g.kstar` and `g.d`, not on `g.supp`.
The key: `hsupp` guarantees `d j = 0 ∧ travel kstar j = 0` for `j ∉ supp`, so
every j with a nonzero contribution is already in `supp`. -/
theorem occTrue_iff (g : EltBridge.Elt) (j : ℤ) :
    j ∈ occTrue g ↔ g.d j ≠ 0 ∨ travel g.kstar j ≠ 0 := by
  simp only [occTrue, Finset.mem_filter]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro hP
    refine ⟨?_, hP⟩
    by_contra hj
    rcases hP with h | h
    · exact absurd (g.hsupp j hj).1 h
    · exact absurd (g.hsupp j hj).2 h

/-- `occTrue` is determined by `(kstar, d)`, independent of `supp`. -/
theorem congr_occTrue {g h : EltBridge.Elt} (H : SameElt g h) :
    occTrue g = occTrue h := by
  ext j
  rw [occTrue_iff g j, occTrue_iff h j, H.2.2.2, H.1]

/-- `ATrue` is constant on SameElt-classes. -/
theorem congr_ATrue {g h : EltBridge.Elt} (H : SameElt g h) :
    ATrue g = ATrue h := by
  simp only [ATrue, congr_occTrue H]

/-- `BTrue` is constant on SameElt-classes. -/
theorem congr_BTrue {g h : EltBridge.Elt} (H : SameElt g h) :
    BTrue g = BTrue h := by
  simp only [BTrue, congr_occTrue H]

/-- `mu` depends only on `(kstar, d)`, not on `supp`. -/
theorem congr_mu {g h : EltBridge.Elt} (H : SameElt g h) (j : ℤ) :
    g.toPathData.mu j = h.toPathData.mu j := by
  simp only [PathData.mu, EltBridge.Elt.toPathData, H.1, H.2.2.2]

/-- `alphaAt` depends only on `(kstar, eps, delta, d)`. -/
theorem congr_alphaAt {g h : EltBridge.Elt} (H : SameElt g h) (s : ℤ) :
    g.toPathData.alphaAt s = h.toPathData.alphaAt s := by
  simp [PathData.alphaAt, PathData.vL, PathData.vD, EltBridge.Elt.toPathData,
        H.1, H.2.2.1, H.2.1, H.2.2.2]

/-- `betaAt` depends only on `(kstar, eps, delta, d)`. -/
theorem congr_betaAt {g h : EltBridge.Elt} (H : SameElt g h) (s : ℤ) :
    g.toPathData.betaAt s = h.toPathData.betaAt s := by
  simp [PathData.betaAt, PathData.vR, PathData.vD, EltBridge.Elt.toPathData,
        H.1, H.2.2.1, H.2.1, H.2.2.2]

/-- `siteCost` depends only on `(kstar, eps, delta, d)`. -/
theorem congr_siteCost {g h : EltBridge.Elt} (H : SameElt g h) (s : ℤ) :
    g.toPathData.siteCost s = h.toPathData.siteCost s := by
  simp only [PathData.siteCost, congr_alphaAt H s, congr_betaAt H s]

/-- `lRTrue` is constant on SameElt-classes.
This is the "constant on classes" half of `M3:lem:classes`. -/
theorem congr_lRTrue {g h : EltBridge.Elt} (H : SameElt g h) :
    lRTrue g = lRTrue h := by
  unfold lRTrue
  rw [congr_ATrue H, congr_BTrue H]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    [exact congr_mu H j; exact congr_siteCost H j]

/-- `PhiAt` depends only on `(kstar, delta, d)`. -/
theorem congr_PhiAt {g h : EltBridge.Elt} (H : SameElt g h) (s : ℤ) :
    g.toPathData.PhiAt s = h.toPathData.PhiAt s := by
  simp [PathData.PhiAt, PathData.f, PathData.vL, PathData.vD, EltBridge.Elt.toPathData,
        H.1, H.2.2.1]

/-- `cut` depends only on `(kstar, eps, delta, d)`. -/
theorem congr_cut {g h : EltBridge.Elt} (H : SameElt g h) (s : ℤ) :
    g.toPathData.cut s ↔ h.toPathData.cut s := by
  simp only [PathData.cut, congr_alphaAt H s, congr_betaAt H s, congr_PhiAt H s]

/-- `ShieldFires` depends only on `(kstar, delta, d)`. -/
theorem congr_shieldFires {g h : EltBridge.Elt} (H : SameElt g h) :
    ShieldFires g ↔ ShieldFires h := by
  simp only [ShieldFires, H.1, H.2.2.1, H.2.2.2]

/-- `cTrue` is constant on SameElt-classes.
This is the second half of `M3:lem:classes`. -/
theorem congr_cTrue {g h : EltBridge.Elt} (H : SameElt g h) :
    cTrue g = cTrue h := by
  simp only [cTrue, congr_ATrue H, congr_BTrue H]
  congr 1
  · congr 1
    apply Finset.filter_congr
    intro s _
    exact congr_cut H s
  · congr 1
    exact propext (and_congr (congr_shieldFires H) (congr_cut H 0))

-- ─────────────────────────────────────────────────────────────────────────────
-- M3:lem:local: local data at non-junction sites
-- ─────────────────────────────────────────────────────────────────────────────

variable {P : PathData}

/-- At any site s ≠ 0: the virtual arrival contribution vArr s = 0. -/
theorem vArr_of_ne_zero {s : ℤ} (hs : s ≠ 0) : vArr s = 0 := by
  simp [vArr, hs]

/-- At any site s ≠ kstar: vD s = 0. -/
theorem vD_of_ne_kstar {s : ℤ} (hs : s ≠ P.kstar) : P.vD s = 0 := by
  simp [PathData.vD, hs]

theorem vL_of_ne_kstar {s : ℤ} (hs : s ≠ P.kstar) : P.vL s = 0 := by
  simp [PathData.vL, PathData.vD, hs]

theorem vR_of_ne_kstar {s : ℤ} (hs : s ≠ P.kstar) : P.vR s = 0 := by
  simp [PathData.vR, PathData.vD, hs]

/-- `M3:lem:local`: at a non-junction site (s ≠ 0 and s ≠ kstar):
    alphaAt s = d(s-1). -/
theorem local_alphaAt {s : ℤ} (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.alphaAt s = P.d (s - 1) := by
  simp [PathData.alphaAt, vArr_of_ne_zero h0, vL_of_ne_kstar hk]

/-- `M3:lem:local`: at a non-junction site s ≠ kstar: betaAt s = d(s). -/
theorem local_betaAt {s : ℤ} (hk : s ≠ P.kstar) :
    P.betaAt s = P.d s := by
  simp [PathData.betaAt, vR_of_ne_kstar hk]

/-- `M3:lem:local`: at a non-junction site, siteCost = max |d(s-1)| |d(s)|. -/
theorem local_siteCost {s : ℤ} (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.siteCost s = max (P.d (s - 1)).natAbs (P.d s).natAbs := by
  simp [PathData.siteCost, local_alphaAt h0 hk, local_betaAt hk]

/-- At a non-junction site, PhiAt s = f(s-1). -/
theorem local_PhiAt {s : ℤ} (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.PhiAt s = P.f (s - 1) := by
  simp [PathData.PhiAt, vArr_of_ne_zero h0, vL_of_ne_kstar hk]

/-- `M3:lem:local`: at a non-junction site, the cut condition simplifies to
    d(s-1) = 0 ∧ d(s) = 0 ∧ f(s-1) = 0. -/
theorem local_cut {s : ℤ} (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.cut s ↔ P.d (s - 1) = 0 ∧ P.d s = 0 ∧ P.f (s - 1) = 0 := by
  simp [PathData.cut, local_alphaAt h0 hk, local_betaAt hk, local_PhiAt h0 hk]

/-- `M3:lem:local(a)`: any site s ≠ 0 and s ≠ kstar with f(s-1) ≠ 0 is never cut. -/
theorem not_cut_of_f_ne_zero {s : ℤ} (h0 : s ≠ 0) (hk : s ≠ P.kstar)
    (hf : P.f (s - 1) ≠ 0) : ¬ P.cut s := by
  rw [local_cut h0 hk]
  push Not
  exact fun _ _ => hf

end M3TierB
