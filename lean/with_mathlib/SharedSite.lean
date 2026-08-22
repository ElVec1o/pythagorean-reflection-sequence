/-
The combinatorial bridge in `thm:nogap`: a shared site always exists.

The merge argument needs a site at which two distinct components both have ends.
That is supplied by the supports being intervals covering the span:

* if some component starts strictly inside the span, the edge immediately to its
  left is covered by a different component, and their common site is where the
  first one starts;
* otherwise every component starts at the left end of the span, so with at least
  two components that end is itself shared.

`lo i` and `hi i` are the endpoints of component `i`'s support, `[L, H)` the span.
Nothing here is about strands: it is the interval bookkeeping only, with the
covering hypothesis coming from `m_j ≥ 1` on a gap-free span.
-/
import Mathlib.Tactic

namespace SharedSite

variable {ι : Type*}

/-- If some component starts strictly inside the span, then the leftmost such one
has a different component covering the edge immediately to its left.  Their common
site is `lo i`, where component `i` has ends only from the edge to its right. -/
theorem shared_of_interior_start [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℤ) (L H : ℤ)
    (hcov : ∀ j : ℤ, L ≤ j → j < H → ∃ k : ι, lo k ≤ j ∧ j < hi k)
    (hspan : ∀ k : ι, hi k ≤ H)
    (hnedeg : ∀ k : ι, lo k < hi k)
    (i₀ : ι) (hi₀ : L < lo i₀) :
    ∃ i j : ι, i ≠ j ∧ L < lo i ∧ lo j ≤ lo i - 1 ∧ lo i - 1 < hi j := by
  classical
  -- the set of components starting strictly inside the span is nonempty
  set S : Finset ι := Finset.univ.filter (fun k => L < lo k) with hS
  have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  obtain ⟨i, hiS, hmin⟩ := S.exists_min_image lo hSne
  have hLi : L < lo i := by simpa [hS] using hiS
  -- the edge immediately left of `lo i` lies in the span
  have h1 : L ≤ lo i - 1 := by omega
  have h2 : lo i - 1 < H := by
    have hne := hnedeg i
    have := hspan i
    omega
  obtain ⟨j, hj1, hj2⟩ := hcov (lo i - 1) h1 h2
  refine ⟨i, j, ?_, hLi, hj1, hj2⟩
  -- `j` starts weakly left of `lo i - 1`, so it is not `i`
  intro hij
  subst hij
  omega

/-- Otherwise every component starts at the left end, so with two of them that end
is shared. -/
theorem shared_of_all_start_left
    (lo : ι → ℤ) (L : ℤ)
    (hall : ∀ k : ι, ¬ L < lo k) (hL : ∀ k : ι, L ≤ lo k)
    (i j : ι) :
    lo i = L ∧ lo j = L := by
  constructor
  · have := hall i; have := hL i; omega
  · have := hall j; have := hL j; omega

/-- The dichotomy actually used: with at least two components, either two of them
start at the left end of the span, or some component starts strictly inside and
shares its starting site with another. -/
theorem shared_site_exists [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℤ) (L H : ℤ)
    (hcov : ∀ j : ℤ, L ≤ j → j < H → ∃ k : ι, lo k ≤ j ∧ j < hi k)
    (hspan : ∀ k : ι, hi k ≤ H) (hL : ∀ k : ι, L ≤ lo k)
    (a b : ι) (hab : a ≠ b) (hnedeg : ∀ k : ι, lo k < hi k) :
    (∃ i j : ι, i ≠ j ∧ lo i = L ∧ lo j = L) ∨
    (∃ i j : ι, i ≠ j ∧ L < lo i ∧ lo j ≤ lo i - 1 ∧ lo i - 1 < hi j) := by
  classical
  by_cases h : ∃ k : ι, L < lo k
  · obtain ⟨k, hk⟩ := h
    exact Or.inr (shared_of_interior_start lo hi L H hcov hspan hnedeg k hk)
  · have h' : ∀ k : ι, ¬ L < lo k := fun k hk => h ⟨k, hk⟩
    obtain ⟨ha, hb⟩ := shared_of_all_start_left lo L h' hL a b
    exact Or.inl ⟨a, b, hab, ha, hb⟩

-- Certification (Rule 5): every declaration above, axioms listed in the build log.
#print axioms SharedSite.shared_of_interior_start
#print axioms SharedSite.shared_of_all_start_left
#print axioms SharedSite.shared_site_exists

end SharedSite
