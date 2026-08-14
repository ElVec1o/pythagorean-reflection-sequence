/-
  OrthoschemeNormals.lean
  =======================
  Paper 3, Lemma `lem:normals`: the facet normals of an n-orthoscheme and their orthogonality
  pattern.

  The paper previously asserted the pattern with the words "verified symbolically for n <= 5".
  It is now proved for every n, and the proof is here.  With vertices V_0 = 0 and
  V_k = V_{k-1} + l_k e_k, the facet opposite V_j has normal

      m_0 = e_1,      m_j = l_{j+1} e_j - l_j e_{j+1}  (1 <= j <= n-1),      m_n = e_n,

  so the supports are {1}, {j, j+1} and {n}.  Two normals are orthogonal exactly when their
  supports are disjoint, and that happens exactly when the indices differ by at least 2.
  The right-angled Coxeter relations of the envelope are precisely those orthogonalities, so
  this lemma is what makes the envelope leg-independent.

  What is formalised: the support bookkeeping (which is the whole combinatorial content), the
  vanishing of the pointwise product on disjoint supports, and the three adjacent inner
  products, which are nonzero for positive legs.  The ambient Euclidean geometry is not
  formalised; the normals enter as the displayed vectors.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OrthoschemeNormals

/-- Everything below is over the reals, where the normals live. -/
abbrev K := ℝ

/-! ### 1. Supports -/

/-- The support of the normal to the facet opposite `V_j`, in an `n`-orthoscheme.
    Coordinates are numbered `1, ..., n`. -/
def supp (n j : ℕ) : Finset ℕ :=
  if j = 0 then {1} else if j = n then {n} else {j, j + 1}

/-- **The support pattern.**  For `0 <= i < j <= n` with `j - i >= 2`, the two supports are
    disjoint.  This is the statement that non-consecutive facets are orthogonal. -/
theorem supp_disjoint {n i j : ℕ} (hn : 2 ≤ n) (hij : i + 2 ≤ j) (hjn : j ≤ n) :
    Disjoint (supp n i) (supp n j) := by
  simp only [supp]
  -- every element of `supp n i` is at most `i + 1`, every element of `supp n j` is at least `j`
  rw [Finset.disjoint_left]
  intro a ha hb
  split_ifs at ha hb with h1 h2 h3 h4 h5 h6 <;>
    simp_all [Finset.mem_insert, Finset.mem_singleton] <;> omega

/-! ### 2. Disjoint supports kill the inner product -/

/-- A vector, as a coordinate function, vanishing off a finite set. -/
def SupportedOn (v : ℕ → K) (S : Finset ℕ) : Prop := ∀ i, i ∉ S → v i = 0

/-- **Disjoint supports give a vanishing product coordinatewise**, hence a vanishing inner
    product however the sum is taken. -/
theorem mul_eq_zero_of_disjoint {v w : ℕ → K} {S T : Finset ℕ}
    (hv : SupportedOn v S) (hw : SupportedOn w T) (hST : Disjoint S T) :
    ∀ i, v i * w i = 0 := by
  intro i
  by_cases hiS : i ∈ S
  · have : i ∉ T := Finset.disjoint_left.mp hST hiS
    rw [hw i this, mul_zero]
  · rw [hv i hiS, zero_mul]

theorem sum_eq_zero_of_disjoint {v w : ℕ → K} {S T : Finset ℕ}
    (hv : SupportedOn v S) (hw : SupportedOn w T) (hST : Disjoint S T) (U : Finset ℕ) :
    ∑ i ∈ U, v i * w i = 0 :=
  Finset.sum_eq_zero fun i _ => mul_eq_zero_of_disjoint hv hw hST i

/-! ### 3. The adjacent inner products are nonzero

    Consecutive facets meet at a genuine dihedral angle for every positive leg tuple; this is
    what leaves the consecutive bonds infinite in the envelope. -/

/-- `m_0 . m_1 = l_2`, with `m_0 = e_1` and `m_1 = l_2 e_1 - l_1 e_2`. -/
theorem dot_zero_one {l1 l2 : K} (h2 : 0 < l2) :
    (1 : K) * l2 + 0 * (-l1) ≠ 0 := by
  have : (1 : K) * l2 + 0 * (-l1) = l2 := by ring
  rw [this]; exact ne_of_gt h2

/-- `m_j . m_{j+1} = - l_j l_{j+2}` for an interior pair, with
    `m_j = l_{j+1} e_j - l_j e_{j+1}` and `m_{j+1} = l_{j+2} e_{j+1} - l_{j+1} e_{j+2}`.
    Only the shared coordinate `j+1` contributes. -/
theorem dot_interior {lj ljp2 : K} (hj : 0 < lj) (hjp2 : 0 < ljp2) :
    (-lj) * ljp2 ≠ 0 := by
  have hpos : (0 : K) < lj * ljp2 := mul_pos hj hjp2
  have : (-lj) * ljp2 < 0 := by nlinarith
  exact ne_of_lt this

/-- `m_{n-1} . m_n = - l_{n-1}`, with `m_n = e_n`. -/
theorem dot_last {lnm1 : K} (h : 0 < lnm1) : (-lnm1) ≠ (0 : K) := by
  have : (-lnm1) < (0 : K) := by linarith
  exact ne_of_lt this

/-! ### 4. What the lemma delivers

    Non-consecutive facets are orthogonal for EVERY positive leg tuple, and consecutive ones
    never are.  The first gives the relations `(R_i R_j)^2 = 1` for `|i - j| >= 2`, uniformly
    in the legs; the second is why no further relation is forced. -/

theorem orthogonality_pattern {n i j : ℕ} (hn : 2 ≤ n) (hij : i + 2 ≤ j) (hjn : j ≤ n)
    {v w : ℕ → K} (hv : SupportedOn v (supp n i)) (hw : SupportedOn w (supp n j))
    (U : Finset ℕ) :
    ∑ k ∈ U, v k * w k = 0 :=
  sum_eq_zero_of_disjoint hv hw (supp_disjoint hn hij hjn) U

end OrthoschemeNormals

-- Rule 5 axiom audit.
#print axioms OrthoschemeNormals.supp_disjoint
#print axioms OrthoschemeNormals.mul_eq_zero_of_disjoint
#print axioms OrthoschemeNormals.sum_eq_zero_of_disjoint
#print axioms OrthoschemeNormals.dot_zero_one
#print axioms OrthoschemeNormals.dot_interior
#print axioms OrthoschemeNormals.dot_last
#print axioms OrthoschemeNormals.orthogonality_pattern
