/-
LorentzAssembly.lean
====================
Formalises `lem:lorentz` from `paper/journal/merged_novel_paper.tex` in full:

  The path tridiagonal Gram matrix G_n (size (n+1)×(n+1)) satisfies:
    (A) det G_n = 0  ↔  n ≡ 1 (mod 3).
    (B) When n ≡ 1 (mod 3), the ℚ-rank of G_n equals n.

Part (A) = PathGramSingular.pathGram_singular_iff.
Part (B) = PathGramRadline.pathGramQ_rank_eq.

Together they give: the radical (kernel) of G_n over ℚ has dimension 1 when n ≡ 1 (mod 3),
and G_n is non-degenerate otherwise — which is the content of lem:lorentz.

Axioms: propext, Classical.choice, Quot.sound.  No sorry.
-/

import PathGramSingular
import PathGramRadline

namespace LorentzAssembly

open PathGramSingular PathGramRadline

/-! ## lem:lorentz (A): singularity criterion -/

/-- lem:lorentz (A): G_n is singular if and only if n ≡ 1 (mod 3). -/
theorem lorentz_singular (n : ℕ) :
    (pathGram n).det = 0 ↔ ∃ j, n = 3 * j + 1 :=
  pathGram_singular_iff n

/-! ## lem:lorentz (B): rank when singular -/

/-- lem:lorentz (B): when n ≡ 1 (mod 3), the ℚ-rank of G_n is n.
    Equivalently, the radical of G_n over ℚ is 1-dimensional (a single null line). -/
theorem lorentz_rank (n : ℕ) (h : ∃ j, n = 3 * j + 1) :
    (pathGramQ n).rank = n :=
  pathGramQ_rank_eq n h

/-! ## lem:lorentz (combined): radical dimension -/

/-- lem:lorentz (combined): G_n is singular iff n ≡ 1 (mod 3);
    when singular, the ℚ-rank is n (radical dimension 1). -/
theorem lem_lorentz (n : ℕ) :
    ((pathGram n).det = 0 ↔ ∃ j, n = 3 * j + 1) ∧
    (∀ _ : ∃ j, n = 3 * j + 1, (pathGramQ n).rank = n) :=
  ⟨lorentz_singular n, fun h => lorentz_rank n h⟩

end LorentzAssembly

-- Rule 5 axiom audit.
#print axioms LorentzAssembly.lem_lorentz
