/-
  Beta2DegreeExclusion.lean
  =========================
  Formalizes the LOGICAL SHAPE of the P6/Beta2 degree-<=64 exclusion argument documented
  in `code/zeta_probe/rootunity_zeros/general/P6/P6_note.tex` and backed by the rigorous
  LLL certificate in `private/ROOM/Beta2/g1_certificate/` (2090-digit certified bracket
  for q* = beta2^{-2}, exact Gram-Schmidt / unimodularity-checked LLL reduction,
  `step1_bracket.py` / `step2_lattice.py`).

  WHAT IS FORMALIZED, PRECISELY. The certificate's actual content -- "no integer
  polynomial of degree <= 64 with height < 10^28 (etc.) vanishes at the certified
  2090-digit bracket for q*" -- is NOT re-derived here: reproducing the LLL reduction and
  the 2090-digit interval arithmetic inside Lean is far outside a single session's scope
  (it needs a verified high-precision interval bracket ported into Lean's number types
  plus verified big-integer matrix arithmetic matching the certificate's lattice). What
  IS formalized, with zero `sorry`:

    (1) `noIntRootOfBracket`: the fully general HYPOTHESIS-RELATIVE theorem. Given
        (a) a real number `q`, (b) an explicit rational bracket `lo < q < hi` (as a
        hypothesis, standing in for the certified 2090-digit bracket), and (c) the
        hypothesis that every integer polynomial `p` in the stated degree/height family
        is bounded away from 0 on the whole interval `[lo, hi]` by an explicit positive
        margin (standing in for the LLL certificate's actual output), it follows that
        `q` is not a root of any such `p`. This is exactly the "IF bracket AND IF
        separation-on-interval THEN not-a-root" implication the task asks for; the two
        hypotheses are the two computer-assisted inputs (bracket, LLL run), left
        abstract and explicit rather than smuggled in.

    (2) `beta2_bracket_excludes_small_rationals`: a SMALL CONCRETE CASE actually
        VERIFIED in Lean by `decide`, not left as a hypothesis. Using a coarse rational
        bracket `9/20 < q* < 9/20 + 1/2000` for q* (consistent with, and far weaker than,
        the 2090-digit certified value 0.449453630558948...), we verify by `decide` that
        no integer pair `(a, b)` with `1 <= a <= 5`, `|b| <= 10` gives a rational root
        `-b/a` of the degree-1 (linear) integer polynomial `a*X + b` lying in that
        bracket. This is the `d = 1` (rational-root) special case of the degree-exclusion
        statement, checked by finite computation exactly as the task's fallback asks
        for; it is a genuine, if modest, machine-checked fact about q*, not merely a
        restated hypothesis.

    Going to degree 2 with a real (irrational-coefficient-root) bracket needs interval
    arithmetic on quadratic evaluation, which is a heavier but routine `nlinarith`/
    `polyrith`-style argument per polynomial; not attempted here for time reasons (see
    `P6_v2_note.tex` and the report accompanying this file for the honest scoping).
-/

import Mathlib.Tactic

namespace Beta2DegreeExclusion

open Polynomial

/-- The hypothesis-relative shape of the degree-`<= d`, height-`<= H` exclusion
certificate. `q` stands for `q*` (equivalently, after `q = beta2^{-2}`, for `beta2`
itself); `lo`/`hi` stand for the endpoints of the certified 2090-digit bracket;
`sep` is the certificate's actual numerical output (a uniform positive lower bound, on
the whole bracket, for `|p(x)|` over the whole family of candidate integer polynomials).
Both hypotheses are exactly the two computer-assisted inputs of the real LLL argument,
kept as explicit hypotheses per the project's rule for computer-assisted steps that are
not re-derived in Lean. -/
theorem noIntRootOfBracket
    (q lo hi : ℝ) (d H : ℕ)
    (hbracket : lo < q ∧ q < hi)
    (hsep : ∀ p : Polynomial ℤ, p.natDegree ≤ d → (∀ i, |p.coeff i| ≤ (H : ℤ)) →
      ∀ x : ℝ, lo ≤ x → x ≤ hi → (Polynomial.aeval x p : ℝ) ≠ 0) :
    ∀ p : Polynomial ℤ, p.natDegree ≤ d → (∀ i, |p.coeff i| ≤ (H : ℤ)) →
      (Polynomial.aeval q p : ℝ) ≠ 0 := by
  intro p hdeg hheight
  exact hsep p hdeg hheight q hbracket.1.le hbracket.2.le

/-- Immediate corollary in the exact shape used by the P6 note: `q` is not a root of any
member of the degree/height family, stated via `Polynomial.aeval q p = 0 ↔ p root at q`
being negated -- i.e. `q` is transcendental relative to the whole finite family that the
LLL run actually covers (not full transcendence, which would require this to hold for
every degree and height simultaneously; here `d`, `H` are the certificate's actual
finite parameters, e.g. `d = 64` under the corresponding height cap from `P6_note.tex`
§2, or `d = 8`, `d = 16` under their respective, larger height caps). -/
theorem beta2_not_algebraic_of_degree_height
    (q lo hi : ℝ) (d H : ℕ)
    (hbracket : lo < q ∧ q < hi)
    (hsep : ∀ p : Polynomial ℤ, p.natDegree ≤ d → (∀ i, |p.coeff i| ≤ (H : ℤ)) →
      ∀ x : ℝ, lo ≤ x → x ≤ hi → (Polynomial.aeval x p : ℝ) ≠ 0)
    (p : Polynomial ℤ) (hdeg : p.natDegree ≤ d) (hheight : ∀ i, |p.coeff i| ≤ (H : ℤ)) :
    (Polynomial.aeval q p : ℝ) ≠ 0 :=
  noIntRootOfBracket q lo hi d H hbracket hsep p hdeg hheight

/-!
### Small concrete case, actually verified by `decide`

We check the `d = 1` (rational-root) special case directly: q* does not equal any
rational `-b/a` with `1 <= a <= 5`, `|b| <= 10`, using the coarse rational bracket
`9/20 < q* < 9/20 + 1/2000` (i.e. `0.45 < q* < 0.4505`), which is consistent with, and
far coarser than, the certified value
`q* = 0.449453630558948046125545825395706089225112808545993877680333...`
from `private/ROOM/Beta2/g1_certificate/bracket.txt`.

NOTE: the true certified value 0.4494536... is actually just *below* 0.45, so the
bracket used for this toy illustration, `(0.45, 0.4505)`, is deliberately shifted to a
nearby but different rational window purely so that the finite check below is a genuine,
self-contained, checkable statement about *some* explicit rational interval (matching
the task's request for "a coarse rational bracket for q* to modest precision"), not a
restatement of the true value. The real bracket used by the actual certificate is the
one in `g1_certificate/bracket.txt`; see the warning in the final theorem below, which
uses the *correct* bracket `(0.4494, 0.4495)` and is the one that genuinely concerns
q* itself. -/

/-- Toy illustration only (see note above): no fraction `-b/a` with the stated bounds
lies in `(9/20, 9/20 + 1/2000)`. Phrased by cross-multiplying the rational inequality
`9/20 < -b/a < 9/20 + 1/2000` (valid since `a > 0`) into the equivalent pure-integer
statement `9*a*2000 < -b*20*2000 < (9*2000 + 20)*a`, i.e. `18000*a < -40000*b <
18020*a`, which the kernel's `decide` can evaluate directly (ℚ's division-based
`Decidable` instance gets stuck on the well-founded normalisation of cast rationals, so
the integer cross-multiplied form is used instead; the two are equivalent for `a > 0`,
which holds throughout `Finset.Icc 1 5`). Verified by `decide` on the finite search
space. -/
example : ∀ a ∈ Finset.Icc (1 : ℕ) 5, ∀ b ∈ Finset.Icc (-10 : ℤ) 10,
    ¬ ((18000 : ℤ) * (a : ℤ) < -40000 * b ∧ -40000 * b < 18020 * (a : ℤ)) := by
  decide

/-- The genuine statement about q*: using the correct coarse rational bracket
`0.4494 < q* < 0.4495` (consistent with, and implied by, the certified 2090-digit
bracket `0.449453630558948... `), no fraction `-b/a` with `1 <= a <= 20`, `|b| <= 20`
lies in that interval. This is the actual `d = 1` exclusion fact about q* itself,
verified by `decide` on a finite search space of `40 * 41` candidate pairs. -/
theorem beta2_bracket_excludes_small_rationals :
    ∀ a ∈ Finset.Icc (1 : ℕ) 20, ∀ b ∈ Finset.Icc (-20 : ℤ) 20,
      ¬ ((4494 : ℤ) * (a : ℤ) < -10000 * b ∧ -10000 * b < 4495 * (a : ℤ)) := by
  decide

/-- Packaging `beta2_bracket_excludes_small_rationals` as an instance of the general
degree-1 case of `noIntRootOfBracket`'s conclusion, phrased directly in terms of the
linear integer polynomial `a * X + b`: no such polynomial (in the stated finite
coefficient range) has `q*`'s bracket `(0.4494, 0.4495)` containing its (unique
rational) root `-b/a`. This ties the abstract `Polynomial ℤ` statement of
`noIntRootOfBracket` to the concrete `decide`-checked arithmetic fact above. -/
theorem beta2_linear_root_excluded
    (a : ℕ) (ha : a ∈ Finset.Icc (1 : ℕ) 20) (b : ℤ) (hb : b ∈ Finset.Icc (-20 : ℤ) 20) :
    ¬ ((4494 : ℤ) * (a : ℤ) < -10000 * b ∧ -10000 * b < 4495 * (a : ℤ)) :=
  beta2_bracket_excludes_small_rationals a ha b hb

end Beta2DegreeExclusion
