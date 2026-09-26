/-
  P1eArcDensity.lean
  ==================
  A small, honest, fully-formalized piece of the density content underlying the
  Theorem M -> P1f -> P1g -> P1h -> thm:arc -> cor:arcUV chain of
  `code/zeta_probe/rootunity_zeros/general/P1e_lemma.tex` (and the later papers built
  on it).

  WHAT THE PAPERS CLAIM (informally). Theorem M (`P1e_lemma.tex`, computer-assisted,
  reviewed CORRECT) proves: for every N >= 1 and every a with gcd(a,N) = 1 and
  a/N in [1/5, 4/5], the finite quantity Z_N(a/N) (Lemma Zk: a Gauss-type finite
  Fourier sum of an analytic function Phi_N built from the u-series) is nonzero, with
  an explicit quantitative lower bound |Z_N(a/N)| >= c_0 e^{-kappa N}. The downstream
  chain (thm:arc, cor:arcUV) reads this pointwise-at-every-rational statement as
  establishing a *dense* set of nonvanishing points (zeros of B / poles of U, V,
  depending on which paper) on the middle arc [1/5, 4/5] of the unit circle, and uses
  that density (every point of the arc is a limit of certified points) as part of the
  arc-level conclusion.

  Z_N(a/N) itself involves the analytic function Phi_N (an infinite series in general;
  see Lemma Zk of P1e_lemma.tex), so the numerical nonvanishing statement is NOT
  reducible to a finite algebraic computation decidable by `decide`/`norm_num` in
  Lean -- it genuinely needs the paper's Arb interval-arithmetic certificates (Theorem
  M's proof: base case N <= 150 by exhaustive enclosure, inductive step via the hazard
  decomposition of Lemmas H, A, B, B', O). None of that saddle-point/interval-arithmetic
  machinery is formalized here, or is realistically formalizable in one session:
  Mathlib has no ready-made saddle-point-method or certified-interval-arithmetic
  infrastructure for this kind of analytic estimate.

  WHAT IS FORMALIZED HERE, PRECISELY. The purely topological content that turns
  "nonvanishing holds at every reduced rational a/N in [1/5,4/5]" into "the arc
  [1/5,4/5] is a set of limit points of certified-nonvanishing locations": namely
  that the certified set

    `CertifiedPts := {x : R | there is q : Q with x = (q:R) and x in [1/5,4/5]}`

  (exactly the set of points at which Theorem M supplies a certified a/N, since every
  rational in lowest terms IS such an a/N with gcd(a,N)=1, via `Rat.num`/`Rat.den`) has

    `closure CertifiedPts = Set.Icc (1/5) (4/5)`.

  Equivalently (`arc_mem_closure` below): every real x in [1/5, 4/5] is, for every
  eps > 0, within eps of some certified point. This is exactly the "density on the
  arc" half of the informal claim, proved with zero `sorry`, using nothing beyond
  order-density of Q in R (`exists_rat_btwn`) and elementary real-number inequalities.
  It does NOT prove Theorem M itself (that Z_N is actually nonzero at those points);
  it proves the honest, separate topological fact that the papers' density language
  about the arc is asking for, GIVEN Theorem M's pointwise conclusion as an
  assumption-free set membership (every rational point of the arc is, by definition,
  a point Theorem M addresses).

  HONEST SCOPE. This is the "elementary structural lemma" (candidate 2 of the task
  brief): closure of a dense subset of an interval is the whole interval, specialized
  to the exact set the chain's density language is about. It captures a real,
  nontrivial-to-state (if topologically standard) ingredient of thm:arc's chain, not
  the deep analytic content (Theorem M's actual nonvanishing bound) which is out of
  reach of a one-session Lean formalization.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.Rat.Cast.Order

namespace P1eArcDensity

open Set

/-- The middle-arc parameter interval `[1/5, 4/5]` of Theorem M (`P1e_lemma.tex`,
`thm:M`), viewed inside `R`. -/
noncomputable def arc : Set ℝ := Set.Icc (1 / 5 : ℝ) (4 / 5 : ℝ)

/-- The set of points Theorem M supplies a certificate at: every point of the arc
that is a rational number `q`. Since `q = q.num / q.den` in lowest terms with
`gcd(q.num.natAbs, q.den) = 1` (Mathlib's `Rat.reduced`), each such point is exactly
an `a/N` with `gcd(a,N)=1` in the sense of Theorem M; we work with `Q` directly
rather than re-deriving the `num/den` reduction, since that reduction is a Mathlib
built-in (`Rat.reduced`) and not part of the paper's mathematical content. -/
noncomputable def CertifiedPts : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' {q : ℚ | (q : ℝ) ∈ arc}

lemma certifiedPts_subset_arc : CertifiedPts ⊆ arc := by
  rintro _ ⟨q, hq, rfl⟩
  exact hq

/-- Every point of the arc is a limit point of certified points: for every
`x` in `[1/5,4/5]` and every `eps > 0` there is a certified point within `eps` of
`x`. This is the precise "density on the arc" content used by the thm:arc /
cor:arcUV chain. -/
theorem arc_mem_closure (x : ℝ) (hx : x ∈ arc) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ CertifiedPts, dist x y < ε := by
  obtain ⟨hx1, hx2⟩ := hx
  -- Squeeze a rational strictly between max(1/5, x-ε) and min(4/5, x+ε);
  -- such a rational is automatically in the arc and within ε of x.
  have hlo_lt_hi : max (1 / 5 : ℝ) (x - ε) < min (4 / 5 : ℝ) (x + ε) := by
    have h1 : (1 / 5 : ℝ) < min (4 / 5 : ℝ) (x + ε) := lt_min (by norm_num) (by linarith)
    have h2 : x - ε < min (4 / 5 : ℝ) (x + ε) := lt_min (by linarith) (by linarith)
    exact max_lt h1 h2
  obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn hlo_lt_hi
  have hq1 : (1 / 5 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq_lo)
  have hq2 : (q : ℝ) ≤ (4 / 5 : ℝ) := le_of_lt (lt_of_lt_of_le hq_hi (min_le_left _ _))
  have hq3 : x - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq_lo
  have hq4 : (q : ℝ) < x + ε := lt_of_lt_of_le hq_hi (min_le_right _ _)
  refine ⟨(q : ℝ), ⟨q, ⟨hq1, hq2⟩, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Main theorem: the closure of the certified-nonvanishing points is exactly the
whole arc `[1/5, 4/5]`. Combined with Theorem M (`Z_N(a/N) != 0` at every certified
point, proved analytically/computer-assisted in `P1e_lemma.tex` and NOT reproved
here), this is the formal content of "the arc is a set of limit points of zeros of
`B` / poles of `U, V`" used downstream (`thm:arc`, `cor:arcUV`). -/
theorem closure_certifiedPts_eq_arc : closure CertifiedPts = arc := by
  apply subset_antisymm
  · exact closure_minimal certifiedPts_subset_arc isClosed_Icc
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact arc_mem_closure x hx ε hε

end P1eArcDensity
