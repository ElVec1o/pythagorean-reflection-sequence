/-
  Paper1TierACensus.lean
  =======================

  Tier-A formalization-debt paydown for paper1.tex (see
  `private/FORMALIZATION_TRIAGE.md` / `private/FORMALIZATION_LEDGER.md`).

  Covers two of the three targeted labels:

  * `cor:fibonacci-phase` — for the reference triangle family, the BFS
    orbit-growth layer counts satisfy `u_d = F_{d+3}` for `1 ≤ d ≤ 9`,
    and the first Fibonacci deficit appears at `d = 10`, where
    `u_10 = 225 = F_13 - 8`.

  * `prop:bonfioli-completeness` — among the 233 canonical length-10
    Coxeter words, the symbolic affine images fall into exactly 217
    singleton equivalence classes and 8 classes of size 2 (i.e. exactly
    8 collision pairs, matching Table `tab:bonfioli`), for every
    admissible (unequal-leg) right triangle.

  Both reuse the existing, already `native_decide`-verified symbolic BFS
  machinery of `ComputableUniversality.lean` (canonical word enumeration,
  the `CAff` polynomial-affine-isometry type over `ℚ[a,b]`, and the
  `CAff.hkey` common-denominator hashing key that `layerCountH`/
  `allLayerCounts` already use and cross-check against the slow
  cross-multiplication equivalence at depth 10, via
  `slow_fast_agree_at_10`). No new BFS/dedup infrastructure is built
  here — this file only adds two new *statements* (a Fibonacci
  comparison, and a class-size census) evaluated on data already
  produced by that machinery.

  `thm:universality-sharp` (the depth-32/33 sharp census) is NOT
  formalized here. Paper1.tex itself classifies it as tier (iii),
  "outside Lean by construction" (line ~4657: "Two further items are
  outside Lean by construction: Theorem~\ref{thm:universality-sharp} and
  Proposition~\ref{prop:modular-cert}"), and Remark~\ref{rem:lean-universality}
  (line ~4398) states explicitly: "The sharp threshold of depth 32
  ... is *not* a Lean theorem; it is established by the modular
  certificate of §ssec:reproduce-modular" (exact ℚ(i) arithmetic over
  independent 31-bit-prime modular filters, run outside Lean). The
  existing depth-22 `native_decide` BFS sweep
  (`ComputableUniversality.universal_layers_through_22`) already takes
  about 22 minutes per the paper's own account (line ~4386-4387); the
  canonical-word count grows like the golden-ratio powers underlying
  this Fibonacci sequence, so depth 32-33 is roughly two more Fibonacci
  "octaves" larger (order of a few million canonical words at depth 32,
  and `u_33 - u_33^{(1,2)} = ...` on the order of several million
  cumulative isometries to hash at depth 33) — well beyond what a single
  `native_decide` BFS sweep can be expected to complete inside this
  session's memory/time budget, and beyond what the paper's own trust
  ledger claims for Lean. No attempt was made to push this depth in
  this session; it is left as future dedicated slow-build work.
-/

import ComputableUniversality

namespace Paper1TierACensus

open ComputableUniversality
open SymbolicUniversality

/-! ### `cor:fibonacci-phase` -/

/-- Fibonacci numbers, `fib 0 = 0`, `fib 1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Fibonacci phase, depths 1-9.**

    The symbolic (hence shape-universal) BFS layer counts at depths
    `1,…,9`, already computed and machine-verified through depth 22 by
    `ComputableUniversality.universal_layers_through_22`, agree exactly
    with `F_{d+3}` for `1 ≤ d ≤ 9`:

      d :   1  2  3  4   5   6   7   8    9
      u_d:  3  5  8  13  21  34  55  89  144
      F_{d+3}: F4 F5 F6 F7 F8 F9 F10 F11 F12  (same values).

    This matches the first half of Corollary `cor:fibonacci-phase`. -/
theorem fibonacci_phase_1_to_9 :
    (List.range 9).map (fun i => (allLayerCounts 22).getD (i + 1) 0) =
      (List.range 9).map (fun i => fib (i + 1 + 3)) := by
  native_decide

/-- **Fibonacci deficit at depth 10.**

    At depth 10 the universal (shape-independent) layer count is
    `u_10 = 225`, strictly below `F_13 = 233`; the deficit is exactly
    `8`, matching the eight collision pairs of
    `prop:bonfioli-completeness` / `ComputableUniversality.universality_at_depth_10`.
    This matches the second half of Corollary `cor:fibonacci-phase`. -/
theorem fibonacci_phase_deficit_at_10 :
    (allLayerCounts 22).getD 10 0 = 225 ∧ fib 13 = 233 ∧
      fib 13 - (allLayerCounts 22).getD 10 0 = 8 := by
  native_decide

/-! ### `prop:bonfioli-completeness` -/

/-- Equivalence-class sizes of the 233 canonical length-10 symbolic
    affine images, grouped by the same `CAff.hkey` common-denominator
    hashing key `layerCountH`/`allLayerCounts` already use (cross-checked
    against the slow cross-multiplication equivalence at depth 10 by
    `ComputableUniversality.slow_fast_agree_at_10`), sorted ascending. -/
def classSizes (d : Nat) : List Nat := Id.run do
  let mut m : Std.HashMap (List (Nat × Nat × Nat × Int × Nat)) Nat := {}
  for w in canonicalWords d do
    let k := CAff.hkey (applyWord w) d
    m := m.insert k (m.getD k 0 + 1)
  return (m.toList.map Prod.snd).mergeSort (· ≤ ·)

/-- **Completeness at depth 10 (`prop:bonfioli-completeness`).**

    Among the 233 canonical length-10 Coxeter words, the symbolic affine
    images over `ℚ[a,b]` (hence for every right triangle with unequal
    legs) fall into exactly 217 singleton classes and 8 classes of size
    2 — i.e. exactly 8 collision pairs, none of any larger size, and no
    further length-10 identity beyond the eight of Table `tab:bonfioli`. -/
theorem bonfioli_completeness_class_sizes :
    classSizes 10 = List.replicate 217 1 ++ List.replicate 8 2 := by
  native_decide

/-- Sanity check: class sizes recover the totals of `universality_at_depth_10`
    (233 words partitioned into 225 classes). -/
theorem bonfioli_completeness_totals :
    (classSizes 10).length = 225 ∧ (classSizes 10).sum = 233 := by
  native_decide

end Paper1TierACensus

-- Rule 5 axiom audit.
#print axioms Paper1TierACensus.fibonacci_phase_1_to_9
#print axioms Paper1TierACensus.fibonacci_phase_deficit_at_10
#print axioms Paper1TierACensus.bonfioli_completeness_class_sizes
#print axioms Paper1TierACensus.bonfioli_completeness_totals
