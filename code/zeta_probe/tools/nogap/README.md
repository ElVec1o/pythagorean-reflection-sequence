# no-gap / shield-law findings

Session 2026-08-22. Labels per Rule 0.

## Summary

| # | Statement | Label |
|---|---|---|
| M6a | no gap edge => `Z` empty | **VERIFIED** (`lean/with_mathlib/NoGapCutFree.lean`), 2 505 271 elts |
| M6  | no gap edge => `c = 0` | **HEURISTIC** (2 505 271 elts, depth 31, 0 violations) |
| M6b | `Z` empty => `c = 0` | **CONJECTURE** (3 101 847 elts, 0 violations) |
| SL  | shield law `c = \|Z\|` incl. boundary term, all `k*` | **HEURISTIC** (3 336 511 elts, 0 violations) |
| M10 | `lamp_lib.relaxed_solve` computes `l_R` | **FALSE** (counterexample below) |

## M10: relaxed_solve is wrong on gap-bearing elements

`relaxed_solve` overestimates `l_R`. Smallest witness: `eps=1, delta=0, k*=0,
lamps {1:-2}`. It returns 10; the true value is 8, realised by `m_0 = m_1 = 2`
(`sum m = 4`) with site costs `0, 2, 2` -- the sign-flip bounce at site 2 forced
because `d_1 = -2` splits as `p^u = 1, p^d = 0`. With `l_T = 10` this gives
`c = 1`, and the Metric Theorem closes; at 10 it does not.

Ground truth: `tools/sitecost` mode `shield`, direct enumeration of realizations
under two independent exact solvers, reports
`l_R = sum m + sum max(|alpha|,|beta|,|Phi|)`, 0 exceptions.

Scope: **150 wrong values out of ~9000 at depth 17, every one on a gap-bearing
element; 0 on no-gap elements.** So the published `prop:local`(i) validation
(pure-travel, a subset of no-gap) is unaffected. Any `c`-distribution or `v_n`
claim drawn from it over ALL elements is not, and should be recomputed.

## SL: the shield law needs the boundary term, and then holds at every k*

`prop:cut` counts cut sites **interior** to the span. That undercounts: when both
markers sit at a span endpoint on the side opposite the edges, cutting there
isolates the marker component and everything else is a cycle. The site must be
counted when

    k* = 0,  delta* = 0,  lo = 0 < hi.

This is exactly `rem:shieldowes`'s boundary shield -- it records the marker site
as cut iff `d_{-1} = 0, delta* = 0, eps* = 1`, where `sh_R = 1[eps*=-1 or delta*=1]`
vanishes. The new content is the `lo = 0 < hi` clause: without it the identity
element is miscounted (`c = 0`, `|Z| = 1`).

Counting it, `c = |Z|` holds with **0 exceptions on 50763 elements at all `k*`**
(depth 21), extending paper 2's verification beyond the `k*=0` bulk. Counting all
marker sites instead produces 8555 `prop:cut` violations -- an impossible result
against a PROVED theorem, which is how the condition was localised.

## M6a (PROVED): no gap edge => Z empty

Let `s` be a site counted by `Z`. With `alpha = d_{s-1}`, `beta = d_s`,
`Phi = f_{s-1}` and the `sitecost` virtual-event fold-in:

* `s` interior, `s \notin {0,k*}`: cut forces `d_{s-1} = 0` and `f_{s-1} = 0`;
  `s` interior puts edge `s-1` in the span, so it is a gap edge.
* `s = 0 \ne k*`: `Phi = f_{-1}+1 = 0` gives `f_{-1} = -1`, so `k* < 0` and
  `f_0 = 0`; `beta = d_0 = 0`. Edge 0 is in the span, so it is a gap edge.
* `s = k* \ne 0`, `delta* = 1`: `alpha = d_{s-1} = 0` and `Phi = f_{s-1} = 0`, so
  edge `s-1` is a gap edge.
* `s = k* \ne 0`, `delta* = 0`: `Phi = f_{s-1}-1 = 0` gives `f_{k*-1} = 1`, so
  `k* > 0` and `f_{k*} = 0`; `beta = d_{k*} = 0`. Edge `k*` is a gap edge.
* `s = 0 = k*` (interior or boundary-shield): `Phi = f_{-1} = 0`, `beta = d_0 = 0`,
  and `f_0 = 0`; the boundary-shield clause gives `hi > 0`, so edge 0 is in the
  span and is a gap edge.

Every case contradicts the hypothesis. Hence `Z` is empty. QED

Verified: 42361 no-gap elements to depth 21, 0 counterexamples.

## Consequence for (T)

`prop:travelinv` (=(T), one of `U`'s two hypotheses) is proved in `lifting_U.tex`
from `prop:local`(i), which has no proof. `prop:local`(i)'s hypothesis implies no
gap edges, so by M6a it implies `Z` empty. Therefore

> **(T) reduces, via the PROVED M6a, to M6b: the `Z` empty case of the reverse
> shield inequality `c <= |Z|`** (paper2 `rem:shieldowes`, unproved).

Note M6b is *stronger* than M6, not equivalent: no-gap is a strict subset of
`Z` empty (42361 vs 48715 elements at depth 21). An earlier version of this note
claimed equivalence; that was wrong.

The `Z` empty case still looks easier than the general one: `rem:shieldowes` needs
pairings connecting all crossings within each of `|Z|+1` classes, whereas at
`Z` empty there is a single class.

## Rule 1 transfer note

The remaining obligation -- choose min-cost pairings at every site so the
transition system is one open walk -- is the **compatible Eulerian circuit /
transition system** problem (Kotzig, Fleischner; Bouchet's isotropic systems and
delta-matroids give the algebra of component counts under 2-swaps). Not yet
pursued; logged so it is not rediscovered.

## Reproduce

`nogap_verify.py` needs `lamp_lib.py` from `code/zeta_probe/route_b/`, which is
untracked (`.gitignore:77`); set `LAMPLIB` to point at it. Anything involving `Z`
or `l_R` should go through `tools/sitecost` (exact, Rust) rather than a Python
reimplementation -- three attempts at that failed here.


## Rust tool (this directory)

`cargo build --release; ./target/release/nogap <depth>`, run under `../runcap.sh`.
Exact integer arithmetic; no floating point outside the ETA display. Depth 31 is
5 033 690 elements enumerated, 3 336 511 used, peak RSS 1265 MB, 6 seconds.
It reproduces the Python numbers at depth 21 exactly (50763 / 48715 / 42361).

`prop:cut` (`c >= |Z|`) is asserted as an invariant: it is PROVED, so a violation
means a bug in this tool, not in the mathematics. That control is what localised
the boundary-term condition.

## Published series are NOT corrupted by the relaxed_solve bug

Recomputed from the closed form at depth 31 (exact for `m <= 18`):

| series | computed | stored | verdict |
|---|---|---|---|
| pure travel, 19 terms | `... 1276 1907 2832` | `lifting_U.tex` | identical |
| `u_n`, 19 terms | `... 3203 4971 7574` | `joint_W.json` | identical |
| `v_m`, `m <= 18` | `... 3513 5455 8418` | `v110.json` | identical |

The bug's blast radius is confined to per-element `c` obtained by calling
`relaxed_solve` directly. The one place the papers do that (`uv_perelem.py`, for
`prop:local`) is on pure-travel elements, where it is correct.

## M6b: obstruction (Rule 2)

Merging an isolated cycle at zero cost needs a 2-swap at a shared site whose two
new pair costs sum to the two old ones. Since a relaxed-optimal `R` has `Delta >= 0`
for every swap, a merge exists iff some swap achieves `Delta = 0`. At the cycle's
leftmost site all of its ends are on the R side, so it bounces, and swapping
against a pass gives `Delta = pc(alpha_C, d_gamma) - pc(alpha_gamma, d_gamma)`,
which vanishes iff the R-side ends there share a sign. The sign splits `p^u_j` are
free and provably do not affect site cost, but they are coupled globally by
`p^d_j = p^u_j + (d_j - f_j)/2`, so they cannot be set site by site; forcing
all-plus at edge `p` needs `d_p = -f_p`, false in general. That is the wall.

## M6a formalisation (Rule 5)

`lean/with_mathlib/NoGapCutFree.lean`, in `defaultTargets`. Nine declarations,
zero `sorry`, axioms confined to the standard three and no `native_decide`:

```
f_eq_zero_of_nonneg_of_le  [propext, Quot.sound]
f_neg_imp_k_neg            [propext, Quot.sound]
f_pos_imp_k_pos            [propext, Quot.sound]
f_neg_imp_lt_zero          [propext, Quot.sound]
f_pos_imp_lt_k             [propext, Quot.sound]
cut_at_zero                [propext, Classical.choice, Quot.sound]
cut_at_k_left              [propext, Classical.choice, Quot.sound]
cut_at_zero_eq_k           [propext, Quot.sound]
f_zero_of_k_zero           [propext, Quot.sound]
```

Reproduce with a file containing `import NoGapCutFree` and `#print axioms` on
each name, run through `lake env lean`.

Two cases of the analysis are absent by design: at a bulk site, and at `s = k*`
with `delta* = 1`, `alpha` and `Phi` are `d (s-1)` and `f (s-1)` definitionally,
so the cut hypothesis IS the assertion that edge `s-1` is a gap edge. Stating
those as Lean theorems produced declarations depending on no axioms at all, which
is the signature of a tautology; they were removed rather than counted.

Adversarial review (Rule 6) also found the `alpha` component unused in
`cut_at_zero`: `beta` and `Phi` alone force the conclusion, so the lemma is
sharper than the cut hypothesis and is now stated that way.

## Rule 1 transfer pass on M6b (2026-08-22)

### Prior art located

* **Cohn-Lempel equality / circuit-nullity formula** (Cohn-Lempel 1972; extended to
  undirected 4-regular graphs by Traldi, `arXiv:0903.4405`): the number of circuits
  in a circuit partition relates to the GF(2) nullity of the interlacement matrix,
  `|P| - c(F) = nu(G_P)`.
* **Kotzig 1968**: `T`-compatible Euler systems exist for **every** transition set
  `T` containing at most one transition per vertex.
* **Fleischner-Sabidussi-Wenger**: all `T`-compatible Euler systems are reachable
  from any one by kappa-transformations and transpositions.
* **Bouchet**: isotropic systems / delta-matroids give the algebra of transition
  systems and their component counts under 2-swaps.

### Dictionary

| here | classical |
|---|---|
| transition system at a site | transition system / Euler system |
| zero-cost 2-swap merge | kappa-transformation |
| `c(g)` isolated cycles | GF(2) nullity of the interlacement matrix |
| M6b (`c = 0` reachable) | some admissible system has nonsingular interlacement matrix |
| admissible (= min-cost) systems | delta-matroid feasible sets |

### Verdict

The dictionary **relocates** the difficulty without dissolving it. Kotzig's theorem
needs `T` to forbid at most one transition per vertex; our constraint instead
specifies a SET of allowed pairings (the min-cost ones), which is not of that form.
Kotzig therefore does not apply off the shelf. Under Cohn-Lempel, M6b becomes a
GF(2) rank condition, which is the more promising relocation, but the admissibility
constraint on which subsets may be used is the part with no classical counterpart.

Logged so the pass is not repeated. Not a closure of M6b.

### New ingredient obtained from the pass: the forced-pass lemma (PROVED)

> At an interior non-marker site, if neither adjacent edge is a gap edge, then
> EVERY min-cost pairing has at least one pass.

Proof. At a non-marker site the arrival/departure balance forces `f_L = f_R =: f`.
If `f != 0` then `P_LR - P_RL = f`, so `P >= |f| >= 1`. If `f = 0`, a pass-free
pairing bounces each side internally; the minimum number of sign-flip bounces on
the left is `|p^u_L - p^d_L| = |d_L|/2`, costing `|d_L|`, and likewise `|d_R|` on
the right, so pass-free costs `|d_L| + |d_R|`, against a minimum of
`max(|d_L|,|d_R|)`. Pass-free is optimal exactly when `min(|d_L|,|d_R|) = 0`, i.e.
`d_L = 0` or `d_R = 0`, which with `f = 0` says one of the two edges is a gap edge.
QED

Falsification: 1699 site configurations (`|f| <= 1`, `m <= 6`, every admissible
deposit and every sign split, min cost by exhaustive integer transportation),
**0 violations**; the same run independently reconfirms `lem:transport`
(`Site = max(|d_L|,|d_R|,|f|)`), also 0 violations.

This is the structural input the Kotzig-type results need: under no gap edges the
transition system is forced to communicate across every interior site. It does NOT
by itself give a single component, since one pass links one strand pair while other
strands may still close into cycles. That remaining step is the open part of M6.
