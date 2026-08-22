# no-gap / shield-law findings

Session 2026-08-22. Labels per Rule 0.

## Summary

| # | Statement | Label |
|---|---|---|
| M6a | no gap edge => `Z` empty | **PROVED** (below), verified 42361 elts |
| M6  | no gap edge => `c = 0` | **HEURISTIC** (42361 elts, depth 21, 0 violations) |
| M6b | `Z` empty => `c = 0` | **CONJECTURE** (48715 elts, 0 violations) |
| SL  | shield law `c = \|Z\|` incl. boundary term, all `k*` | **HEURISTIC** (50763 elts, 0 violations) |
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
