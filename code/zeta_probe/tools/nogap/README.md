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

## M6 PROVED: no gap edge => c = 0.  Adversarial review done; one gap found, repaired, and closed

The transfer pass overturned the obstruction recorded above. The claim there, that
the sign splits `p^u_j` are free, is FALSE at minimum multiplicity. They are forced,
and forced to be homogeneous, which is exactly what the merge argument needed.

**Step 1. A relaxed-optimal realization has `m_j = m*_j`.**
The site cost `max(|alpha|,|beta|,|Phi|)` is independent of `m` and of the sign
split (`sitecost` mode `universal`, 4 532 157 configurations, 0 exceptions), so
raising any `m_j` by 2 adds 2 to `sum m` and lowers nothing.

**Step 2. No gap edge => `d_j != 0` on every span edge.**
`d_j = 0` with `f_j = 0` is a gap edge. `d_j = 0` with `f_j != 0` is impossible,
since `d_j = f_j (mod 2)` would force `f_j` even.

**Step 3. `m_j = |d_j|`, and the sign split is forced and homogeneous.**
`|d_j| >= |f_j|` in both parities, so `m*_j = |d_j|`. Then
`p^d_j = p^u_j + (d_j - f_j)/2` together with `0 <= p^d_j <= dn_j` forces
`p^u_j = 0` when `d_j > 0` and `p^u_j = u_j` when `d_j < 0`. Hence every
up-crossing of edge `j` carries sign `-sgn(d_j)` and every down-crossing carries
`+sgn(d_j)`. Checked on all 24 admissible no-gap edge configurations: the split is
unique, homogeneous, and follows the `sgn(d)` rule, 0 exceptions.

**Step 4. For edge strands the pair cost depends only on the side pattern.**
Arrivals on the left are up-crossings of the left edge, departures on the left are
its down-crossings, and by Step 3 these carry opposite signs. So
`pc(L,L) = pc(R,R) = 2` and `pc(L,R) = pc(R,L) = 1`.

**Step 5. A 2-swap is free exactly when the two pairs share an arrival side or a
departure side.** Over the 16 side patterns, `Delta = 0` in 12, `Delta = -2` in 2,
`Delta = +2` in 2, and `Delta = 0` holds precisely under that condition. The two
`Delta = -2` patterns (`a=L, a'=R, d=L, d'=R` and its mirror) cannot occur in a
cost-minimal realization.

**Step 6. Conclusion.** Take a relaxed-optimal realization minimising the number of
components and suppose it has an isolated cycle `gamma`. The support of `gamma` is
an interval (a walk cannot skip an edge), so at its leftmost site all of its ends
lie on the R side and all of its pairs there are `(R -> R)`. Any other component
present at that site either shares the arrival side R or the departure side R, and
the merge is free by Step 5; or all of its pairs are `(L -> L)`, which is a
`Delta = -2` pattern and contradicts cost-minimality. A 2-swap between pairs of
different components merges them, so either way there is a relaxed-optimal
realization with strictly fewer components, contradicting minimality. Hence there
is no isolated cycle and `c = 0`. QED

**Consequences.** `prop:local`(i) follows, since support inside `I_k` implies no gap
edge; and `prop:travelinv` (=(T)) follows from it by the two-line argument already
in `lifting_U.tex`. That removes (T) from the hypotheses of `U`, leaving (L).

### Adversarial review (Rule 6), and the repair

The review attacked step 6 and found a genuine gap: the argument privileged
`gamma`. If `gamma`'s leftmost site is `lo` AND `gamma` owns every strand of edge
`lo`, that site is unshared and the argument stalls. The earlier hand-check missed
this.

Two facts, both checked exhaustively over the side patterns, replace it:

* **A component with a bounce at a shared site always merges free** (0 blocking
  cases).
* **Blocking requires BOTH components to have a pass, in opposite directions**
  (only `A=(L,R), B=(R,L)` and its mirror, 2 of 16 patterns).

**Step 6 (repaired).** Suppose a component-count-minimal relaxed-optimal
realization has at least two components. If two of them hold strands of edge `lo`,
then site `lo` is shared and both have `(R -> R)` bounces there, so the merge is
free. Otherwise one component owns edge `lo`; let `B` be any other component with
minimal leftmost site `r`, so `r > lo`. Edge `r-1` is then in the span with
`m >= 1`, and its strands are not `B`'s, so site `r` is shared; `B`'s ends at `r`
come only from edge `r`, so `B` bounces there and the merge is free. Either way the
component count drops at no cost, contradicting minimality. Hence one component,
and `c = 0`. QED

**Residual, narrowed to a single configuration.** The virtual ends do not obey the
sign homogeneity of Step 3, so the site carrying the virtual arrival needs its own
enumeration. Doing it exhaustively: with `B` holding the virtual arrival at its
leftmost site `r`, `B` may have one `(L -> R)` pass and no bounce. Against a
neighbour `C` the four pair types give

| `C`'s pair at `r` | `Delta` | outcome |
|---|---|---|
| `(L -> L)` bounce | `-2` or `0` | contradiction or free |
| `(L -> R)` pass | `0` | free |
| `(R -> L)` pass | `0` or `+2` | free, or BLOCKED when `sgn(d_{r-1}) = -1` |
| `(R -> R)` bounce | `0` | free |

so the only blocker is `C` with an `(R -> L)` pass and `d_{r-1} < 0`. In that
configuration `C` has no `L`-arrival at `r`, hence its strands on edge `r-1` are
all down-crossings. Any up-crossing of edge `r-1` would belong to some other
component, which then has an `L`-arrival at `r` and merges with `B` for free by the
shared arrival side. So the blocker additionally requires `u_{r-1} = 0`, i.e.

    d_{r-1} = f_{r-1} = -1,  a single strand on edge r-1.

**That configuration is impossible.** `f_{r-1} = -1` forces `k* <= -1 < 0`, and
`r = 0` because `r` carries the virtual arrival. So edge `-1` has `d = f = -1` and
carries exactly one strand. The marker component `B` holds the virtual arrival at
site `0` and must also hold the virtual departure at site `k* <= -1`, so `B` is a
walk from site `0` to site `k*` and must traverse edge `-1`. Its single strand
therefore belongs to `B`, contradicting the assumption that it belongs to
`C != B`. Hence the blocker never arises and **M6 is proved**.

End-to-end, the statement is verified on 2 505 271 elements to word length 31 with
0 exceptions, which is independent of the proof above.

## M2 proved: the relaxed length decomposes, at every k*

`sitecost` verifies `l_R = sum m + sum max(|alpha|,|beta|,|Phi|)` by direct
enumeration only for `k* = 0` (mode `shield`). The site-cost law itself is verified
much more widely: mode `universal` covers all eight site types and all four marker
data over 4 532 157 configurations, every crossing count and every sign split, with
0 exceptions. What was missing at `k* != 0` is only that the global minimum
**decomposes** into the sum of the local minima. It does:

1. The site cost `max(|alpha_s|,|beta_s|,|Phi_s|)` depends only on the deposits and
   the travel indicator. It is independent of the crossing counts `m_j` and of the
   sign splits `p^u_j` (this is exactly what mode `universal` establishes).
2. Therefore `sum_j m_j` is minimised separately, at `m_j = m*_j`, the minimum
   admissible multiplicity, with a gap edge of the span forced to 2 by reachability.
3. Edge `j` has one end at site `j` and one at site `j+1`, but as a departure at the
   first and an arrival at the second. So the matchings at distinct sites act on
   disjoint sets of ends and may be chosen independently.
4. In the relaxed model any choice of per-site perfect matchings is admissible,
   since isolated cycles are permitted and carry no extra cost.

By 1 and 2 no term can be lowered below its local minimum, and by 3 and 4 all local
minima are attainable simultaneously. Hence

    l_R = sum_j m*_j + sum_s max(|alpha_s|,|beta_s|,|Phi_s|)

for every `k*`, not only in the bulk. The coupling one might fear, that the sign
splits are shared between adjacent sites, is harmless precisely because the site
cost does not see them.

Note the contrast with the true metric: there the single-open-walk requirement does
couple the sites, which is why `l_T` does not decompose and needs the whole M6
argument.

## M10 fixed

`route_b/lamp_lib.py` (untracked) now routes `relaxed_solve` through
`relaxed_closed`, the closed form, and prints a loud stderr warning whenever the old
DP disagrees. The DP is kept as `_relaxed_solve_dp` for diagnosis. Callers get
correct values instead of silently wrong ones.

## NO-GO: the M6 argument does NOT generalise to the reverse shield inequality

The natural next move is to run the merge argument at every non-cut site and
conclude `c = |Z+|`, closing `rem:shieldowes`. It fails, and the reason is exactly
the ingredient M6 depends on.

M6 works because no gap edge forces `m_j = |d_j|`, which forces the sign split, so
the pair cost sees only the side pattern. With gap edges present that collapses:
a gap edge has `m = 2` and `d = 0`, so `p^d = p^u` with `u = dn = 1` leaves two
admissible splits, and homogeneity is gone.

Enumerating all 256 sign-and-side configurations of a 2-swap:

| | count |
|---|---|
| `Delta = 0` | 152 |
| `Delta < 0` (impossible at a cost minimum) | 52 |
| `Delta > 0` (blocking) | 52 |

and both criteria that carry M6 are false in general:

* **"sharing an arrival or departure side implies free" is FALSE**: 36 of the 52
  blockers share a side.
* **"a cost-0 bounce always merges free" is FALSE**: 28 counterexamples, e.g.
  `A = ((L,+) -> (L,+))` against `B = ((L,-) -> (L,-))`, which gives `Delta = +4`.

So `c <= |Z+|` is not reachable by this route. It remains HEURISTIC on 3 336 511
elements to word length 31. Do not retry the naive generalisation; a different
mechanism is needed for the sites where the split is free.

## Formalisation: two modeling errors found by testing, and what they cost

The Lean development of `thm:nogap` (2026-08-22/23, `lean/with_mathlib/`) proved
every mathematical input of the argument. Trying to write the model as a whole,
rather than accreting it, then found two errors in the interpretation. Both were
caught by attempting to satisfy a specification, not by reading proofs.

**One: cycles of the transition system are not the components.** A component is a
walk, and a walk alternates crossing an edge with turning at a site; the transition
system only turns. In the smallest instance, one edge with an up- and a
down-crossing, its cycles are the pair of top ends and the pair of bottom ends, so
the two ends of one crossing lie in different cycles.

**Two: cycles of `turn . partner` are not the walks either.** Measured on small
configurations:

| configuration | walks | cycles of `turn . partner` |
|---|---|---|
| closed walk, no `turn` fixed points | 1 | 2 |
| open walk, `turn` fixed at both ends | 1 | 1 |

A closed walk splits into two cycles of the product, an open one does not. In our
setting the marker component is open and the isolated cycles are closed, so

    #cycles(pi) = 1 + 2c,   i.e.   c = (#cycles(pi) - 1) / 2.

**The consequence for the merge.** A 2-swap re-pairs at a site, and `turn` must
remain an involution, so the change is composition with a **double** transposition.
That lowers the cycle count by two and the walk count by one. `CycleMerge`, which
treats a single transposition, therefore does not model a transition-system 2-swap,
and `RealizationModel.comp` cannot be read as a cycle count of either `turn` or the
product without the correction above.

**What survives.** Every purely mathematical statement: the forced sign split, the
forced-pass lemma, the swap criterion over side patterns, the shared-site argument,
the two cycle lemmas Mathlib lacks, the counting step, and the descent. Those are
theorems about deposits, side patterns, permutations and finite sets, and none
depends on the interpretation. The paper proof is unaffected, its components being
walks throughout.

**What is owed.** A model built on the correct correspondence: `c` as
`(#cycles - 1)/2`, and the merge as a double transposition. That is a redesign of
the interpretation layer, not a further lemma, and it is why the formalisation debt
on `thm:nogap` did not clear.

### A measurement that did not apply, and why it is recorded

Chasing the corrected merge, the double-transposition analogue was measured on
random permutations. Across two cycles it gave `-2` about 71 per cent of the time
and `0` otherwise; restricted to the shape thought to match the application, `a, d`
in one cycle and `a', d'` in another, it gave `0` in all 853 samples.

**That measurement does not apply, and the `0` must not be read as a result.** The
permutation in question is `turn . partner` with both factors involutions, which is
a structured class, not a uniform random permutation, and the four points are tied
to `turn` and `partner` rather than chosen freely. The restriction used also
assumed `a` and `d` share a cycle, which is not established: `d = pi(partner a)`
does not place `a` and `d` in one cycle of `pi`.

The single-transposition control in the same run is sound and reconfirms
`CycleMerge`: across two cycles the count fell by exactly one in 9987 of 9987
samples.

The lesson is the same one the two modeling errors taught, in a different guise: a
measurement on the wrong ensemble is as misleading as a proof of the wrong
statement, and neither is caught by checking axioms. Any future measurement here
must sample `turn` and `partner` as involutions with the site and edge structure,
not permutations at large.

### The correct ensemble, and the merge measured on it

Generating `turn` and `partner` as involutions with the site and edge structure
imposed, rather than sampling permutations at large:

* ends are `(edge, crossing, atTop)`; `partner` exchanges the two ends of a
  crossing; `turn` is a random perfect matching of arrivals to departures at each
  site, an up-crossing arriving at its top end and a down-crossing at its bottom
  one;
* `pi = turn . partner`, walks are the orbits of the two involutions together.

**First, the relation.** On 810 closed configurations, `cycles(pi) = 2 * walks`
with no exceptions, confirming the earlier hand-worked cases.

**Then the merge.** Re-pairing two arrivals at one site, which is the 2-swap:

| `a, a'` in different walks | delta cycles | delta walks | count |
|---|---|---|---|
| yes | -2 | -1 | 479 |
| no | +2 | +1 | 486 |

No exceptions either way. A 2-swap between arrivals in different walks merges them,
lowering the walk count by exactly one; within one walk it splits, raising it by
one. That is the merge the argument needs, and it is what the earlier
random-permutation run failed to see.

So the corrected chain is: the defect is `(cycles - 1)/2` in the presence of the
markers and `cycles/2` in the closed case; a transition-system 2-swap across two
walks lowers the walk count by one; and the free-swap criterion, which is about
side patterns and already verified, decides when that merge costs nothing. What a
Lean model still owes is this correspondence, not the merge criterion.

### The remaining obligation, reduced to a named classical statement

`WalkMerge.conn_merge` carries one hypothesis, `hpath`: after the re-pairing, the
other walk stays connected having lost its turn-edge.  That is the statement that a
cycle minus one edge is still a path, and it is the only thing between the measured
merge and a proved one.

It is not an open modelling question.  Mathlib has

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` -- an edge is a bridge
  exactly when it lies in no cycle;
* `SimpleGraph.isBridge_iff` -- an edge is a bridge exactly when it is adjacent and
  its endpoints are not reachable after deleting it.

So `hpath` follows once the turn-edge is exhibited inside a cycle, and in the graph
at hand every edge is: the graph has an edge of each kind at every end, so it is
2-regular and its components are cycles.

The route is therefore: build the `SimpleGraph` on ends whose adjacency is
`y = p x` or `y = t x`; prove it 2-regular from the two involutions; conclude every
edge lies in a cycle; apply the two lemmas above to get `hpath`; and discharge
`conn_merge`.  That is a bounded piece of standard graph theory with library
support, not a further piece of the reflection-group argument.

Recorded so the next attempt starts from the reduction rather than rediscovering
it.

### The no-go refined: the local obstruction is exactly a cut site

The earlier no-go treated the signs at a gap edge as given. They are not: a gap edge
has `m = 2`, `d = 0`, `f = 0`, so `p^d = p^u` with `p^u` free, and the two crossings
share a sign either way. In building a relaxed-optimal realisation that choice is
ours.

Measuring with the choice available: of 64 configurations where one pair sits on a
gap edge, **60 admit a choice making the swap free or cheaper**, against 52 of 256
blocking when all signs are fixed. Only **4** block under both choices, and they are
all the same shape:

    A = (L,s) -> (L,s)      B = (R,g) -> (R,g)      and its mirror

that is, **both components have a cost-zero bounce, on opposite sides**.

That shape is worth naming. Under the homogeneity that no gap edges forces, a bounce
costs 2, since arrivals and departures on a side carry opposite signs; swapping two
such bounces gives two passes at `1 + 1`, so the merge is free. At a gap edge a
bounce can cost 0, and then the same swap costs `+2`.

And cost-zero bounces on both sides is exactly `alpha = beta = Phi = 0`, the cut-site
condition of `prop:cut`. So the local obstruction to merging is precisely a cut
site.

**This refines the no-go rather than overturning it.** What is now clear is where
the difficulty sits: not in the merge, which the walk formulation handles, and not
in gap edges as such, whose sign freedom rescues almost everything, but exactly at
the sites `prop:cut` already identifies. Whether that local statement assembles into
`c <= |Z|` is not settled here; it is a lead, and it is the first one that points at
the cut sites themselves rather than away from them.

### The route the refined no-go opens, and the step it turns on

With the local obstruction identified as exactly a cut site, the reverse inequality
has a route:

1. Suppose a cost-minimal realisation has more than `|Z| + 1` components.
2. Removing the `|Z|` cut sites splits the ends into `|Z| + 1` classes.
3. By pigeonhole some class contains two distinct components.
4. Within a class the ends are connected through non-cut sites only, so two
   distinct components meet at some non-cut site.
5. There the merge is free, by the refined local statement, so the component count
   drops at no cost, contradicting minimality.

Hence `c <= |Z|`, and with `prop:cut` the shield law.

Steps 1, 2, 3 and 5 are in hand: the cut count is defined, the classes are its
complement, pigeonhole is pigeonhole, and step 5 is the measurement above together
with the merge already proved. **Step 4 is the one that is not.** It says two
components lying in the same class must actually meet, rather than merely lying in
a common class without sharing a site. That is a connectivity statement about the
class, and it is where `prop:cut`'s own argument already works, since that
proposition reasons about exactly this decomposition to get its lower bound.

Recording the route rather than claiming the conclusion. What has changed is that
the difficulty is now one named step inside a decomposition the paper already uses,
instead of an obstruction that looked like it ruled the approach out.
