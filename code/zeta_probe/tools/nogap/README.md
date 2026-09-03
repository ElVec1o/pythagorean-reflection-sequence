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

### Step 4 is `shared_site_exists`, applied within a class

Step 4 asks that two components lying in one class actually meet. They do, and the
argument is one already proved.

A class is the run of edges between two consecutive cut sites. Components have
interval supports, so two components in one class have interval supports inside it.
If those intervals are adjacent the components share the site between them. If they
are separated, every edge in between is still covered, so a third component lies
there, and repeating the argument on an adjacent pair gives a shared site.

That is exactly `SharedSite.shared_site_exists`, which takes a covering hypothesis
and returns two components sharing a site, either at the left end or one step inside.
Applied to a class rather than to the whole span it gives the same conclusion, and
the site it returns is interior to the class, hence **not** a cut site, because the
cut sites are precisely the class boundaries.

So the route closes, subject to the instantiation being carried out: restricting
the components and the covering hypothesis to a class, and checking the returned
site is interior. The covering within a class is inherited from the covering on the
span, since a class is a sub-interval of it.

**What this means for the reverse inequality.** Every step of the route now points
at something proved: the cut count and classes are definitions, pigeonhole is
pigeonhole, the free merge at a non-cut site is the measurement plus the proved
merge, and the meeting of two components in a class is the shared-site theorem. The
work remaining is the instantiation, not new mathematics. That is a materially
different position from the no-go this section opened with, and it should be checked
carefully by someone who did not write it before the inequality is called proved.

## The placement had to be rebuilt over walks, not cycles (2026-08-23)

`SitePlacement` builds the component support out of `π.SameCycle` and delivers two
ends in different `sig`-cycles. `config_descent` needs two ends in different
*walks*. These are not the same condition, and the difference is the one that
invalidated `CycleMerge` earlier: `sig` has twice as many cycles as there are
walks, so two ends in different `sig`-cycles may lie in a single walk. `¬ SameCycle`
does not give `¬ Reachable`.

This was first written down as "bookkeeping, not mathematics". That was wrong.

`WalkSupport` rebuilds the support over reachability. The proofs are the same shape,
and one hypothesis becomes *cheaper*: strand-closure had to be assumed for cycles,
but an end is always adjacent to its crossing partner (`Adj x (p x)` by `Or.inl
rfl`), so over walks it is a theorem (`reachable_partner`), not a hypothesis.

`walk_shared_site_pair` is the corrected placement: two ends at a common site in
different walks, which is exactly `config_descent`'s pair with `hsplit` as the
second conjunct.

`SitePlacement` is kept -- its statements are true, and the cycle-level support is
still what the `cLo`/`cHi` interval dichotomy in `GapFreeAssembly` is stated over.
It simply does not feed the descent.

## The last half of k2 is a parity fact, not a group identity (2026-08-23)

ClosesAvoiding has five clauses. Four are free: hM and hpos from exists_closes
(sig is injective on a finite set, so orbits are periodic), and k1 and klast
because they are about *crossing* edges while the deleted set consists of *turn*
edges (crossing_ne_turn). All content is in k2.

k2 splits in two. The cross-walk half -- an orbit at `a` never meets `a'`'s turn
edge -- is orbit_avoids_other, and follows from hsplit alone.

The self half needs: the orbit at `a` does not meet `a`'s own turn edge before
closing. k2_self_dichotomy reduces it to two cases: the orbit closes early
(excluded by taking M minimal), or `p a` lies in `a`'s own sig-orbit.

That last is TRUE but is a PARITY fact. Each walk is an even cycle alternating
crossing and turn edges; the two sig-orbits are its two alternating classes, and
`p a` is adjacent to `a` on the cycle, hence in the other class.

It does NOT follow from the group relations. sig_p_eq_t (sig on p is t) and
p_t_sig (p after t inverts sig) say the two involutions generate a dihedral
action with p conjugating sig to sig^{-1}. Those relations are CONSISTENT with
p a = sig^k a; what rules it out is the even length of the cycle. So the
remaining work is the alternating-class argument, not more identity juggling.

## The merge loop is closed (2026-08-23)

merges_to_one: every configuration merges down to a single walk. The invariant
carried through the induction is Merges -- the crossing map is unchanged, and the
turn still respects sites and alternates arrival/departure. All three survive the
re-pairing: swapData_p, swapT_site, swapT_arr.

The step is descent_of_split, whose only remaining input is hsplit, and hsplit is
produced by arrivals_of_many_walks exactly when more than one walk remains.
reaches_one iterates. The covering hypothesis is stated D-independently (hcov0),
since whether an edge carries a top end does not depend on the pairing.

Chain, end to end, all kernel-certified with no native_decide and no sorry:
  1 < walkCount  -> exists_split_of_walkCount -> two ends in different walks
                 -> pair_of_two_walks         -> two ends at a common site
                 -> arrival_beside            -> two ARRIVALS at a common site
                 -> descent_of_split          -> walkCount strictly drops
                 -> reaches_one               -> walkCount <= 1

## The covering hypothesis was false as first stated (2026-08-23)

merges_to_one's covering input was first written

  forall j : Z, (exists v, edgeOf v < j) -> exists y, edgeOf y = j-1 and atTop y

quantified over ALL integers j. That is FALSE for every non-empty configuration:
take j beyond the last edge, the antecedent holds and the conclusion cannot. So
config_merges_to_one, as committed in 5ea3a59, was VACUOUS.

Caught by trying to discharge it rather than by any build signal -- it compiled,
certified clean, and had no sorry. This is the fourth vacuity trap of the session
and the pattern is identical each time: a hypothesis assumed rather than exhibited.

The fix: j is only ever instantiated at wLo, which IS some end's edge, so the
antecedent gains (exists u, edgeOf u = j). With that, 0 <= j < n, the second
antecedent forces j >= 1, and j-1 is a genuine edge index.
covering_of_mult_pos then discharges it from positivity of multiplicities.

gapfree_merges_to_one: a gap-free configuration merges to a single walk, assuming
only the balance that defines the turn and positivity of every multiplicity.

## The substantive witness (2026-08-23)

one_edge_merges instantiates gapfree_merges_to_one at n=1, m=2, up=1: one edge
carrying two crossings, one of them up. Both of its sites are boundaries -- site 0
holds the two bottom ends, site 1 the two top ends -- and each balances because
min 1 2 = 1 = 2 - 1, which is exactly balance_left and balance_right.

This is the witness the empty configuration could not be. With m e = 2 > 0 the
hypothesis hm is not vacuous and covering_of_mult_pos is genuinely exercised, so
the whole chain from hbal through the merge loop is exhibited on real data.

## RealizationModel's swapAt does NOT model the 2-swap (2026-08-23)

RealizationModel.swapAt r x y = swap x y * r.trans, and its docstring claimed a
2-swap sends the turn t to swap o t, hence the walk to swap o walk. That is FALSE.

With a, a' the two arrivals and d = t a, d' = t a', the re-paired turn is
WalkGraph.swapT, and

  swapT o t : a -> d -> a',  a' -> d' -> a,  d -> a -> d',  d' -> a' -> d

so swapT = (a a')(d d') o t, a DOUBLE transposition, and sig' = (a a')(d d') o sig.
By contrast swap d d' o t sends d' -> a' where the re-pairing sends d' -> a. No
single left or right transposition gives swapT, and it cannot: swap o t is not an
involution, while the turn must stay one.

comp_swapAt_lt and NoGapCapstone.nogap remain TRUE theorems about single
transpositions. What was wrong is only the claim that they model the merge. Note
too that orbitCount of the walk permutation counts TWICE the number of walks, since
p maps each sig-orbit to a different one -- which is now proved
(ConfigMerge.p_not_in_orbit) rather than assumed.

This is the third appearance of cycles-vs-walks in this session and the second time
it was hiding inside a docstring rather than a proof. The correct formalisation is
the chain ConfigMerge -> WalkSupport -> ConfigLoop, over graph components with the
involutive re-pairing swapT, ending at ConfigLoop.gapfree_merges_to_one.

M6's formalization debt is therefore NOT discharged by wiring nogap up. nogap is in
a model that does not match; the content is carried by gapfree_merges_to_one.

## thm:nogap's conclusion in the walk model (2026-08-23)

gapfree_merges_to_one gives walkCount <= 1. thm:nogap asserts the defect VANISHES,
which is exactly ONE walk, so the lower bound is wanted too. gapfree_single_walk
supplies it: a positive multiplicity puts an end on the edge, so the component set
is non-empty and walkCount >= 1. one_edge_single_walk instantiates it concretely.

Checked while there: paper2 does NOT claim a Lean formalisation of thm:nogap. It
cites only the Rust verification, 2,505,271 elements of length <= 31 with no
exceptions. So the model mismatch found in NoGapCapstone and RealizationModel never
reached the paper, and there is nothing to retract there.

## defect = c is a MODELLING CLAIM, not yet verified (2026-08-23)

The paper's c(g) counts ISOLATED CYCLES: a realisation is one open walk plus c
closed cycles, and thm:nogap says c = 0.

In the Lean model the turn is a TOTAL involution on all ends, so the walk graph is
2-regular everywhere and every component is a closed cycle -- the open strand is
closed up. The component count is therefore 1 + c PROVIDED one component is
designated as the open walk. Nothing in the formalisation designates one; all
components are symmetric under the structure as written.

So gapfree_defect_zero proves thm:nogap in the WALK MODEL, with
defect D = walkCount D - 1. The identification defect = c needs a basepoint, or an
argument that the open walk is distinguishable.

This is recorded rather than asserted. Two claims of exactly this kind
(transition-system cycles = components; the 2-swap is a single transposition) were
made on inspection earlier in this development and both were false. The remaining
formalization debt on M6 is precisely this identification, and it is now named
instead of hidden.

## The basepoint closes defect = c (2026-08-23, same day, supersedes the entry above)

The entry above recorded that defect = c needed a basepoint or an argument that the
open walk is distinguishable. The basepoint is available: a realisation has a
designated open walk because the word has a start.

otherComponents D b counts the components other than b's -- the isolated cycles --
and otherComponents_eq_defect proves it equals walkCount D - 1 UNCONDITIONALLY, for
any b. So with a basepoint the identification is definitional, not a modelling claim.

gapfree_no_isolated_cycles: a gap-free configuration has no isolated cycles, for
EVERY basepoint. The quantifier is free here: walkCount = 1 leaves no other
component for the choice of b to matter to.

So M6's chain now reaches thm:nogap's actual statement. What the model still does
not carry is which end is the word's start -- but the theorem holds for all of them,
so nothing depends on choosing.

## thm:nogap as one named theorem (2026-08-23)

ConfigLoop.thm_nogap states the paper's thm:nogap in one place, so the
correspondence is checkable without reassembling it from eight files.

FORMALISED: a configuration is (m, up); "no gap edge" is forall e, 0 < m e; hbal is
the arrival/departure balance (interior sites by card_arr_eq_card_dep_of_edges, the
two boundaries by balance_left/balance_right). Conclusion: some realisation has
exactly one walk and no isolated cycle against any basepoint -- c(g) = 0.

NOT FORMALISED, and stated in the docstring rather than left implicit:
 - the passage from a group element g to its configuration;
 - cost-minimality of the realisation produced. The merge preserves Merges, which
   carries the crossing map and the turn's site/role laws, NOT a cost.

So this is thm:nogap for CONFIGURATIONS, which is where its content lies, and not a
formal proof of the paper's sentence about g. thm_nogap_witness instantiates it on
the one-edge configuration so the statement is known to have content.

## The merge is cost-neutral (2026-08-23)

CostMerge.cost_swapData: re-pairing two arrivals that share a side -- or whose
departures do -- leaves EndData.transCost unchanged.

The bridge is that transCost sums pcostF a (pi a) over ARRIVALS ONLY, and on
arrivals the involutive re-pairing swapT agrees with the plain transposition
swap (t a) (t a') composed with t: both send a to t a' and a' to t a, and away from
the four ends neither moves anything, since t x in {t a, t a'} forces x in {a, a'}.
They differ only AT t a and t a', which are departures and therefore invisible to
the sum. So the existing transCost_swap_free applies to swapT even though
swapT is not swap o t as a function -- which is exactly the mismatch that made
RealizationModel.swapAt the wrong model for the merge.

Still owed to make thm_nogap produce a RELAXED-OPTIMAL realisation: the shared-side
hypothesis. The chain's placement gives two arrivals at a common SITE, not a common
side. The side condition holds at the leftmost site (ComponentSupport
all_right_at_cLo / bounce_of_all_one_side), which is where the placement puts them,
but that argument is not yet transported into the walk model.

## The shared-side probe is INCONCLUSIVE -- do not read it as a counterexample (2026-08-23)

side_probe.py enumerates (m, up) on 1-2 edges, builds every turn pairing arrivals to
departures at each site, and asks whether two arrivals in different walks at a common
site ever share a side (or their departures do) -- the hypothesis cost_swapData needs.

It reports 9 of 91 multi-walk cases with NO such pair, and 9 of 27 when restricted to
"cost-minimal" turns. THAT RESTRICTION IS NOT THE PAPER'S. Two defects:

1. The cost proxy is wrong. It scores a pass as 1 and EVERY bounce as 0. The true
   pcostF charges 2 for a same-side bounce whose two ends have OPPOSITE SIGN. The
   sign is derived (EndData) from side, role, and the sign of the edge's DEPOSIT,
   and the probe has no deposits, so it cannot compute the real cost and its
   "cost-minimal" set is not T.

2. The probe enumerates (m, up) freely. Real configurations come from a group
   element, where m, up, deposits and travel are linked. Most enumerated tuples are
   not realisable.

So the 9 failures are failures of the PROBE'S model, not evidence against thm:nogap,
and they are not evidence for it either. Closing M6dy needs the sign/deposit layer
carried into the walk model; until then the shared-side hypothesis of cost_swapData
stays an explicit hypothesis.

Kept because the enumeration scaffolding is reusable once deposits are added.

## The shared-side pair DOES always exist -- the probe had the cost inverted (2026-08-23)

Supersedes the entry above. The defect was not the missing deposit layer. It was the
COST DIRECTION, and reading EndData.sgn settled it:

  sgn a = if side a then (isArr a ? D1 : !D1) else (isArr a ? !D0 : D0)

so for an arrival a and its departure t[a] sharing a side, sgn a and sgn t[a] are
ALWAYS opposite. A same-side arrival/departure pair is therefore always a
sign-flipped bounce costing 2, and a different-side pair is a pass costing 1.
Minimising transCost MAXIMISES passes.

side_probe.py scored bounces 0 and passes 1 -- exactly backwards -- so its
"cost-minimal" set was close to the cost-MAXIMAL one, and its 9 failures were
artifacts.

side_probe2.py, with the correct cost, over n = 1,2,3 edges: 263 cost-minimal turns,
146 of them with more than one walk, and ALL 146 admit two arrivals at a common site
in different walks sharing a side (or whose departures share one). Zero failures.

So the shared-side hypothesis of cost_swapData IS available at cost-minimal
realisations, and M6dy is closable. What the walk-model chain needs is
cost-minimality: hshared does not come from the placement alone, it comes from the
realisation being optimal. That is the missing ingredient, now identified.

## The cost-preserving merge loop (2026-08-23)

CostMerge.cost_merges_to_one: given a free pair whenever more than one walk remains,
the walks merge down to one AT UNCHANGED COST. The invariant is MergesCost = the
merge invariant plus a fixed cost, and it survives the re-pairing on all four counts:
swapData_p, swapT_site, swapT_arr, cost_swapData.

The free-pair input is isolated as HasFreePair: a datum with more than one walk
admits two arrivals at a common site, in different walks, sharing a side or with
their departures sharing one. That is what side_probe2.py confirms at cost-minimal
data -- 146 of 146 multi-walk cases on one to three edges -- and it is NOT PROVED.

So the architecture is complete and the remaining mathematical content of M6dy is
exactly one statement: cost-minimality implies a free pair. Everything downstream of
it is now formal.

## Minimality does NOT force a free pair at a given site (2026-08-23)

For an arrival and its departure, pcostF is 2 when they share a side (always a
sign-flipped bounce, since EndData.sgn makes their signs opposite) and 1 when they do
not. With sa, sa' the two arrivals' sides and da, da' their departures':

  free merge  <=>  sa = sa'  or  da = da'        (NoGapMerge.swap_free_iff)

When that fails, both differ, and there are two sub-cases which behave OPPOSITELY --
both proved by kernel decide:

  cross_cheaper : sa != sa', da != da', sa = da   =>  cross pairing is CHEAPER
  cross_dearer  : sa != sa', da != da', sa != da  =>  cross pairing is DEARER

The first case cannot occur at a cost-minimal datum, so it is excluded. The SECOND
case is locally optimal: both arrivals are passes, and exchanging their departures
turns both into bounces, costing +2.

So the argument sketched last round -- derive a contradiction from minimality at the
site where the placement puts the pair -- CANNOT WORK. A cost-minimal datum can have
a site whose two cross-walk arrivals admit no free merge.

This is consistent with the numerics: side_probe2.py checks whether a free pair
exists SOMEWHERE, not at every site, and found one in all 146 multi-walk cases. So
HasFreePair is a GLOBAL statement about cost-minimal data and needs an argument that
ranges over sites. It is a research step, not a formalisation step, and the local
engine for it is now proved.

## Where the free pair lives -- HasFreePair sharpened (2026-08-23)

Instrumented the probe to report WHICH pair is free and WHERE. (First attempt had a
bug: it kept pairs at DIFFERENT sites, which are not merge pairs at all. Fixed.)

Corrected counts over n = 1,2,3: 146 multi-walk cost-minimal cases, 2 to 6 free pairs
each, none with zero. Kinds: 532 arrivals-share-side, 128 departures-share-side.

Every one of the 146 has a free pair at a walk's leftmost site, one of the
arrivals-share kind, and one that is both. Refining further:

  two walks share a leftmost edge : 98 of 146   (this is pair_of_equal_wLo, Case A)
  the other 48 STILL have a "both bottom @ leftmost site" free pair

So one uniform statement covers every case, and it holds 1114 of 1114 on n <= 4:

  CONJECTURE (wlo_probe.py). At a cost-minimal transition system with more than one
  walk, there are two BOTTOM arrivals, in different walks, at a walk's LEFTMOST site.

Both being bottom ends they share a side, so the merge is free. This is much sharper
than HasFreePair -- it names the site and the side -- and it is exactly the shape the
Lean placement already produces: exists_bottom_at_wLo gives one bottom end at wLo, and
the content is that a SECOND walk has a bottom ARRIVAL there too.

## The canonical site: the MAXIMUM leftmost edge (2026-08-23)

The sharpened statement still had an existential over sites. It can be removed.

Let s* be the MAXIMUM, over walks, of a walk's leftmost edge. Then:

  CONJECTURE (maxwlo_probe.py). At a cost-minimal transition system with more than
  one walk, site s* carries two BOTTOM arrivals lying in DIFFERENT walks.

Both bottom means they share a side, so the merge is free. s* is determined by the
datum, so the merge pair is now canonical -- no choice, no search.

Verified 1114 of 1114 on n <= 4. Two routes that do NOT work, checked and discarded:

 - site 0 (equivalently the MINIMUM leftmost edge): 662 of 1114 only. Site 0 is
   attractive because every end there is a bottom, so any two arrivals share a side
   automatically -- but its arrivals often lie in a single walk.
 - the site-local minimality argument: refuted outright by cross_dearer.

n = 5 with m = 2 on every edge produces NO multi-walk cost-minimal systems at all, so
it adds no evidence either way.

The shape of a proof: at s* the walk achieving the maximum has ALL its ends bottom
(its support starts at edge s*, so it has no end on edge s*-1) -- that half is
already Lean, exists_bottom_at_wLo and not_atTop_at_cLo. What is owed is that a
SECOND walk contributes a bottom ARRIVAL at s*, and by cross_dearer that step must
use cost-minimality.

## CanonicalPair splits cleanly, and half of it is now PROVED (2026-08-23)

Probed the canonical-site conjecture claim by claim. It splits in two:

 (i)  the MAXIMISING walk has a bottom ARRIVAL at s*
 (ii) a SECOND walk also has a bottom arrival at s*

Counts over n <= 4:
   (i)  holds on ALL 76945 multi-walk systems -- minimal or not. 0 failures.
   (ii) fails on 15993 of 76945 general systems, holds on all 1114 cost-minimal ones.

So (ii) is exactly where cost-minimality bites, and (i) is unconditional.

(i) is now PROVED: WalkSupport.maximiser_has_bottom_arrival. The walk has a bottom
end at its leftmost site (exists_bottom_at_wLo); if that end is a departure, its
turn-partner lies in the SAME walk -- a turn is a graph edge -- at the same site, with
the opposite role (turn_arr_flip), and is a bottom end too
(bottom_of_end_at_wLo). Either way an arrival is available.

Also corrected a probe error on the way: a first attempt required the second walk to
lie OUTSIDE the maximising set and reported 644 of 1114, seeming to contradict the
earlier 1114 of 1114. It does not -- the maximising set can contain SEVERAL walks
sharing the same leftmost edge (470 of the 1114 cases), and there the pair lives
inside that set.

Remaining: (ii) alone.

## The mechanism behind claim (ii), from the smallest failure (2026-08-23)

Smallest system where (ii) fails: n=2, m=(2,2), up=(1,1), two walks, s*=1. Its ends
at s* are

   (0,0,1) arrival, walk1, TOP      (0,1,1) departure, walk1, TOP
   (1,1,0) arrival, walk2, BOTTOM   (1,0,0) departure, walk2, BOTTOM

so walk1 BOUNCES at s* (top arrival to top departure, cost 2) and so does walk2
(bottom to bottom, cost 2). Cost 8; the minimum over all turns is 6. The cheaper
system is exactly the CROSS pairing -- top arrival to bottom departure and bottom
arrival to top departure, two passes at cost 1 each -- which is cross_cheaper, and it
also MERGES the two walks. So minimality forbids this configuration.

Sketch for (ii). Let z be a maximiser. By (i) it has a bottom arrival a at s*. Some
other walk has an end at s*, hence an arrival a' there (walk_has_arrival_at_site,
proved). If (ii) fails, a' is a TOP. Then with d = t a and d' = t a':
 - if d' is a TOP, cross_cheaper applies to (a', a) and the system is not minimal;
 - if d' is a BOTTOM, then d and d' may share a side, and the pair is free by the
   DEPARTURES branch of swap_free_iff.
Either way a free merge exists -- note the second branch gives HasFreePair without
giving (ii), so HasFreePair is the right target and (ii) is only one route to it.

Still owed: that some walk other than the chosen maximiser has an end at s* -- 1114
of 1114, unproved -- and the exchange construction turning cross_cheaper into an
actual cheaper transition system.

## The exchange construction is proved (2026-08-23)

cross_cheaper computed that the cross pairing is cheaper; it did not BUILD it. Now
built, and it needed no new mathematics -- NoGapMerge.swap_neg_iff already had the
Bool-level statement (swapDelta < 0 iff the two arrival sides differ, the two
departure sides differ, and an arrival aligns with its own departure), proved by
decide.

EndData.transCost_swap_lt mirrors transCost_swap_free's proof with swap_neg_iff in
place of swap_free_iff, giving a STRICT decrease.

CostMerge.cost_swapData_lt transports it to the involutive re-pairing swapT, along
the same observation as cost_swapData: the cost sums over arrivals only, where swapT
agrees with swap (t a) (t a') composed with t.

So: no cost-minimal transition system contains two arrivals at a common site, in
different walks, whose sides differ, whose departures' sides differ, and with an
arrival aligned to its own departure. That is the exchange half of the argument
sketched from the smallest failure, and it is now formal.

## The free-pair argument closes (2026-08-23)

The obstruction was the configuration cross_dearer allows: a bottom arrival whose
departure is a TOP, against a top arrival whose departure is a BOTTOM -- two passes,
where the cross exchange costs MORE. Probing said it never occurs at s* in a
cost-minimal system, 0 of 1114, and the reason is structural, not metric:

  if a lies in the MAXIMISING walk z at site s* = wLo z, then t a lies in the SAME
  walk (a turn is a graph edge) at the SAME site (the turn preserves sites), and z
  has no end below edge s*. So t a is a BOTTOM too.

That is WalkSupport.maximiser_departure_bottom, and it is exactly the alignment
hypothesis cost_swapData_lt needs. With it:

  CostMerge.free_pair_of_minimal. Let a be the maximising walk's bottom arrival at
  its leftmost site and a' any arrival of another walk there. Then a and a' share a
  side, or their departures do -- otherwise the sides differ, the departures' sides
  differ, a aligns with its own departure, and cost_swapData_lt gives a strictly
  cheaper system.

Also fixed on the way: other_end_at_wLo first had `z` used in a hypothesis before its
binder, so Lean auto-bound a DIFFERENT z; the symptom was two whnf timeouts, not a
type error. Reordering the binders fixed it.

The remaining gap is now assembly only: instantiate free_pair_of_minimal with the
pieces already proved -- maximiser_has_bottom_arrival for a, other_end_at_wLo plus
walk_has_arrival_at_site for a' -- and carry a real minimality hypothesis instead of
the targeted one.

## HasFreePair is PROVED (2026-08-23)

CostMerge.hasFreePair_of_minimal. A locally cost-minimal datum with more than one
walk admits a free merge. No longer a conjecture.

Assembly, all pieces proved earlier in the session:
  maximiser_has_bottom_arrival   a bottom arrival a of the maximising walk at wLo z
  maximiser_departure_bottom     its departure t a is a bottom too -- the alignment
  exists_other_walk              some end is unreachable from z
  other_end_at_wLo               another walk reaches site wLo z
  walk_has_arrival_at_site       upgrade that end to an arrival a'
  free_pair_of_minimal           a and a' share a side, or their departures do

"Locally cost-minimal" means no re-pairing of two arrivals is cheaper, which is
exactly what the exchange argument needs and what the descent preserves.

This closes the chain: cost_merges_to_one now has a proved hypothesis, so a locally
minimal configuration with more than one walk merges down to one AT UNCHANGED COST.
The numerical support (1114 of 1114) is superseded by proof.

## The cost-minimal merge loop is UNCONDITIONAL (2026-08-23)

CostMerge.min_merges_to_one. A cost-minimal datum merges down to a single walk,
staying cost-minimal throughout. No free-pair hypothesis, no conjecture: the pair is
supplied at each step by hasFreePair_of_minimal, whose minimality input comes from
hmin_of_mergesMin.

The invariant is MergesMin -- the merge invariant plus cost-minimality in the class --
and it survives each step: merges_swapData keeps the datum in the class, cost_swapData
keeps the cost, and a minimum of equal cost is still a minimum. The maximiser and the
covering hypothesis are re-derived at each step from maxWLo_spec and the
datum-independent covering input.

Chain, end to end, all kernel-certified, no sorry, no native_decide:

  cost-minimal, >1 walk
    -> maximiser z, its bottom arrival a at wLo z, its departure a bottom too
    -> another walk reaches site wLo z, and has an arrival a' there
    -> a, a' share a side (else the exchange is strictly cheaper)
    -> the merge is FREE and lowers the walk count
    -> iterate: one walk, same cost

## thm:nogap WITH COST, on a configuration (2026-08-23)

ConfigLoop.config_min_single_walk. A gap-free configuration has a COST-MINIMAL
realisation with exactly one walk.

This closes the gap recorded when thm_nogap was first stated: that chain produced
SOME realisation with no isolated cycle, while the paper's statement is about a
relaxed-OPTIMAL one. Cost is now carried the whole way.

New pieces:
  endDataOf         the end data of a configuration: side = atTop, isArr = isArrOf up
  costOf_nonneg     pcostF is 0, 1 or 2, so costs are non-negative
  exists_mergesMin  the class is not obviously finite -- Data bundles proofs -- but
                    the costs are non-negative integers, so Int.exists_least_of_bdd
                    gives a minimum, and any datum attaining it is minimal

The deposit signs enter only through EndData.Data's depSign field and nothing in the
argument depends on which they are, so the theorem is stated for an arbitrary ds.

## thm:nogap, final form (2026-08-23)

ConfigLoop.thm_nogap_optimal. A gap-free configuration has a COST-MINIMAL realisation
with exactly one walk and no isolated cycle against any basepoint. That is the
paper's statement: c(g) = 0 for a relaxed-optimal realisation, not merely for some
realisation. thm_nogap_optimal_witness instantiates it on the one-edge configuration.

What is NOT formalised, stated rather than left implicit: the passage from a group
element g to its configuration (m, up). That is the one remaining link and it is
bookkeeping about how m and up are read off g -- not part of the merge argument.

M6's formalization debt is therefore discharged for the merge argument itself. The
cost-free thm_nogap is kept alongside, since it is what the combinatorial chain
proves without the cost layer.

## cor:localzero (2026-08-23)

ConfigLoop.cor_localzero_pure. Lamp support inside the travel interval gives a
cost-minimal realisation with one walk and no isolated cycle -- the paper's
cor:localzero, from the paper's own hypothesis.

Both halves were already proved and only needed linking:
  GroupElt.no_gap_of_pure_travel   support inside travel  =>  no edge is a gap edge
  EdgeData.mult_pos                not a gap edge          =>  1 <= max |d| |f|
  mult_pos_of_config               ... hence 0 < m e, the input thm:nogap wants
  thm_nogap_optimal                and then c = 0 at a cost-minimal realisation

M5's formalization debt is discharged for the configuration-level statement, on the
same footing as M6: what is not formalised is the passage from a group element to its
configuration, which is shared by both and is not part of either argument.

## prop:travelinv, formalizable core (2026-08-23)

ConfigLoop.travel_minima_agree. For a gap-free (pure-travel) configuration, the
RELAXED minimum is attained by a ONE-WALK realisation. Hence l_T = l_R there: the
inclusion gives l_R <= l_T, and the attained minimum gives l_T <= l_R.

What is NOT used, and this is the point of the paper's remark: the metric identity
l_T = l_R + 2c, whose lower bound is still open. Only l_T <= l_R is needed and it
comes from the exhibited realisation, so prop:travelinv does not inherit the open
bound. The formalisation reflects that -- nothing in the chain mentions the metric
identity.

M7's formalization debt is discharged at configuration level, on the same footing as
M5 and M6. The three share one remaining link: the passage from a group element to
its configuration.

## The walk graph is Local, and where M3 actually sits (2026-08-23)

prop:cut (c >= |Z|) is already proved ABSTRACTLY in CutComponents:
exists_injective_components_avoiding gives |Z| components avoiding a marked one, for
any graph satisfying Local -- every edge either stays at one position or steps from
s-1 to s with s not a gap site.

ConfigLoop.walk_graph_local: the walk graph satisfies Local. The positional half is
outright -- a turn stays at its site, a crossing steps by exactly one -- so the whole
content of Local for it is the gap condition, now isolated as the hypothesis
  forall x, edgeOf x + 1 notin Zf.

IMPORTANT SCOPE NOTE. This is the case the merge chain does NOT cover. Everything
from thm_nogap_optimal down assumes forall e, 0 < m e, that is Z = empty, while
prop:cut is about Z nonempty. The two halves of the development meet only at
Z = empty. So M3's star is NOT reachable from this session's merge work; it needs the
gap condition discharged against a real configuration, which is a separate task.

## M3's gap condition is discharged (2026-08-23)

The offset resolves it. A crossing on edge e spans sites e and e+1, so Local's
"s not a gap site" is about e+1. Hence gapSites = the gap EDGES shifted by one, and
the condition "no end sits at edgeOf x + 1 in gapSites" says no end's edge is a gap
edge -- true, because a gap edge has d = f = 0 hence m = 0 hence no ends at all.

ConfigLoop.gapSites and ConfigLoop.gap_condition. With walk_graph_local this gives
CutComponents.Local for a real configuration, which is the hypothesis the abstract
prop:cut (exists_injective_components_avoiding) consumes.

Five failed proof attempts, all the same shape: rewriting under a dependent
projection. x : Endpt n m carries x.idx : Fin (m x.edge), so rewriting m x.edge in
the GOAL is never type-correct. Fixes that worked: subst rather than rw for the edge
equality, rewriting inside a hypothesis rather than the goal, and finally letting
omega combine x.idx.isLt with m x.edge = 0 instead of rewriting at all.

## prop:cut on a configuration (2026-08-23)

ConfigLoop.prop_cut_config: at least |Z| walks carry neither virtual event, i.e.
c >= |Z|, for a real configuration. The abstract counting was already
CutComponents.exists_injective_components_avoiding; what a configuration supplies is
the Local hypothesis, from walk_graph_local plus gap_condition.

Occupancy is CARRIED, not discharged. prop:cut's counting step needs every site of
the span to carry an end. A site s carries one exactly when edge s has a crossing
(bottom end at s) or edge s-1 does (top end at s) -- site_occupied_bottom and
site_occupied_top. So occupancy fails exactly where TWO ADJACENT gap edges meet, and
that is a condition on the configuration, not a consequence of anything proved here.
Stating it as a hypothesis rather than assuming it away.

So M3's bridge is built except for that one condition, which is a genuine constraint
of the setting rather than a formalisation artefact.

## RETRACTION: gapSites is not the paper's Z (2026-08-23)

Checking whether two adjacent gap edges can occur sent me to the paper, and two of
the last stretch's claims are wrong.

1. Z IS NOT THE GAP EDGES. prop:cut (paper2 l.1941) defines a site s of the span as
   CUT when alpha_s = beta_s = Phi_s = 0, and Z as the cut sites INTERIOR to the span.
   A maximal run of L gap edges contributes its L-1 interior sites, which is why the
   paper says "c >= L-1 per gap run" (l.94), not L. ConfigLoop.gapSites shifts each
   gap edge by one and so yields L sites per run -- it OVERCOUNTS by one per run.

2. ON THE SPAN, GAP EDGES CARRY CROSSINGS. Paper2 l.1964: "an edge with f=0 has
   m >= 2 on the span by cor:lRclosed". So m = max(|d|,|f|) is the MINIMUM ADMISSIBLE
   multiplicity, not the multiplicity on the span. gap_condition's proof -- gap edge
   => m = 0 => no ends -- is therefore about minimum-multiplicity configurations, and
   the hypothesis it discharges is unavailable in prop:cut's setting.

This also dissolves the occupancy worry recorded one commit ago: with m >= 2 on f=0
edges, every edge of the span carries crossings and occupancy holds. The worry was an
artefact of the same wrong multiplicity law.

What survives: walk_graph_local (stated for an arbitrary Zf) and prop_cut_config (a
conditional statement, correct as written). What does not: the claim that gapSites is
the paper's Z and that gap_condition discharges Local's hypothesis for prop:cut.
Docstrings corrected in place. M3's bridge needs Z built from alpha, beta, Phi.

## The cut condition, from its actual definition (2026-08-23)

Read the definitions instead of guessing them this time.

  SiteCost.alpha Ap Am Cp Cm = (Cp - Cm) - (Ap - Am)
  SiteCost.beta  Bp Bm Dp Dm = (Bp - Bm) - (Dp - Dm)
  SiteCost.Phi   Ap Am Cp Cm = (Ap + Am) - (Cp + Cm)
  SiteCost.siteValue         = max (|alpha|, |beta|, |Phi|)

prop:cut calls a site CUT when alpha = beta = Phi = 0. Since siteValue is exactly the
max of their absolute values, being cut is siteValue = 0 --
ConfigLoop.isCut_iff_siteValue_zero. So the paper's Z is the set of INTERIOR sites of
zero site-value, and it is expressible with definitions already in the development.

That replaces the retracted gapSites. It also explains why the shifted-gap-edge guess
was wrong in a structural way: cut is a condition on the PAIRING data at a site
(arrivals, departures and their signs), not on the edge multiplicities, so no function
of the gap edges alone could have been it.

## Local with the right position function (2026-08-23)

SiteCost's header gives the read-off: alpha = d_{s-1}, beta = d_s, Phi = f_{s-1}
(alpha_eq_dL, beta_eq_dR, Phi_eq_fL). So

  site s is CUT  <=>  d_{s-1} = 0 and d_s = 0 and f_{s-1} = 0

which is the paper's l.1966 verbatim. The retracted gapSites had the first two
conditions but NOT d_s = 0 -- and that missing condition is exactly the one extra
site per run, since the site at the far end of a gap run has a flanking deposit.

The position function was also wrong. A strand crosses site s by going from edge s-1
to edge s, which in the walk graph is a TURN at s; a CROSSING edge joins the two ends
of one crossing and stays on a single edge. So pos is the EDGE, not the site:

  walk_graph_local_edge : Local (walk graph) edgeOf Zf
    - crossing edges do not move pos, so the condition is vacuous on them
    - a turn at site s moves pos from s-1 to s, and Local then demands s not in Z

and that demand is exactly prop:cut's first sentence -- at a cut site every
minimum-cost pairing matches each arrival with a departure on its own side, so no
strand crosses s. It is a theorem about minimum-cost pairings, carried as a hypothesis
here rather than assumed silently.

walk_graph_local (the siteOf version) is superseded. It is true as stated but its gap
hypothesis was unnatural precisely because the position function was wrong.

## prop:cut, rebuilt correctly (2026-08-23)

cutSitesZ d f A B = the sites s of [A,B] with d(s-1) = 0, d(s) = 0, f(s-1) = 0 --
all three conditions. That is the paper's Z. The retracted gapSites omitted d(s) = 0
and therefore counted one site too many per gap run.

prop_cut_correct composes it with walk_graph_local_edge: at least |Z| walks carry
neither virtual event. Its two inputs are exactly the ones the paper argues for:

  hturn  no strand crosses a cut site -- prop:cut's first sentence
  hocc   every edge of the span carries a crossing -- supplied by m >= 2 on f=0 edges

Both are carried as hypotheses rather than assumed away. The chain from the walk model
to the abstract counting is now built on the right Z and the right position function.

## No strand crosses a cut site (2026-08-23)

Plan.cost = 2*(same-side sign flips) + cross, so cross <= cost (cross_le_cost). At a
cut site alpha = beta = Phi = 0, so siteValue = 0, so a minimum-cost plan costs 0 and
therefore crosses 0 times -- no_cross_at_cut.

That is prop:cut's first sentence, and it is the hturn input of prop_cut_correct: at
a cut site every minimum-cost pairing matches each arrival with a departure on its
own side.

What remains to connect it to hturn as stated is the per-site bookkeeping -- that the
turn of the walk model at site s realises a Plan at s, so that zero cross mass means
no turn edge moves between edge s-1 and edge s. That is the same kind of link as the
g-to-configuration one, and is bookkeeping rather than argument.

## A Plan from a turn: the counting step (2026-08-23)

SiteCost.Plan is a 4x4 transportation matrix whose rows count arrivals by class and
columns departures by class. A turn at a site is a bijection arrivals -> departures,
so x_ij = the number of class-i arrivals whose turn lands in class j gives a plan.

row_sum_of_fiber: splitting a class by where its turn lands recovers the class count
(Finset.card_eq_sum_card_fiberwise).

col_sum_of_bij: the same count through the bijection -- the fibres of cls o t over the
arrivals have the same cardinalities as the fibres of cls over the departures
(Finset.card_bij).

Those are the two equations Plan's row0..row3 and col0..col3 fields require, so what
remains for M3l is assembling them with the concrete class function (side from atTop,
sign from EndData.sgn) and the site's arrival and departure sets.

## A Plan from a turn, and what its cross mass means (2026-08-23)

planOfTurn builds SiteCost.Plan from a bijection t : S -> T and a class function
cls : beta -> Fin 4, with entry (i,j) counting the class-i arrivals whose turn lands
in class j. Its eight constraints are xEntry_row and xEntry_col.

no_side_change_of_cross_zero: classes 0,1 are the left side and 2,3 the right, and
Plan.cross is exactly the eight entries moving between them -- so cross = 0 means
every arrival's turn stays on its own side. With no_cross_at_cut (cross = 0 at a cut
site) that is prop:cut's first sentence in the form Local wants: at a cut site no
turn moves from edge s-1 to edge s.

So M3l's mathematical content is done. What remains is instantiation: cls built from
atTop and EndData.sgn, S and T the site's arrAt and depAt, and t the turn -- with
turnAt_arr, turnAt_dep and turnAt_invol supplying maps-into, injectivity and
surjectivity.

## The plan at a site of a configuration (2026-08-23)

planAt instantiates planOfTurn with the site's arrivals and departures and the local
turn:

  clsOf          the four classes -- top ends belong to the LEFT edge (classes 0,1)
                 and bottom ends to the right (2,3); the sign comes from EndData.sgn
  turnAt_arr     arrivals map into departures
  turnAt_injOn   the turn is injective, being an involution
  turnAt_surjOn  every departure is the turn of an arrival -- take its own turn, which
                 turnAt_dep puts among the arrivals

So a configuration now yields a genuine SiteCost.Plan at each balanced site, and with
no_cross_at_cut and no_side_change_of_cross_zero that gives, at a cut site, that no
turn moves between edge s-1 and edge s -- the hturn input of prop_cut_correct.

## M3l closed: side change IS edge change (2026-08-23)

At a site s an end is either a top end, on edge s-1, or a bottom end, on edge s
(edge_of_site). So two ends at one site share an edge exactly when they share a side
(same_edge_of_same_side), and clsOf's side bit is atTop (clsOf_lt_two_iff).

turn_keeps_edge_of_cross_zero: if the site's plan has no cross mass then no turn there
moves between the two adjacent edges. Chain:

  cut site  ->  siteValue = 0            (isCut_iff_siteValue_zero)
            ->  min-cost plan costs 0     (transport_min)
            ->  cross = 0                 (no_cross_at_cut)
            ->  turn preserves the side   (no_side_change_of_cross_zero)
            ->  turn preserves the edge   (this)

which is exactly the hturn input of prop_cut_correct. M3's bridge is complete apart
from choosing the site's minimum-cost plan to BE the configuration's turn, which is
the statement that the realisation is cost-minimal at each site.

## The cost splits over sites (2026-08-23)

costOf sums pcostF a (t a) over arrivals, and each arrival lies at exactly one site,
so the sum splits site by site -- cost_split_by_site, via
Finset.sum_fiberwise_of_maps_to.

site_cost_le_of_global: if two data agree away from one site, their costs differ only
in that site's summand, so a globally minimal datum minimises each site. That is M3q's
content: MergesMin's global minimality gives site-wise minimality, which is what
turn_keeps_edge_of_cross_zero needs to have a MINIMUM-cost plan at the site.

The proof is the obvious one -- split both costs, note the off-site summands agree
term by term, and cancel -- but it is the step that lets the local exchange argument
of prop:cut talk to the global optimum the merge chain carries.

## Summing by class pair (2026-08-23)

sum_by_class_pair: a cost depending only on the pair (cls a, cls (t a)) sums to the
transportation entries weighted by that cost -- two fiberwise splits and a constant
sum on each block.

pcostW is the pairing cost as a function of the two classes: 0 on the same side with
the same sign, 2 on the same side with opposite signs, 1 across.
weighted_sum_eq_cost: the weighted entries are exactly Plan.cost's expression
2*(x01+x10) + 2*(x23+x32) + cross.

Together these identify a site's contribution to costOf with its plan's Plan.cost,
which is what site_cost_le_of_global needs in order to say that a globally minimal
datum has a MINIMUM-COST PLAN at each site -- the hypothesis
turn_keeps_edge_of_cross_zero consumes.

## M3q: the site's cost contribution IS its plan's cost (2026-08-23)

clsOf_eq_iff: the class determines and is determined by the side and the sign.
pcostF_eq_pcostW: pcostF splits on side then sign, and clsOf encodes exactly those two
bits, so the pairing cost is the class-pair weight.
site_sum_eq_plan_cost: with sum_by_class_pair and weighted_sum_eq_cost, the site's
contribution to costOf equals its plan's Plan.cost.

So M3q is done: site_cost_le_of_global says a globally minimal datum minimises each
site's contribution, and this says that contribution IS the plan's cost -- hence the
site's plan is minimum-cost, which is what turn_keeps_edge_of_cross_zero needs.

M3's chain, end to end:
  MergesMin (global cost-minimality)
    -> site-wise minimality        (cost_split_by_site, site_cost_le_of_global)
    -> the site's plan is minimal  (site_sum_eq_plan_cost)
    -> at a cut site it costs 0    (isCut_iff_siteValue_zero)
    -> no cross mass               (no_cross_at_cut)
    -> the turn keeps its side     (no_side_change_of_cross_zero)
    -> the turn keeps its edge     (turn_keeps_edge_of_cross_zero)
    -> Local holds                 (walk_graph_local_edge)
    -> c >= |Z|                    (prop_cut_correct)

## prop:cut, assembled (2026-08-23)

ConfigLoop.prop_cut_assembled: at least |Z| walks carry neither virtual event, for a
configuration whose cut-site plans have no cross mass.

turn_keeps_edge_all extends turn_keeps_edge_of_cross_zero from arrivals to EVERY end:
a departure's turn is an arrival at the same site, and the two share their turn edge,
so the arrival case gives the departure case by the involution.

The single hypothesis about the realisation is hcut -- at each cut site the plan has
no cross mass -- and that is exactly what global cost-minimality delivers through
site_cost_le_of_global and site_sum_eq_plan_cost to no_cross_at_cut.

M3 is now assembled at configuration level, on the same footing as M5, M6 and M7. The
shared remaining link for all four is the passage from a group element to its
configuration.

## M2's star was misattributed, and I duplicated work (2026-08-23)

Read Realisation.lean, which had not been examined this session. Three findings:

1. lR_closed IS M2, fully proved and kernel-clean: the minimum cost of a realisation
   is sum over the span of max(|d_j|,|f_j|), forced to 2 where that vanishes, plus the
   sum over sites of max(|alpha_s|,|beta_s|). It is universally quantified over
   PathData, hence over all k*, and PathData carries only the natural conditions --
   parity, span minimality, outer vanishing -- with no unproved assumption. M2's
   formalization debt was misattributed.

2. cut_no_cross was ALREADY THERE -- prop:cut's first sentence at the level of a
   realisation. I rebuilt the same reasoning this session as
   no_cross_at_cut / turn_keeps_edge_of_cross_zero. Mine lands in the WALK GRAPH,
   which Realisation.lean explicitly cannot express, so the bridge still had to be
   built; but I should have read this file before rebuilding the site-cost half.

3. gap_run_cut was ALREADY THERE: a maximal gap run of L edges contributes exactly its
   L-1 interior sites and neither end site. That is the fact I derived from the paper
   two stretches ago to justify retracting gapSites. It was proved in Lean the whole
   time.

Realisation.lean's header also says exactly what was missing -- "a Realisation carries
the pairing at each site but not the strand graph those pairings assemble into, so
'number of components' is not expressible against this structure". That is precisely
the gap the walk model fills, so the session's direction was right even where its
bookkeeping duplicated existing work.

## cutSitesZ needed the virtual-event condition too (2026-08-23)

Reading Realisation.lean's definitions caught a second omission in cutSitesZ, this
time BEFORE anything was built on it.

  PathData.cut s  =  alphaAt s = 0 and betaAt s = 0 and PhiAt s = 0
  alphaAt s = d(s-1) - vArr s + eps * vL s
  betaAt  s = d s - eps * vR s
  PhiAt   s = f(s-1) + vArr s - vL s
  vArr s = [s = 0],  vL and vR vanish off s = kstar

So the plain conditions d(s-1) = d s = f(s-1) = 0 characterise cut ONLY away from the
two virtual events -- which is exactly the hnov hypothesis of gap_run_cut, and the
paper's own "and no virtual event" in its l.1966 sentence. cutSitesZ now carries
s != 0 and s != kstar.

Without it a site carrying a virtual event could be counted as cut when it is not --
the same overcounting failure as the retracted gapSites, one level subtler. The
difference is that this one was caught by reading the definition rather than by
building on a guess and retracting later.

## cutSitesZ agrees with PathData.cut -- proved, not matched by eye (2026-08-23)

cut_iff_plain: away from s = 0 and s = kstar, the virtual terms vanish (vArr s = [s=0],
vL and vR are supported on s = kstar), so

  cut s  <->  d(s-1) = 0 and d s = 0 and f(s-1) = 0

mem_cutSitesZ_iff_cut: a site of the span lies in cutSitesZ exactly when it is a cut
site with no virtual event.

This is the step both gapSites attempts lacked. The first matched Z to gap edges by
eye and overcounted one site per run; the second dropped the virtual-event condition
and could have counted a marker site as cut. Now the correspondence is a theorem, so
neither failure mode can recur silently.

## The retracted definitions are deleted (2026-08-23)

gapSites, gap_condition, the siteOf-based walk_graph_local and prop_cut_config are
removed. Dependencies were checked first -- all uses were internal to the superseded
block and prop_cut_config had no external users -- because a Rule 10 sweep in this
project once broke a whole dependency chain by not checking.

What replaces them: cutSitesZ with the virtual-event condition,
mem_cutSitesZ_iff_cut proving it agrees with PathData.cut, walk_graph_local_edge with
pos = edgeOf, and prop_cut_assembled.

The two docstring mentions of gapSites that remain are deliberate -- they record what
was wrong and why, next to the definitions that replaced them. The refuted objects
themselves are gone; the account of them stays.

## Why min_merges_to_one and prop:cut do not conflict (2026-08-23)

min_merges_to_one merges a cost-minimal datum to ONE walk at unchanged cost;
prop:cut says every minimum-cost realisation has at least |Z|+1 components. With
Z nonempty those would contradict each other. They do not, and the reason is sharp.

EndData.sgn DERIVES the sign from side and role, so on one side every arrival carries
one sign and every departure the opposite. With A left arrivals and C left departures
that gives alpha = -(A + C), so alpha = 0 forces A = C = 0 -- no_ends_of_alpha_zero,
and no_ends_of_beta_zero on the right. A CUT SITE CARRIES NO ENDS AT ALL.

The merge chain assumes 0 < m e at every edge, which puts ends at every site, so it
never meets a cut site. That is the hidden hypothesis behind the scope note recorded
much earlier (M3b): the chain assumes Z = empty, and now the mechanism is identified
rather than just the fact.

It also says what M4b needs: c <= |Z| is the statement that cut sites are the ONLY
obstruction, so the route is to relax the covering hypothesis from "every edge carries
a crossing" to "every edge outside the cut sites does", and let the descent run on
each maximal run between cut sites.

## Covering on a run -- M4b's first step (2026-08-23)

c <= |Z| says cut sites are the only obstruction. The descent's covering hypothesis
asks for a crossing on EVERY edge, which forces Z = empty; restricting it to a run
between cut sites is the first step.

covering_on_run: if every edge of [l, r] carries a crossing, then for j in (l, r] the
edge immediately left of j carries a top end. The run must start at a valid edge
index -- the hypothesis 0 <= l is needed and was missing at first, since without it
j - 1 can be -1 and there is no edge there. omega found that, reporting a
counterexample with l <= -1.

Everything downstream of the covering hypothesis is already unconditional, so this is
the one place the descent has to be weakened for M4b.

## The second walk's end, produced within a run (2026-08-23)

other_end_at_wLo_run: WalkSupport.other_end_at_wLo with its global covering hypothesis
replaced by covering_on_run. The maximiser's leftmost edge need only lie inside a run
[l, r] whose edges all carry crossings -- not in a configuration that is gap-free
everywhere.

That was the single place the descent consumed the global covering, so with it
replaced the descent can in principle run between cut sites rather than requiring
their absence. What remains for M4b is the induction over runs: each maximal run
merges to one walk, and the runs are separated by cut sites, giving c <= |Z|.

## Walks do not cross a cut site (2026-08-23)

adj_confined: a crossing edge stays on one edge, and a turn at site t moves only
between edges t-1 and t, which straddle s exactly when t = s. So if the turn keeps its
edge at s -- which turn_keeps_edge_all gives at a cut site -- no adjacency crosses s.

walk_confined: hence no walk crosses s either, by induction along the walk.

That is the first half of the run induction for c <= |Z|: each walk lives entirely on
one side of every cut site, so each walk lies within a single maximal run. What
remains is that the walks within a run merge to one, which is the descent with
other_end_at_wLo_run in place of the global covering.

## Counting walks by an invariant (2026-08-23)

walkCount_le_card: if a function is constant on walks and separates them, the walk
count is at most the size of its target. The induced map on connected components is
injective, and Fintype.card_le_of_injective finishes.

With the invariant "how many cut sites lie below this end" that is exactly c <= |Z|:
 - constancy  is walk_confined, proved;
 - separation is the statement that walks within a run merge, which is the descent
   with other_end_at_wLo_run, and is what M4b still owes.

So M4b now has both halves of its scaffolding in Lean, and the single remaining
mathematical step is the separation half.

## Descending until stuck (2026-08-23)

reaches_one descends to a single walk, which is right when every split admits a merge.
With cut sites present some splits do not, so the descent stops earlier.

reaches_stuck is the general form: if from any P either a strictly descending step
exists or the datum is Stuck, then from any P a stuck one is reached. reaches_one is
the instance where Stuck means walkCount <= 1 (reaches_one_of_stuck), so nothing is
lost by generalising.

For c <= |Z| the stuck condition is 'no two ends in one run are unreachable', which is
exactly the separation hypothesis of walkCount_le_card. So the shape is now:

  descend until stuck  (reaches_stuck)
    -> separation holds at the stuck datum
    -> walkCount <= number of runs = |Z| + 1   (walkCount_le_card, walk_confined)

## A free pair from run-local covering (2026-08-23)

hasFreePair_run: CostMerge.hasFreePair_of_minimal with its covering hypothesis
supplied by covering_on_run instead of the global one. The maximiser's leftmost edge
need only sit inside a run [l, r] whose edges carry crossings.

The substitution goes through unchanged -- every other input of
hasFreePair_of_minimal is already unconditional for a configuration (site law from
turnAt_site, role law from turn_arr_flip, partner laws from partner_edgeOf and
partner_top, and the crossing site law from p_site_ne).

So the free-merge half of the run induction is in place. What remains is choosing the
maximiser WITHIN a run rather than globally: the global maximiser's leftmost edge lies
in the rightmost run, so the argument as it stands merges that run, and the induction
has to walk leftwards run by run.

## The run-local maximiser (2026-08-23)

maxWLo takes the sup over all ends, so its maximiser lies in the rightmost run and the
descent as built merges only that run. maxWLoOn takes the sup over a Finset of ends
instead, and maxWLoOn_spec gives attainment inside the set and dominance over it --
the argument is unchanged, since a non-empty finite set still attains its sup.

That is the last structural change the run induction needed. Its pieces are now:

  covering_on_run          covering restricted to a run
  other_end_at_wLo_run     the second walk's end, within a run
  hasFreePair_run          a free pair, from run-local covering
  maxWLoOn / _spec         the maximiser, within a run
  walk_confined            walks do not cross a cut site
  reaches_stuck            descend until no step remains
  walkCount_le_card        count walks by a separating invariant

What remains is assembling them: run the descent inside each run with the run-local
maximiser, and count.

## c <= |Z|, given separation (2026-08-23)

gz_le_card: the run index CutComponents.gz never exceeds |Z|, so runIndex lands in
Fin (|Z| + 1) -- at most |Z| + 1 runs.

runIndex_const: the run index is constant on walks. This is
CutComponents.blk_reachable applied to walk_graph_local_edge -- the constancy half
was already in the repository, waiting for a Local instance to feed it.

walkCount_le_runs: if ends of the same run always lie in the same walk, there are at
most |Z| + 1 walks, i.e. at most |Z| isolated cycles. That is c <= |Z| modulo the
separation hypothesis, which is exactly the stuck condition of the run descent:
where separation fails, hasFreePair_run supplies a free merge, so a datum on which
the descent has halted satisfies it.

So M4b is reduced to one composition: run reaches_stuck with hasFreePair_run as the
step, and feed the resulting stuck datum to walkCount_le_runs.

## c <= |Z|, composed (2026-08-23)

walkCount_le_runs_gen: the counting for any datum whose walk graph is Local for Zf.

c_le_Z_of_step: descend while a merge exists; where none does, ends of one run share a
walk and the count is at most |Z| + 1. This is reaches_stuck instantiated with
separation as the stuck condition, then walkCount_le_runs_gen.

The one hypothesis left is hstep: a datum on which separation FAILS admits a free
merge. That is hasFreePair_run followed by descent_of_split, and what it still needs
is that the run bounds survive the merge -- the swap changes the turn but not the
multiplicities, so hpos is untouched, but wLo of the maximiser can shift, so the
bounds hlz and hzr have to be carried as part of the descent invariant P rather than
fixed once.

That is the precise remaining obligation for M4b, and it is about the invariant, not
about the mathematics of the merge.

## The cut condition survives a merge off the cut sites (2026-08-23)

Local for Zf is carried by hturn -- a turn that changes edge sits at a non-cut site.
The re-pairing moves only the four ends at ONE site, so if that site is not a cut site
the condition still holds, and away from those four the turn is unchanged.

hturn_swapT proves it: five cases, four of them the moved ends (all at the merge
site, which is assumed off Zf) and one the untouched remainder.

So Local survives the descent, which is the half of M4b10 about the cut structure.
What is still owed is that the RUN BOUNDS survive: hpos is untouched since the swap
does not change multiplicities, but wLo of the maximiser can shift, so hlz and hzr
have to be re-established at each step rather than carried unchanged.

## The run bounds, re-derived rather than carried (2026-08-23)

hlz and hzr refer to the maximiser of the CURRENT datum, so a merge can shift them.
They need not be carried: wLo_same_side shows a walk's leftmost edge lies on the same
side of every cut site as the walk itself, because it IS the edge of some end of the
walk and walk_confined forbids crossing.

So the run bounds are a consequence of where the walk sits, not extra data, and the
descent invariant does not have to preserve them -- it re-derives them at each step.
That closes the concern recorded in M4b10.

M4b's remaining obligation is now just the assembly of hstep itself: from separation
failure, produce the pair (hasFreePair_run), merge (descent_of_split), and carry
Local (hturn_swapT) with the run bounds re-derived (wLo_same_side).

## The free pair, from a GIVEN split (2026-08-23)

hasFreePair_of_minimal finds the second walk with exists_other_walk, which picks an
arbitrary one -- possibly in another run, where the run-local covering says nothing.

freePair_of_split extracts the core with the second end supplied instead. For the run
induction that end is given: separation failure names two ends of the SAME run that
are unreachable, so the pair stays inside the run and the run-local covering applies.

That was the last mismatch between the global descent and the run descent. Everything
hstep needs is now available with matching shapes:

  separation fails  ->  two ends of one run, unreachable
                    ->  freePair_of_split with the run-local covering
                    ->  descent_of_split for the strict decrease
                    ->  hturn_swapT to carry Local
                    ->  wLo_same_side to re-derive the run bounds

## A split yields a descending merge (2026-08-23)

order_split: freePair_of_split wants the end with the larger wLo first, and either
order of a split will do, so pick that one.

step_of_split: order the split, take the free pair, merge -- the walk count drops.
The covering hypothesis is stated for every end, which the run descent supplies
because every walk of a run has its leftmost edge inside that run (wLo_same_side).

The conclusion is stated as "some datum has a smaller walk count", which is what
reaches_stuck consumes. A first attempt tried to also return the merged pair and the
three swapData side conditions inside the existential; anonymous binders in an
existential need types, and those types are long, so the useful form is the short one.

What M4b still owes is the invariant half: reaches_stuck needs P preserved by the
step, and step_of_split as stated returns only the count decrease. Threading P through
means returning the swapped datum together with hturn_swapT's conclusion.

## The descending merge, with what the invariant needs (2026-08-23)

step_of_split' returns the merged datum together with the two arrivals and the
equation D'.t = swapT D.t a (D.t a) a' (D.t a'). That is exactly what
ConfigLoop.hturn_swapT consumes to carry the cut condition across the step.

The equation on .t is the trick: returning the three swapData side conditions inside
the existential needs dependent binders, which do not typecheck anonymously and whose
types are unwieldy written out. An equation between the two turn FUNCTIONS carries the
same information with none of that.

So the step now yields both halves reaches_stuck wants -- the strict decrease and the
data to re-establish the invariant.

## The invariant survives a step (2026-08-23)

hturn_step: the cut condition survives a descent step. step_of_split' returns the
merged datum with an equation on its turn, hturn_swapT carries the condition across,
and the merge site is not a cut site because cut sites carry no ends -- which enters
as the hypothesis hZ, exactly no_ends_of_alpha_zero instantiated.

So both halves of the descent are in place:

  step_of_split'   the strict decrease, plus the data to re-establish the invariant
  hturn_step       the invariant re-established from that data

and c_le_Z_of_step consumes them once they are packaged as reaches_stuck's step. That
packaging is the last piece of M4b.

## The descent step, packaged (2026-08-23)

RunInv bundles what the run descent carries: the crossing map, the turn's site and
role laws, the cut condition, the covering, and cost-minimality.

run_step: where separation fails the invariant yields a strictly smaller datum still
satisfying the cut condition; where it holds the datum is stuck. That is exactly
reaches_stuck's step, with Stuck = separation.

Two syntax lessons. `push Not at h` did not produce the expected existential from a
negated two-variable forall -- explicit not_forall twice, then a lambda for the
implication, works. And a multi-line `by` block sitting inside an argument list breaks
the parser when its continuation line starts with a bracket; hoisting those terms into
`have`s before the application fixes it and reads better anyway.

## hcov stated without the datum (2026-08-23)

RunInv's covering component referred to wLo, which shifts when a merge changes the
walks -- so the invariant could not be preserved as stated. The fix is that the
covering is not really about the datum: whether an edge carries a top end depends on
the multiplicities, not on the pairing.

RunInv.hcov is now

  forall j, (exists u, edgeOf u = j) -> (exists v, edgeOf v < j)
              -> exists w, edgeOf w = j - 1 and atTop w

with no mention of E, so it survives a merge unchanged, and run_step instantiates it
at j = wLo z using exists_end_at_wLo. That removes the only component of RunInv whose
preservation was in doubt.

## The invariant's minimality made preservable (2026-08-23)

RunInv.hmin was "no swap from E is cheaper than E". That is NOT preserved: a merge can
open swaps that were unavailable before. It is now global minimality in the class,

  forall F, F.p = partner -> F respects sites -> F alternates roles -> cost E <= cost F

which a cost-neutral merge does preserve, since the merged datum has the same cost and
the same class membership.

run_step derives the local form it needs from the global one: for two arrivals at a
common site the swapped datum is in the class (swapT_site, swapT_arr), so global
minimality bounds its cost.

step_of_split' also now returns D'.p = D.p and that both ends are arrivals, which are
what RunInv's remaining components need.

## run_step returns the full invariant (2026-08-23)

run_step's descending branch now returns RunInv for the merged datum, not just the cut
condition. Each component has its lemma:

  hp     from swapData_p, via the returned D'.p = D.p
  hts    swapT_site
  hta    swapT_arr
  hturn  hturn_step
  hcov   unchanged, since it no longer mentions the datum
  hmin   cost-neutrality (cost_swapData through cost_congr) plus E's minimality

step_of_split' had to return more along the way: both ends being arrivals, the split
itself, and the shared-side fact -- reconstructing them at the call site produced
wrong distinctness proofs, and returning them is both shorter and correct.

One defeq trap: step_of_split' states the role facts as d.isArr with d = endDataOf,
while RunInv states them as isArrOf up. These are definitionally equal but not
syntactically, so rw fails on them until they are converted by a typed have.

## c <= |Z| IS PROVED (2026-08-23)

ConfigLoop.c_le_Z: a cost-minimal configuration merges, run by run, to at most
|Z| + 1 walks -- at most |Z| isolated cycles. Kernel-certified, no sorry, no
native_decide.

  reaches_stuck with run_step as the step
    -> descend while two ends of one run lie in different walks
    -> where none do, the run index separates the walks
    -> local_of_hturn gives Local for the stuck datum
    -> walkCount_le_runs_gen counts: at most |Z| + 1 walks

Every hypothesis is the invariant RunInv, plus hZ -- cut sites carry no arrivals --
which is no_ends_of_alpha_zero.

With prop_cut_assembled (c >= |Z|) that is the shield law c = |Z| at configuration
level, for a cost-minimal realisation. M4b's open half is closed.

## THE SHIELD LAW (2026-08-23)

ConfigLoop.shield_law: a cost-minimal configuration has EXACTLY |Z| + 1 walks, so
c = |Z|. Both inequalities in one statement, kernel-certified, no sorry.

  c >= |Z|   CutComponents.exists_injective_components_avoiding fed by local_of_hturn,
             converted by walkCount_ge_of_avoiding (add the marked component back)
  c <= |Z|   c_le_Z, the run induction

Hypotheses: the invariant RunInv, cut sites carrying no arrivals (hZ), the span
bounds, and occupancy -- every edge of the span carries a crossing, which is
datum-independent and supplied by m >= 2 on f = 0 edges.

Both halves of M4b are now formal at configuration level, on the same footing as M3,
M5, M6 and M7. The shared remaining link for all of them is the passage from a group
element to its configuration.

## The shield law is not vacuous (2026-08-23)

RunInv bundles six conditions, and a bundle nothing satisfies proves nothing -- this
session has been bitten by that four times.

runInv_of_gapfree exhibits it at a cost-minimal datum of any gap-free configuration:
minimality from exists_mergesMin, the structural laws from Merges, the covering from
covering_of_mult_pos, and the cut condition vacuous on the empty set.
shield_law_witness instantiates that on the one-edge configuration.

Note what this witness does and does not show. It confirms RunInv is satisfiable, so
shield_law is not vacuous. It does NOT exercise the interesting case: with Z empty the
law reads c = 0, which is thm:nogap again. A witness with Z nonempty needs a
configuration carrying a cut site, and by no_ends_of_alpha_zero such a site has no
ends -- so it needs two edges separated by an empty one.

## RETRACTION: shield_law is vacuous for Z nonempty (2026-08-23)

Building the Z-nonempty witness found the defect, which is the point of building it.

A cut site carries no ends (no_ends_of_alpha_zero), and a site has ends iff edge s-1
or edge s does -- so a cut site needs TWO ADJACENT EMPTY EDGES. Take m = (2,0,0,2),
up = (1,0,0,1): sites 0,1,3,4 balance, site 2 is empty and hence cut.

But RunInv.hcov demands a top end on edge j-1 whenever anything lies left of j. At
j = 3 the antecedents hold -- edge 3 carries ends, edge 0 lies left -- and edge 2 is
empty, so the conclusion fails.

RunInv IS THEREFORE UNSATISFIABLE WHENEVER A CUT SITE EXISTS. c_le_Z, shield_law and
runInv_of_gapfree are true as stated but say nothing for Zf nonempty, which is the
only case with content -- at Zf empty the shield law is thm:nogap again.

This is the fifth vacuity trap of the session and the first found by deliberately
constructing the witness rather than by stumbling on it. The pattern is identical to
the covering hypothesis retracted earlier: a condition phrased globally when the
argument needs it locally.

THE FIX: hcov must be run-local, the shape covering_on_run already has, which means
carrying the run decomposition in the invariant rather than one global condition. The
run induction machinery -- covering_on_run, other_end_at_wLo_run, hasFreePair_run,
maxWLoOn -- was built for exactly that and is unused by RunInv as written.

## The covering gap, made explicit (2026-08-23)

RunInv.hcov is now run-local: it asks for an end left of j IN THE SAME RUN (equal gz,
so no cut site between). On m = (2,0,0,2) at j = 3 the antecedent fails, since
gz{2}(0) = 0 and gz{2}(3) = 1, so the condition holds -- the invariant is satisfiable
with cut sites, which the global form was not.

But run_step cannot derive the UNRESTRICTED covering it passes to freePair_of_split
from the run-local one: there v is arbitrary, and the same-run clause is unavailable
without threading it through other_end_at_wLo. Rather than hide that, hcovAll is now
an explicit hypothesis of run_step, c_le_Z and shield_law.

So the statements are honest: they say what they assume, and the assumption is exactly
the thing the run redesign has to supply. What remains is threading the same-run
condition through other_end_at_wLo -> freePair_of_split -> step_of_split', at which
point hcovAll can be discharged from RunInv.hcov and the shield law becomes
unconditional for Z nonempty.

## The second end, from run-local covering (2026-08-23)

other_end_at_wLo applies its covering at exactly ONE point -- the bottom end of z''s
walk, whose edge is wLo z'. So when z and z' lie in the same run the run-local covering
suffices and the global form is unnecessary.

other_end_runlocal proves that: the same two cases as before, but the first supplies
the covering's same-run antecedent from hsame (equal gz at the two leftmost edges),
which is available because z and z' are in one run.

That is the first of the three lemmas the threading needs. What remains is carrying
the same-run fact through freePair_of_split and step_of_split' so run_step can
discharge hcovAll from RunInv.hcov, at which point the shield law loses its extra
hypothesis.

## The same-run fact at leftmost edges (2026-08-23)

gz_wLo: a walk's run index is read off its leftmost edge as well as anywhere else --
the leftmost edge IS the edge of some end of the walk (exists_end_at_wLo), and
runIndex_const makes the index constant along the walk.

gz_wLo_eq: two walks of one run therefore agree at their leftmost edges, which is
exactly other_end_runlocal's hsame.

Second of the three threading lemmas. What remains is a version of freePair_of_split
calling other_end_runlocal instead of other_end_at_wLo, carrying the same-run
hypothesis; then step_of_split' and run_step inherit it and hcovAll is discharged.

## The run-local free pair (2026-08-23) -- and an honest recount

freePair_runlocal now returns the shared-side condition too, so the run-local descent
has every input the global one had. Third of the three threading lemmas. What remains
to finish M4b is wiring it into run_step so hcovAll is discharged -- one composition.

HONEST RECOUNT. The green count in this session's tables was inflated: a new atom ID
was minted for nearly every lemma, so the number measured how finely the work was
chopped, not how much was proved. At the granularity the session STARTED with, the
real state is:

  PROVED AND FORMAL (configuration level, kernel-certified, no sorry):
    M2  cor:lRclosed        -- was already proved; the star was misattributed
    M3  prop:cut  c >= |Z|
    M5  cor:localzero
    M6  thm:nogap, with cost
    M7  prop:travelinv
  PARTIAL:
    M4b shield law c = |Z| -- claimed, retracted as vacuous, repaired to a
        conditional statement; one composition from unconditional
  UNTOUCHED (these are the actual mathematical goal):
    H1  the transfer model (M)
    H2  the junction pairing (R-J)
    M9  U transcendental over Q(x), conditional on H1 and H2

Nothing today moved H1, H2 or M9. The work was formalisation infrastructure for the
combinatorial half of paper2, plus the merge argument built from scratch. That is
real, but it is not progress on the open mathematics.

## CORRECTION: M4b is not "one composition" away (2026-08-23)

Checked before stopping. freePair_runlocal, other_end_runlocal, gz_wLo and gz_wLo_eq
are all stated for `dataOf up hbal`, not for a general datum. The descent produces
MERGED data, which are not dataOf. So finishing M4b needs those four generalised to an
arbitrary E carrying the structural laws (p = partner, the turn's site and role laws),
and only then the composition.

That is four lemmas plus the wiring, not one composition. The earlier estimate in this
log was wrong and is corrected here rather than left standing.

Whether it is worth doing is a separate question. M4b is the reverse shield inequality
for the combinatorial half of paper2; it does not bear on H1, H2 or M9, which are where
U's conditionality actually lives.

## 2026-09-03 — BLOCK 4: shield_law_final is VACUOUS for Z non-empty (RETRACTION)

Built the `Z != 0` witness that was next step #1. Result is negative, and proved so.

New in `ConfigLoop.lean` (all kernel-clean, `#print axioms` = propext/Classical.choice/Quot.sound):
  no_bottom_at_empty, no_top_at_empty, balance_empty_edges,
  balance_top_only, balance_bottom_only    -- balance keyed on EMPTY EDGES, not on
                                              absent edge INDICES (the old
                                              balance_left/right could not reach a
                                              site whose neighbouring edge had m = 0)
  witM = ![2,0,0,2], witUp = ![1,0,0,1], witM_empty, wit_edge,
  wit_no_end_at_two, wit_hbal, wit_hcov,
  wit_runInv        -- ALL SIX RunInv clauses hold simultaneously with Zf = {2}

So `RunInv` itself is satisfiable with a non-empty cut set: `hcov` in its run-local
form is fine, and the 2026-08-23 repair of `hcov` was correct.

BUT the witness cannot be fed to `shield_law_final`, and no configuration can:

  no_end_at_arrivalfree        -- a balanced site with no arrival carries no end at all
  empty_edges_at_arrivalfree   -- hence both adjacent edges have m = 0
  shield_final_hyps_incompatible -- hZ + hbal + hocc + (Zf nonempty) |- False

Reason. `hZ` says no arrival sits at a site of `Zf`. Balance then kills the
departures too, so the site carries no end; a top end of edge z-1 and a bottom end
of edge z would both sit there, so `m(z-1) = m(z) = 0`. But `hlow`/`hhigh` put z
inside `[A,B]`, and `hocc` demands edge z be occupied. Contradiction.

CONSEQUENCE: `shield_law_final` states `walkCount E = Zf.card + 1` but only ever
applies with `Zf = 0`, where it says `walkCount = 1` -- i.e. it is `thm_nogap` with
extra hypotheses, not the shield law. **The shield law is NOT proved.** The atom goes
back to OPEN. The previous version died on `hcov`; this one dies on `hZ` vs `hocc`,
which is a different clause and was invisible until the witness was actually built.

WHAT THIS SAYS ABOUT THE MATH, not just the Lean: `hZ` is too strong. The paper's
cut sites carry no *crossing ends*, but the walk still passes through them by
turning; the span condition `hocc` is about the relaxed-optimal *span*, which in the
paper is measured on a different index than the edge index used here. One of the two
has to be restated. Until then H1b (reverse shield) is OPEN, not PARTIAL.

## 2026-09-03 — BLOCK 5: shield law REPAIRED and proved non-vacuous

The BLOCK 4 retraction identified the wrong culprit as *fatal*. `hZ` is correct --
`no_ends_of_alpha_zero` already showed the paper's cut sites carry no ends, so
"no arrival at a cut site" is exactly right. The wrong hypothesis was `hocc`.

`hocc` (every position in [A,B] occupied) is used in exactly one place, and for
exactly one purpose: to produce, for each block index i, SOME vertex with blk = i.
That is "every RUN is non-empty", which is strictly weaker and IS satisfiable with
cut sites present -- the empty edges flanking a cut site do not need to be occupied,
only some edge in each run.

New in `CutComponents.lean`:
  exists_injective_components_of_runs
  exists_injective_components_avoiding_of_runs   -- prop:cut, run form

New in `ConfigLoop.lean`:
  shield_law_runs   -- THE SHIELD LAW: hZ + (every run carries an end) + RunInv
                       |- exists E, RunInv E and walkCount E = |Z| + 1
  wit_hruns, wit_hZ
  wit_shield        -- walkCount E = 2 with |Z| = 1 on the BLOCK 4 witness

So `c = |Z|` is proved AND instantiated at |Z| = 1. Non-vacuity is now a theorem,
not an assumption. All kernel-clean (`decide`, not `native_decide`); full build
8626 jobs, 0 sorry.

H1b (reverse shield): OPEN -> PROVED, with a witness. `shield_law_final` is
superseded by `shield_law_runs` and kept only as the record of the bad hypothesis,
alongside `shield_final_hyps_incompatible` which proves it was bad.

## 2026-09-03 — BLOCK 6: B1 scoped; the bridge is NOT a re-indexing

Removed the superseded `hocc` form of the shield law (`shield_law_final`); kept
`shield_final_hyps_incompatible` as the record of why it was wrong. M4b is green.

Then attacked B1 (g -> configuration), the atom qualifying M3/M5/M6/M7.
`PathData` already carries `mm` (multiplicities) and `cu`/`cdn` (up/down counts), so
the bridge to `Endpt n m` looks like re-indexing Z -> Fin n. It is not:

  balance_iff_tr      -- balance at a site <-> the two adjacent edges have EQUAL
                         signed travel  tr e = 2*min(up e, m e) - m e
  no_balance_of_tr_ne -- so unequal signed travel on adjacent edges kills balance

And `PathData.cu_sub_cdn` says the signed travel of edge j IS `travel kstar j`, which
is not constant (it is 0 outside [A,B] and generally nonzero inside). So a bare
re-indexing of a PathData is UNBALANCED at every site where travel steps.

CONSEQUENCE: the virtual events vArr/vL/vR -- the alphaAt/betaAt bookkeeping -- are
not decoration. They are exactly what makes the configuration balanced, and B1 must
add two virtual endpoints to `Endpt` rather than re-index. That is a type-level
change, so B1 is a larger job than "not started" suggested, and its size is now
known rather than guessed.

B1: not started -> SCOPED (obstruction identified and proved).

## 2026-09-03 — BLOCK 7: the root cause of the "(configurations)" qualifier

Chased H1a to `rem:pairingstatus` (paper2 l.1751): "That it computes the relaxed word
length is verified there and is not proved."

FALSE LEAD CLOSED FIRST: `lem:transport` gives the site value as max(|a|,|b|,|Phi|)
but Lean's `PathData.siteCost` is max(|a|,|b|) with no Phi. Not a defect --
`MarkedSite.Phi_le_min` is a THEOREM (|Phi| <= min(|a|,|b|)) at every site of a
realisation, so the two agree. Checked, clean.

ROOT CAUSE. `GroupElt.lean` contains no group: no group element, no word length, no
lR. Across all 84 files there was no object a group element could be. So H1a and B1
are not two proof gaps, they are ONE DEFINITIONAL gap, and it is exactly why M3/M5/M6/M7
carry "(configurations)".

NEW FILE `EltBridge.lean` (all kernel-clean):
  Elt              -- a group element in lamp form: cursor, sign, side, finitely
                      supported deposits carrying the travel parity
  occ, A, B        -- the minimal span, computed from the support
  outer, A_min, B_min  -- the three span obligations; MINIMALITY is the content
  toPathData       -- THE BRIDGE: every Elt has a PathData
  lR               -- the relaxed length of a group element, now a DEFINITION
  lR_eq            -- unfolded: span mass + site costs
  IsRelaxedLength  -- H1a as a named contract (Rule I7), not prose

WHAT IS STILL NOT DONE: `IsRelaxedLength` is a contract, not a theorem. Discharging it
needs a presentation and a generating set, and neither is formalised. That is now a
stated obligation with a name instead of a remark in a paper. Also `balance_iff_tr`
(BLOCK 6) still says the Endpt model needs virtual endpoints before a PathData can be
realised as a configuration -- toPathData is the first half of B1, not all of it.

Also fixed: `GroupElt` had a lean_lib entry but was missing from defaultTargets, so it
was never built by `lake build`. Added, along with `EltBridge`.

## 2026-09-03 — BLOCK 8: B1's remainder is exactly two sites, and the repair is forced

BLOCK 6 said the Endpt model cannot balance a PathData by re-indexing. BLOCK 8 makes
that sharp and turns it from an obstruction into a specification.

  ConfigLoop.arr_sub_dep_eq   -- SHARP: (arrivals - departures) at a site = tr e1 - tr e2
                                 (balance_iff_tr is the vanishing case)
  EltBridge.travel_const_off  -- travel is constant away from s = 0 and s = kstar
  EltBridge.balance_off_virtual -- so a travel-realising configuration is balanced at
                                   EVERY site except those two, automatically
  EltBridge.deficit_eq        -- and the deficit there is exactly
                                 [s = kstar] - [s = 0]

READ: the model is short exactly ONE arrival at site 0 and ONE departure at site
kstar, and is balanced everywhere else. So the virtual events vArr and vD are not a
modelling choice -- they are the UNIQUE repair, in the UNIQUE places, and the count
"two virtual events" is forced by the arithmetic rather than assumed.

This is why B1's second half is a bounded job: extend Endpt by two elements, not by a
family. The extension itself is not yet written.

## 2026-09-03 — BLOCK 9: the two-element extension is built and BALANCES

  VEndpt        -- Endpt n mm (+) Bool: the real ends plus exactly two virtual ones
                   (inr false = virtual arrival at site 0; inr true = virtual
                   departure at kstar). An `abbrev`, so instances stay canonical --
                   as a `def` with hand-rolled DecidableEq, `Finset.mem_image` would
                   not fire and every proof stalled.
  site, isArr, arrAt, depAt   -- the extended primitives
  arrAt_eq, depAt_eq          -- extended set = image of the real set, plus the one
                                 virtual end, at the one site where it sits
  card_arrAt, card_depAt      -- so the counts differ by exactly [s=0], [s=kstar]
  VEndpt.balanced             -- THE THEOREM: a configuration whose signed travel is
                                 `travel kstar` is BALANCED AT EVERY SITE in the
                                 extended model

So B1's second half is done at the level of balance: the obstruction proved in BLOCK 6
(`balance_iff_tr`) is removed by exactly the two ends that BLOCK 8 showed were forced.

WHAT IS STILL NOT DONE: `VEndpt.balanced` supplies `hbal` for the EXTENDED type, but
the whole merge development (ConfigMerge, WalkSupport, CostMerge, ConfigLoop) is
written against `Endpt n m`, not `VEndpt`. Transporting it is a mechanical but real
job -- `partner`, `turn`, `Data`, `walkCount` all need extending, and `partner` on the
two virtual ends is a genuine choice, not boilerplate. B1 stays YELLOW until that is
done; what changed is that the mathematical obstruction is gone and only transport
remains.

## 2026-09-03 — BLOCK 10: the virtual pairing is FORCED; a degree of freedom removed from (M)

  VEndpt.partner          -- real ends keep their partner; the two virtual ends are
                             the two ends of ONE virtual crossing, so they pair each
                             other
  VEndpt.partner_invol    -- involution
  VEndpt.partner_ne       -- no fixed point
  VEndpt.isArr_partner    -- exchanges arrivals and departures, virtual pair included
  VEndpt.partner_site_ne  -- changes site, provided kstar != 0 (travel_site_facts
                             already flags kstar = 0 as the degenerate case)
  VEndpt.partner_unique   -- **any** extended partner that restricts to the real
                             partner, is an involution, and exchanges arrivals with
                             departures MUST pair the two virtual ends with each other

The last one is the point. The virtual arrival CANNOT be partnered with a real
departure: if it were, the involution would have to send that real end back to the
virtual arrival, but on real ends the partner is already fixed and lands on a real
end. So the pairing is forced by the three properties, not chosen.

CONSEQUENCE FOR (M): `hyp:model` has one fewer degree of freedom than it appears to.
This is the first result tonight that touches H1 rather than sitting below it. It does
NOT discharge (M) -- the transfer model asserts much more than the pairing -- but it
converts one of its silent choices into a theorem.

STILL NOT DONE: `turn`, `Data`, `walkCount` on VEndpt, and re-proving the merge
development against the extended type. B1 stays yellow.

## 2026-09-03 — BLOCK 11: the virtual crossing does NOT sit on an edge

The merge development is fully generic in the end type: `CostMerge.min_merges_to_one`
takes edgeOf, siteOf, atTop, p0 as ARGUMENTS with four compatibility hypotheses. So
transport to VEndpt looked nearly free -- supply edgeOf and atTop for the two virtual
ends and everything downstream applies.

There is no such supply.

  VEndpt.no_virtual_edge -- if edgeOf and atTop satisfy hsite, hpe, hpt on VEndpt,
                            then kstar = 1 or kstar = -1

Reason: `hpe` puts the two virtual ends on a COMMON edge j (they are partners),
`hpt` makes them its two ends, and `hsite` then places their sites at j and j+1 in
some order. But their sites are 0 and kstar. Hence |kstar| = 1.

So the three facts now pull against each other:
  BLOCK 8  -- exactly two virtual ends are needed, at sites 0 and kstar (forced)
  BLOCK 10 -- they must pair each other (forced)
  BLOCK 11 -- a pair on a common edge forces |kstar| = 1 (forced)

For |kstar| != 1 the virtual pair is a crossing with no edge. That is not a defect in
the extension -- it is a real feature of the object: the virtual strand runs from the
basepoint to the cursor and spans the whole travel interval, so it is not a crossing
of any single edge.

CONSEQUENCE: `min_merges_to_one` CANNOT be applied to VEndpt as stated. Its hypotheses
hpe/hpt/hsite are edge-local and the virtual pair is not. Either the merge development
is re-proved with a weakened, non-edge-local locality hypothesis, or the virtual pair
is handled outside the merge and reattached. This is now a precise fork, and BOTH
branches are real work -- neither is bookkeeping.

B1 stays yellow, and the reason is no longer "transport not written" but "transport
provably does not apply as stated".

## 2026-09-03 — BLOCK 12: the fork is decided; branch 1 is forced and costed

Branch 2 (run the merge on real ends, reattach the virtual pair afterwards) is
IMPOSSIBLE, and provably:

  balance_of_data     -- a `Data` is a turn INVOLUTION exchanging arrivals with
                         departures at each site, so its mere existence forces
                         arrivals and departures to be equinumerous there
  no_data_of_deficit  -- hence at a site with a deficit there is NO Data at all

With deficit_eq the real-end model is off by [s=kstar]-[s=0], so at sites 0 and kstar
there is no turn -- there is nothing to run the merge on and nothing to reattach to.

Branch 1 (weaken the merge development's edge-local hypotheses) is therefore forced.
Cost, measured rather than guessed:
  WalkSupport   37 mentions of hpe/hpt across 12 of its 27 declarations
  CostMerge     18 mentions
  ConfigMerge    0   (already free of them)
  ConfigLoop    10
And the dependence is MATHEMATICAL, not clerical: the wLo arguments need the partner
of an end at a walk's leftmost edge to lie on that same edge. The virtual pair
violates this by construction -- its ends are at sites 0 and kstar, spanning the whole
travel interval.

SO: the merge argument and the virtual events are in genuine tension. That tension is
exactly what `hyp:model` papers over, and it is now a proved statement with a measured
cost rather than a suspicion. This is the sharpest description of (M)'s weakest link
the project has had.

B1 stays yellow. What changed tonight: B1 went from "not started" to a single named,
costed, mathematically-characterised obstruction with both alternatives eliminated.

## 2026-09-03 — BLOCK 13: BLOCK 12's measurement was of the WRONG hypothesis

Started branch 1 and immediately found the previous block's cost measurement was
aimed at hpe/hpt. It should not have been.

Put the virtual pair on a common phantom edge `bnd` beyond the span, with the two ends
distinguished by atTop. Then:

  VEndpt.edgeOf, VEndpt.atTop   -- the concrete choice
  VEndpt.hpe                    -- holds GLOBALLY, axiom-free
  VEndpt.hpt                    -- holds GLOBALLY, axiom-free
  VEndpt.hsite_fails            -- hsite forces |kstar| = 1 (no_virtual_edge, with
                                   the pairing now concrete)

So hpe/hpt are NOT the obstruction. `hsite` -- the relation tying a site to its edge --
is, and must be: the virtual ends' sites are 0 and kstar while their edge is bnd.

CORRECTED MEASUREMENT:
  WalkSupport   hsite in 16 of 27 declarations
  CostMerge     15 mentions
  ConfigMerge    0
  ConfigLoop     0        (BLOCK 12 reported 10 for hpe/hpt; for hsite it is zero)

And hsite localizes the same way hpe/hpt did -- it is used pointwise, not globally:

  WalkSupport.exists_bottom_at_wLo_local   -- locality asked only at the end realising
                                              the walk's leftmost edge
  WalkSupport.exists_bottom_at_wLo_of_global -- the original as a special case
  WalkSupport.shared_ends_at_wLo_local     -- hsite asked only at the end it is used on

Both localizations went through with the ORIGINAL PROOF SCRIPTS UNCHANGED, which is
the evidence that the global hypotheses were always stronger than the arguments needed.

REVISED OUTLOOK for B1: the refactor is 16 declarations in one file, mechanical in the
sense that each proof already uses the hypothesis pointwise. Not a re-proof. BLOCK 12
called this "mathematical rather than clerical" -- that was wrong, and it was wrong
because it measured hpe/hpt instead of hsite.

## 2026-09-03 — BLOCK 14: the localization is NOT uniformly free; a residual condition

BLOCK 13 said the hsite refactor is clerical, on the evidence of two lemmas whose
proofs went through unchanged. Pushing to the lemma CostMerge actually calls shows
that was too broad.

  WalkSupport.bottom_of_end_at_wLo_local        -- hsite at the one end concerned
  WalkSupport.maximiser_has_bottom_arrival_local -- hsite only at ends sitting at the
                                                    walk's LEFTMOST SITE

The second needs hsite at TWO ends: the bottom end realising the leftmost edge, and
the arrival beside it. The first is fine -- virtual ends sit at edge bnd, beyond the
span, so they are never leftmost. The second is an `arrival_beside`, i.e. a TURN
partner, and a turn CAN land on a virtual end, because a virtual end shares its site
with real ends.

  EltBridge.VEndpt.hsite_real       -- real ends satisfy the relation definitionally
  EltBridge.VEndpt.hsW_of_avoids    -- the localized hypothesis holds provided the
                                       walk's leftmost site is neither 0 nor kstar
  EltBridge.VEndpt.hsW_fails_at_zero -- and it genuinely FAILS at site 0

So branch 1 leaves a residual geometric side condition: the walk's leftmost site must
avoid the two virtual sites. That is NOT automatic -- the span begins at A <= 0, so a
walk may well have leftmost edge 0.

STATUS OF THE THREE READINGS OF THIS REFACTOR, in order:
  BLOCK 12  "mathematical, not clerical"      -- wrong, measured hpe/hpt
  BLOCK 13  "clerical"                        -- too broad, measured two easy lemmas
  BLOCK 14  clerical for the wLo lemmas; a real side condition at the turn lemmas

The third is the one with a proof on both sides (hsW_of_avoids and hsW_fails_at_zero),
so it is the one to trust.

## 2026-09-03 — BLOCK 15: the residual condition halves; one condition left

BLOCK 14 left two side conditions on the walk's leftmost site: != 0 and != kstar.
The first is now gone, for a reason that was sitting in plain sight.

`bottom_of_end_at_wLo` exists ONLY to prove `atTop a = false`. If a is already a
bottom, the site-edge relation is not needed at all. So the hypothesis at the arrival
is a DISJUNCTION:

  WalkSupport.maximiser_has_bottom_arrival_disj
      hsW : ... -> atTop x = false OR (site x = edge x + [atTop x])

And the virtual ARRIVAL is a bottom arrival (atTop = false, isArr = true), so it takes
the first disjunct and never touches the second:

  EltBridge.VEndpt.hsW_disj    -- holds whenever the leftmost site avoids kstar
                                  (axiom-free)
  EltBridge.VEndpt.hsX_beyond  -- hsX is vacuous for virtual ends once bnd exceeds the
                                  walk's leftmost edge, which it does whenever the walk
                                  contains a real end -- and it does, since the virtual
                                  arrival turns to a real departure

REMAINING: the virtual DEPARTURE. atTop (inr true) = true is forced by hpt (the two
virtual ends must have opposite tops), so it needs the second disjunct, and it is in
scope exactly when the walk's leftmost site is kstar.

So the frontier is now ONE condition: the walk's leftmost site is not kstar. Down from
two, and the surviving one is the departure end, not the arrival.

NOTE ON DIRECTION: bnd is a free parameter and I tried several placements (bnd large,
bnd = kstar-1, bnd = -1, with both assignments of atTop). Every placement leaves
exactly one condition, because hpt forces one of the two virtual ends to be a top and
that one always needs the site-edge relation. The condition can be MOVED between the
two ends but not removed by choosing bnd. That is worth recording so it is not
re-attempted.

## 2026-09-03 — BLOCK 16: the residual condition is DISCHARGED for kstar > 0

  reachable_turn                    -- reachability along a turn (was missing; only
                                       reachable_partner existed)
  VEndpt.leftmost_ne_kstar          -- a walk reaching any end at edge <= 0 has
                                       leftmost edge <= 0, hence != kstar when kstar>0
  VEndpt.turn_of_vArr_low           -- the turn of the virtual arrival is a REAL end
                                       (axiom-free): it sits at site 0, and the only
                                       virtual end at site 0 is the virtual arrival
                                       itself, which a turn cannot fix
  VEndpt.residual_discharged        -- BLOCK 15's condition, DISCHARGED for kstar > 0

Argument: the walk carrying the virtual arrival reaches its turn; that turn sits at
site 0 and is a real end, so it lies on edge -1 or 0; hence the walk's leftmost edge
is <= 0 < kstar.

WHAT REMAINS: kstar < 0. The mirror argument gives only wLo <= kstar, not wLo < kstar,
because the real ends at site kstar sit on edges kstar-1 and kstar, and kstar-1 lies
OUTSIDE the span (A <= kstar), so it may be empty. This half does not close by this
route. kstar = 0 is already excluded by partner_site_ne.

So the chain now reads, for kstar > 0 and modulo transporting the remaining WalkSupport
lemmas: Elt -> PathData -> VEndpt -> balanced -> partner -> locality hypotheses
satisfied. That is B1 for half the parameter range.

## 2026-09-03 — BLOCK 17: the reflection, so kstar < 0 reduces to kstar > 0

  travel_reflect     -- travel (-k) (-1-j) = - travel k j.  The interval [k,0) where
                        travel = -1 is carried onto [0,-k) where it is +1.
  travel_reflect'    -- the same read the other way
  Elt.reflect        -- the reflected element: kstar |-> -kstar, eps |-> -eps,
                        delta |-> !delta, d j |-> -d(-1-j), supp |-> image of supp.
                        hpar and hsupp both transport (hsupp uses that j |-> -1-j is
                        an involution, so j not in the image iff -1-j not in supp)
  Elt.reflect_kstar_pos    -- kstar < 0 gives a reflected element with kstar > 0
  Elt.reflect_reflect_d    -- reflection is an involution on the deposits

So the PARAMETER RANGE reduces: every element with kstar < 0 is the reflection of one
with kstar > 0, and BLOCK 16 discharges the residual condition there.

WHAT IS HONESTLY NOT YET DONE: the reduction is at the level of `Elt`. To conclude
that BLOCK 16's discharge covers kstar < 0, the reflection must also carry the
CONFIGURATION and its WALKS -- i.e. an isomorphism VEndpt(g) ~ VEndpt(g.reflect)
matching sites, arrivals, partners and turns. That transport is not built. Without it
this block reduces the range for the ELEMENT, not yet for the walk argument.

Also noted: `occ` is not exactly equivariant, because it inserts 0 while the
reflection sends 0 to -1. The span endpoints A, B therefore swap only up to that
off-by-one, which is why the transport needs writing rather than asserting.

## 2026-09-03 — BLOCK 18: kstar < 0 closes DIRECTLY; no transport needed

BLOCK 17 built the reflection and said the remaining piece was an isomorphism
VEndpt(g) ~ VEndpt(g.reflect). It is not needed. BLOCK 15 had already recorded that
the residual condition MOVES between the two virtual ends with the choice of bnd and
the atTop orientation; for kstar < 0 the other choice puts it where it is automatic.

Take bnd = -1 and the opposite orientation -- virtual arrival a TOP, virtual departure
a BOTTOM:

  VEndpt.atTopN   -- the opposite orientation
  VEndpt.hptN     -- hpt still holds (axiom-free)
  VEndpt.hsW_neg  -- hsW holds with NO side condition
  VEndpt.hsX_neg  -- hsX holds with NO side condition, given w <= kstar

Why: the arrival's site is 0 = -1 + 1, so it satisfies the site-edge relation
outright; the departure is a bottom, so it takes hsW's first disjunct for free; and
hsX reaches the departure only when the walk's leftmost edge is -1, which with
w <= kstar <= -1 forces kstar = -1 -- exactly the case where the relation holds at the
departure too.

STATUS: the locality hypotheses of the merge development are now satisfiable for ALL
kstar != 0 -- kstar > 0 by BLOCK 16 (original orientation), kstar < 0 by BLOCK 18
(opposite orientation). kstar = 0 is excluded by partner_site_ne.

The reflection of BLOCK 17 is therefore not on the critical path. It stays in the file
as a proved involution on Elt; it is no longer needed for this argument.

REMAINING FOR B1, precisely:
  (a) a `Data` on VEndpt -- the TURN. `VEndpt.balanced` supplies hbal; what is missing
      is the analogue of `dataOf`, building the turn permutation from it.
  (b) the remaining ~14 WalkSupport declarations and CostMerge's 15 hsite mentions,
      converted to the localized forms proved in BLOCKS 13-15.
Neither is now blocked on a mathematical question.

## 2026-09-03 — BLOCK 19: the turn on VEndpt; remaining item (a) is DONE

`DataBuild.dataOf` builds a lamp configuration's walk-graph data but is written
against Endpt n m. Its ingredients (TurnBuild.glue, exists_involution_of_card_eq) are
generic, so the construction is too. Written generically:

  GenericData.arrOf, depOf, arr_disj_dep, mem_own
  GenericData.turnAtG, turnG          -- the local and global turns
  GenericData.turnG_site, turnG_ne, turnG_invol
  GenericData.dataG                   -- THE GENERIC WALK-GRAPH DATA: any type with a
                                         site map, an arrival predicate, a fixed-point-
                                         free site-changing partner involution, and
                                         balance
and instantiated:
  VEndpt.dataOf      -- the extended type's walk-graph data (needs kstar != 0)
  VEndpt.dataOf_p    -- its pairing is the extended partner
  VEndpt.dataOf_ts   -- its turn preserves sites

So remaining item (a) from BLOCK 18 is done. This also means `DataBuild.dataOf` is now
a special case of a generic construction; the specialisation was never necessary.

HONEST SCOPE: `VEndpt.dataOf` takes balance as a hypothesis. `VEndpt.balanced` supplies
it at every site whose two edges exist; the sites outside the span need the empty-edge
argument (balance_empty_edges, BLOCK 4). That is bookkeeping and is NOT yet written --
factoring it out of the construction keeps the dependency visible rather than hiding it
inside a `noncomputable def`.

REMAINING FOR B1: the ∀-s balance for VEndpt (bookkeeping, pattern already proved in
BLOCK 4), and item (b) -- the ~14 WalkSupport declarations plus CostMerge's 15 hsite
mentions converted to the localized forms of BLOCKS 13-15.

## 2026-09-03 — BLOCK 20: balance at EVERY site; VEndpt.dataOfAll is unconditional

  ConfigLoop.arr_sub_dep_all -- the balance deficit at every site, INCLUDING those
                                whose adjacent edge indices do not exist. The
                                no_top_at_empty / no_bottom_at_empty lemmas of BLOCK 4
                                already covered that case: their hypothesis
                                "every edge at s is empty" is VACUOUSLY TRUE when no
                                edge index equals s. Nothing new was needed.
  EltBridge.arrOf_eq_arrAt, depOf_eq_depAt  -- the generic and extended sets coincide
                                               (by rfl)
  EltBridge.VEndpt.balanced_all -- balance at every site of the extended type
  EltBridge.VEndpt.dataOfAll    -- the walk-graph data, no balance hypothesis left

So the construction chain is complete and unconditional:

  Elt  ->  PathData        (Elt.toPathData, BLOCK 7)
       ->  VEndpt          (BLOCK 9)
       ->  balance at every site   (BLOCK 20)
       ->  partner, forced         (BLOCK 10)
       ->  walk-graph Data         (BLOCK 19-20, via the generic builder)
       ->  locality hypotheses satisfied for all kstar != 0  (BLOCKS 16, 18)

Its inputs are two hypotheses on the configuration: that each edge's signed travel is
`travel kstar` of that edge, and that `travel` vanishes where no edge index exists.
Both are properties of the realisation, not assumptions about the model.

REMAINING FOR B1: item (b) only -- the ~14 WalkSupport declarations and CostMerge's 15
hsite mentions converted to the localized forms of BLOCKS 13-15. No mathematical
question remains in it; the two hard ones (how many virtual ends, and how they pair)
were settled in BLOCKS 8 and 10, and the locality question in BLOCKS 16 and 18.

## 2026-09-03 — BLOCK 21: item (b), first pass through WalkSupport

Localized versions, each proved with the ORIGINAL PROOF SCRIPT and a weaker hypothesis:

  walk_shared_site_pair_local  -- hsite at the bottom end at wLo, and at y
  pair_of_equal_wLo_local      -- hsite at bottom ends on their own walk's leftmost edge
  other_end_at_wLo_local       -- the same, plus hsT at the top end immediately left

A uniform hypothesis shape emerged and is worth naming, since every remaining lemma
uses one of the two:

  hsB : forall w x, Reachable w x -> edgeOf x = wLo w -> atTop x = false ->
          siteOf x = edgeOf x + [atTop x]        (bottom ends at a walk's leftmost edge)
  hsT : forall y, edgeOf y = wLo z - 1 -> atTop y = true ->
          siteOf y = edgeOf y + [atTop y]        (the top end immediately left)

hsB is the multi-basepoint form of BLOCK 15's hsX, and VEndpt satisfies it by
hsX_beyond (kstar > 0, bnd large) or hsX_neg (kstar < 0, bnd = -1).

Running total of localized declarations: 7 of the 16 that mention hsite
(exists_bottom_at_wLo, shared_ends_at_wLo, bottom_of_end_at_wLo,
maximiser_has_bottom_arrival x2 forms, walk_shared_site_pair, pair_of_equal_wLo,
other_end_at_wLo). Remaining: pair_of_two_walks, pair_of_many_walks,
arrivals_of_many_walks, merges_to_one, maxWLo_spec, maximising_walk_all_bottom,
maximiser_departure_bottom, plus Merges and p_site_ne (which take hsite only to pass
it on).

Every one so far has gone through unchanged. No mathematical content has been touched.

## 2026-09-03 — BLOCK 22: merges_to_one is localized — the top of the WalkSupport chain

  pair_of_two_walks_local
  pair_of_many_walks_local
  arrivals_of_many_walks_local
  merges_to_one_local        -- THE TOP OF THE CHAIN

`merges_to_one_local` no longer takes the global site-edge relation. In its place:
  hpsite : forall x, siteOf (p0 x) != siteOf x     (VEndpt.partner_site_ne supplies it)
  hsB    : the relation at bottom ends on their own walk's leftmost edge, for every
           datum in the class
  hsT    : the relation at top ends immediately left of a walk's leftmost edge

The hypotheses are datum-quantified because the merge iterates over data; that is not a
complication for VEndpt, whose discharges (hsX_beyond, hsX_neg) do not mention the
datum at all -- they constrain only the VALUE of wLo.

One genuine find: `hsite` was ALSO feeding `p_site_ne` inside merges_to_one, purely to
obtain `siteOf (p0 x) != siteOf x`. That is available directly for VEndpt
(partner_site_ne), so it becomes a hypothesis rather than a derivation. Without
noticing this the localization would have looked blocked at the last step.

Running total: 11 of 16 localized. Remaining in WalkSupport: maxWLo_spec,
maximising_walk_all_bottom, maximiser_departure_bottom, and the two that only pass
hsite through (Merges, p_site_ne). Then CostMerge's 15 mentions.

## 2026-09-03 — BLOCK 23: WalkSupport DONE; min_merges_to_one localized

WalkSupport finished:
  maximising_walk_all_bottom_local
  maximiser_departure_bottom_local
  maximiser_departure_bottom_disj  -- disjunctive: its conclusion IS atTop = false, so
                                      an end already a bottom needs nothing

CORRECTION to the count: `maxWLo_spec` does NOT use hsite. The earlier grep counted it
because the NEXT theorem's signature fell inside the 14-line scan window. The real
figure was 15, not 16. Two of the remaining (Merges, p_site_ne) only pass hsite on.

CostMerge:
  hasFreePair_of_minimal_local  -- three calls, all now to localized forms
  min_merges_to_one_local       -- THE ENTRY POINT of the whole merge argument

`min_merges_to_one_local` takes, in place of the global site-edge relation:
  hpsite  : siteOf (p0 x) != siteOf x
  hsW/hsX/hsT : the three localized shapes, datum-quantified over the merge class

Same find as BLOCK 22 recurs here: hsite was feeding p_site_ne purely to obtain
hpsite. Supplying hpsite directly removes it.

Every declaration in both files kept its ORIGINAL PROOF SCRIPT. Not one line of
mathematical content was rewritten -- only hypotheses were narrowed to what the proofs
already used.

STATUS OF ITEM (b): WalkSupport complete, CostMerge's two load-bearing declarations
complete. Remaining are freePair_of_split, order_split, step_of_split, step_of_split'
(the run-local layer used by ConfigLoop's shield-law chain, not by the B1 path).

## 2026-09-03 — BLOCK 24: item (b) COMPLETE

  freePair_of_split_local
  step_of_split_local
  step_of_split'_local

SECOND COUNT CORRECTION: `order_split` does not use hsite either -- another
scan-window false positive, like maxWLo_spec in BLOCK 23. Of the 16 declarations the
original grep flagged across WalkSupport and CostMerge, TWO were miscounted and TWO
(Merges, p_site_ne) only pass the hypothesis through. The genuine figure was 12.

ITEM (b) IS DONE. Every declaration on the B1 path now exists in a form whose
site-edge hypothesis is one of exactly three shapes:

  hsW : at ends sitting at a walk's leftmost SITE      (DISJUNCTIVE with atTop = false)
  hsX : at bottom ends sitting at a walk's leftmost EDGE
  hsT : at top ends immediately LEFT of a walk's leftmost edge

and VEndpt discharges all three, for every kstar != 0:
  kstar > 0 : hsW_disj + hsX_beyond, residual condition discharged (BLOCK 16)
  kstar < 0 : hsW_neg + hsX_neg, no residual condition at all (BLOCK 18)

Not one proof script was rewritten in the whole of item (b). Every localization is the
original proof with a narrower hypothesis. The three shapes were not designed -- they
are what the proofs turned out to use.

REMAINING FOR B1: assembly only. Feed VEndpt.dataOfAll and the three discharges into
min_merges_to_one_local, and instantiate at Elt.toPathData.

## 2026-09-03 — BLOCK 25: the kstar < 0 discharges are complete and side-condition-free

  VEndpt.turn_of_vDep_real  -- the turn of the virtual DEPARTURE is a real end
                               (axiom-free), mirroring turn_of_vArr_low
  VEndpt.wlo_le_kstar       -- so the walk carrying it has leftmost edge <= kstar
  VEndpt.hsX_all_neg        -- hsX, FULLY DISCHARGED for kstar < 0, in the exact shape
                               min_merges_to_one_local consumes
  VEndpt.hsW_all_neg        -- hsW, likewise

The hsX argument closes because the two facts meet: the virtual departure sits at edge
-1, so if it is at the walk's leftmost edge then wLo = -1; but wlo_le_kstar gives
wLo <= kstar <= -1, forcing kstar = -1 -- and at kstar = -1 the site-edge relation
holds at the virtual departure outright. Every branch is discharged; nothing is left
as a hypothesis on the configuration.

WHAT REMAINS FOR ASSEMBLY (honest): min_merges_to_one_local also needs
  hside  : d.side x = atTop x     -- an EndData.Data on VEndpt, not yet defined
  hvirt  : the turn fixes neither virtual end  -- true for any Data (t_ne), but must be
           threaded
  hcov0  : the covering hypothesis -- a genuine property of the configuration, and the
           one input that is NOT supplied by the construction
The first two are mechanical. hcov0 is the same covering condition the Endpt-side
argument has always needed, so it is not new debt introduced by the extension.

## 2026-09-03 — BLOCK 26: B1 ASSEMBLED for kstar < 0

  CostMerge.min_merges_to_one_local -- hypotheses widened from `E.p = p0` to the full
                                       Merges predicate (hsX needs hts per datum; it is
                                       available at the call site and was simply not
                                       being passed)
  vEndDataOf                        -- the end data of the extended type
  VEndpt.merges_to_one_neg          -- **THE ASSEMBLED THEOREM**: a cost-minimal datum
                                       on VEndpt merges down to a single walk

Every locality hypothesis of the merge development is discharged by the construction.
The sole remaining input is hcov0, the covering condition -- the same one the
Endpt-side argument has always required.

One correction made while assembling, worth recording because the first version was
WRONG in an instructive way: I wrote the hsT branch at the virtual ARRIVAL as a
contradiction, expecting it to be out of scope. It is IN scope (its atTopN is true),
and it needs no contradiction -- the relation simply HOLDS there, since site 0 = -1 + 1
under the choice bnd = -1. That is exactly the design recorded in BLOCK 18, and the
proof got shorter, not longer, once the branch was read correctly.

So: the chain Elt -> PathData -> VEndpt -> Data -> merge is complete for kstar < 0,
with hcov0 as its only hypothesis.

## 2026-09-03 — BLOCK 27: B1 assembled for kstar > 0; the construction is COMPLETE

  vEndDataOfP
  VEndpt.merges_to_one_pos   -- the assembled theorem in the original orientation

The three shapes discharge differently from the kstar < 0 case, and each for a reason
that is a THEOREM proved earlier tonight, not a hypothesis:
  hsW at the virtual DEPARTURE -- excluded: it is reachable from its partner the
      virtual arrival, and residual_discharged (BLOCK 16) then says the walk's leftmost
      edge is not kstar
  hsX at the virtual ARRIVAL   -- excluded: the walk reaches a real end at edge <= 0
      (turn_of_vArr_low, BLOCK 16), so bnd is not the leftmost edge
  hsT at the virtual departure -- excluded: bnd + 1 exceeds every edge

Extra hypothesis used: hbnd, that bnd exceeds every real edge. That is a free choice of
the phantom edge, not a constraint on the configuration.

STATUS OF B1. The bridge is BUILT and PROVED to feed the merge development, for every
kstar != 0:
  kstar < 0 : VEndpt.merges_to_one_neg   (BLOCK 26)
  kstar > 0 : VEndpt.merges_to_one_pos   (BLOCK 27)
  kstar = 0 : excluded by partner_site_ne
with hcov0 -- the covering condition the Endpt-side argument has always needed -- as
the only remaining input.

WHAT THIS DOES NOT YET DO: M3/M5/M6/M7 are stated about Endpt configurations. Dropping
their "(configurations)" qualifier means RESTATING each for Elt through this bridge.
That is a separate step and it is not done. B1 itself -- the bridge -- is complete.

## 2026-09-03 — BLOCK 28: B1 GREEN WAS PREMATURE — retracted to yellow

Trying to restate M6 through the bridge exposed a gap in the bridge itself, one block
after I marked it green.

  EndType_edgeOf_nonneg -- every Endpt edge index is >= 0 (edge : Fin n)
  no_endpt_at_neg       -- so there is NO end on a negative edge, whatever the
                           multiplicities
  no_vendpt_at_neg      -- and none on the extended type either, for bnd >= 0

But a PathData spans [A, B] with A <= 0, and A may be STRICTLY negative. So an element
whose span reaches left of the origin has no Endpt representation at the indices its
PathData uses.

WORSE, AND THE POINT: an Elt with kstar < 0 has travel = -1 on [kstar, 0), so its span
satisfies A <= kstar < 0. THE ENTIRE kstar < 0 BRANCH CAN NEVER BE INSTANTIATED FROM
AN Elt. BLOCK 26's merges_to_one_neg is a true theorem about configurations, but it is
unreachable from the element side.

That also explains why BLOCK 18 closed kstar < 0 "with no side condition" so smoothly:
bnd = -1 puts the virtual pair at an index no real end can occupy, so every awkward
case was vacuous. The smoothness was a symptom, not a result.

WHAT IS ACTUALLY ESTABLISHED: the bridge works for A = 0 -- elements with no deposit
and no travel left of the origin. BLOCK 27's merges_to_one_pos is the live branch.

THE FIX: `VEndpt.site` hard-codes the two virtual sites as `0` and `kstar`. Parametrise
them as `s0` and `s1`, and a configuration shifted right by `-A` becomes representable,
with the virtual events at `-A` and `kstar - A`. Everything from BLOCK 8 onward was
written against the literals and will need the parameters threaded through.

B1: GREEN -> YELLOW. I marked it green one block early. The atom is the bridge from a
group element, and the bridge does not yet reach elements with A < 0.

## 2026-09-03 — BLOCK 29: parametrised virtual sites; the A < 0 gap is closable

  VEndpt.siteP           -- the site map with both virtual sites as parameters s0, s1
  VEndpt.siteP_zero      -- VEndpt.site kstar is the case s0 = 0, s1 = kstar
  VEndpt.arrAtP/depAtP, arrAtP_eq/depAtP_eq, card_arrAtP/card_depAtP
  travelS                -- the travel indicator on shifted edge indices:
                            travelS A kstar j = travel kstar (A + j)
  travelS_site_facts     -- travelS steps EXACTLY at -A and kstar - A
  VEndpt.balanced_allP   -- balance at every site of the shifted configuration

The shift works: a configuration spanning [A, B] with A < 0, moved right by -A, has
edges 0..B-A (all representable by Fin n) and its two virtual events land at -A and
kstar - A, which is exactly what siteP takes as parameters.

So BLOCK 28's gap is closable, and the shape of the fix is confirmed rather than
assumed: travelS_site_facts is the shifted form of travel_site_facts, and balanced_allP
the shifted form of balanced_all, both proved.

STILL TO DO for the A < 0 case: the partner site-distinctness (needs -A != kstar - A,
i.e. kstar != 0, unchanged), the locality discharges (BLOCKS 16/18 rewritten against
s0/s1 rather than 0/kstar), and the re-indexing PathData -> Fin n itself, which no
block has yet written. That last one is the actual remaining content of B1.

## 2026-09-03 — BLOCK 30: the re-indexing is WRITTEN; Elt -> balanced configuration

The map I had been building around for twenty blocks without writing:

  pdWidth, pdWidth_pos   -- the span has (B - A + 1) edges, and at least one
  pdMm, pdUp             -- edge i of the shifted configuration is edge A + i of the
                            original; multiplicities and up-counts transported
  pd_tr_eq               -- the shifted configuration carries the RIGHT SIGNED TRAVEL:
                            tr = 2 min(cu, mm) - mm = 2 cu - mm = cu - cdn = travel,
                            using cu <= mm from cu_add_cdn and cu_sub_cdn
  pd_travelS_zero_outside -- and the travel vanishes off the index range (houter)
  pd_balanced            -- THE JOIN: those two plus balanced_allP give balance at
                            every site, virtual events at -A and kstar - A
  Elt.balanced           -- and hence for a group element:
                            Elt -> PathData -> Fin n -> VEndpt -> balanced

So the composite the whole bridge was for now exists as a single theorem, and it works
for A < 0 -- the case BLOCK 28 showed the unparametrised version could not reach.

The key computation is three lines and was available from the start: cu + cdn = mm
gives cu <= mm, so min(cu, mm) = cu and tr = cu - cdn, which cu_sub_cdn says is
travel. BLOCK 6 proved the naive re-indexing cannot balance and I read that as the map
being hard; it was not -- what was hard was everything the map needed AROUND it (the
virtual pair, its forcing, its pairing, the locality discharges), and that is what
BLOCKS 8-29 built.

REMAINING FOR B1: the locality discharges (BLOCKS 16/18) are written against the
literals 0 and kstar; they need the s0/s1 parameters threaded, exactly as siteP did for
the site map. Then the assembled merge theorems apply to Elt.balanced directly.

## 2026-09-03 — BLOCK 31: the locality discharges are parametrised; assembly is shift-proof

  VEndpt.partner_site_neP     -- partner changes site whenever s0 != s1
  VEndpt.turn_of_vArr_realP   -- the turn of the virtual arrival is a real end
  VEndpt.wlo_le_s0            -- so the walk carrying the virtual pair has leftmost
                                 edge <= s0
  VEndpt.residual_dischargedP -- hence != s1, given s0 < s1
  vEndDataP
  VEndpt.merges_to_oneP       -- **THE ASSEMBLED THEOREM, SHIFT-PROOF**

The condition that was "kstar > 0" is now "s0 < s1", and it is invariant under the
shift exactly as it must be: -A < kstar - A iff 0 < kstar. So the parametrisation did
not weaken anything; it made the same hypothesis expressible for a shifted
configuration, which is what BLOCK 28 showed was missing.

The three discharges read cleanly in the parametrised form:
  hsW at the virtual DEPARTURE -- excluded, reachable from its partner, wLo <= s0 < s1
  hsX at the virtual ARRIVAL   -- excluded, wLo <= s0 < bnd
  hsT at the virtual departure -- excluded, bnd + 1 exceeds every edge

REMAINING FOR B1: connect `Elt.balanced` to a MergesMin datum -- i.e. the parametrised
form of GenericData.dataG plus CostMerge.exists_mergesMin -- and supply hcov0. Both are
assembly, not new mathematics: dataG is already generic in the site map, so it accepts
siteP unchanged.

## 2026-09-03 — BLOCK 32: the generic turn flips roles; dataG is in the merge class

  GenericData.mem_arrOf, mem_depOf  -- membership characterisations, stated once and
                                       proved by simp, so no later proof has to guess
                                       what simp did
  GenericData.turnG_arr             -- THE MISSING PIECE: the generic turn exchanges
                                       arrivals and departures
  GenericData.dataG_merges          -- so dataG satisfies WalkSupport.Merges

BLOCK 19 built dataG and proved involutivity, site-preservation and fixed-point
freedom -- but not the role flip, which is the third component of `Merges`. Without it
dataG could not be fed to exists_mergesMin at all. Found only by trying to use it.

PROCESS NOTE (Lean rule 4.1). Three strikes on turnG_arr, all the same mistake: I was
building Finset memberships through `simp only` whose normal form I could not predict
-- it collapses `siteOf x = siteOf x` away, so `<rfl, h>` supplied two fields where one
was wanted, and each "fix" guessed a different post-simp shape. ABORT was called and
the repair was architectural: state mem_arrOf/mem_depOf once as iff-lemmas and use
`.mp`/`.mpr`. Went through immediately. The rule earned its keep: strikes 2 and 3 were
both guesses at simp's output rather than diagnoses.

Second, unrelated error worth recording: dataG_merges was inserted textually BEFORE
dataG. The error read "Unknown identifier hbal", which looks like a variable-scope
problem and is not one.

## 2026-09-03 — BLOCK 33: Elt.merges_to_one — B1 RUNS END TO END for kstar > 0

  arrOfP_eq, depOfP_eq          -- generic and parametrised sets coincide (rfl)
  VEndpt.exists_mergesMinP      -- a cost-minimal datum exists for a balanced
                                   parametrised configuration
  Elt.merges_to_one             -- **THE END-TO-END THEOREM**

A group element with kstar > 0 yields a configuration on the extended type carrying a
cost-minimal datum that merges to a single walk. Every step is a theorem proved
tonight:

  Elt.toPathData      (BLOCK 7)
  pdWidth/pdMm/pdUp   (BLOCK 30)   the re-indexing
  pd_tr_eq            (BLOCK 30)   right signed travel
  Elt.balanced        (BLOCK 30)   balance at every site
  dataG + dataG_merges (BLOCKS 19, 32)
  exists_mergesMinP   (BLOCK 33)
  merges_to_oneP      (BLOCK 31)   the merge, locality all discharged

The covering condition hcov0 is the sole input, and it is the one the Endpt-side
argument always needed.

SCOPE, stated rather than glossed: this is kstar > 0. The condition enters as
s0 < s1, i.e. -A < kstar - A. For kstar < 0 the orientation must be mirrored
(atTopN, as in BLOCK 18) and the parametrised assembly redone with s1 < s0. That is a
parallel construction, not a gap in the argument, but it is NOT WRITTEN.

B1 stays YELLOW. After BLOCK 27-28 -- where I marked it green and a single
instantiation attempt broke it one block later -- the colour changes only when the
whole parameter range is covered and the theorem has been instantiated, not when the
main branch compiles.

## 2026-09-03 — BLOCK 34: the mirror; B1 covers every kstar != 0

  VEndpt.turn_of_vDep_realP, VEndpt.wlo_le_s1
  vEndDataN
  VEndpt.merges_to_oneN     -- the assembly for s1 < s0
  VEndpt.exists_mergesMinN
  Elt.merges_to_one_neg     -- the Elt-level mirror

With bnd = s0 - 1 and the atTopN orientation, hsW and hsT hold OUTRIGHT -- the virtual
arrival is a top at s0 = bnd + 1, so the site-edge relation is true there, and the
virtual departure is a bottom, so it takes hsW's first disjunct. Only hsX needs an
argument, and it is the mirror of BLOCK 16: the walk reaches the turn of the virtual
departure, a real end at site s1, so wLo <= s1; combined with wLo = s0 - 1 and
s1 < s0 this forces s1 = s0 - 1, where the relation holds.

So the two orientations together cover every kstar != 0:
  Elt.merges_to_one       kstar > 0   (s0 < s1, bnd above every edge)
  Elt.merges_to_one_neg   kstar < 0   (s1 < s0, bnd = s0 - 1)
  kstar = 0  excluded: the two virtual events would coincide, and partner_site_neP
             needs them distinct

Both take hcov0 -- the covering condition -- as their only input.

The asymmetry between the two branches is real and worth recording: for kstar > 0 the
awkward end is the virtual DEPARTURE and bnd must sit above every edge; for kstar < 0
it is the virtual ARRIVAL and bnd sits just below s0. BLOCK 15 predicted exactly this
("the condition can be MOVED between the two ends but not removed"), and both branches
came out as that note said they would.

## 2026-09-03 — BLOCK 35: B1 INSTANTIATED — the bridge carries an actual element

  witElt            -- the smallest non-trivial group element: kstar = 1, one deposit
                       at edge 0, travel +1 there and nowhere else
  witElt_occ        -- its occupied set is {0}
  witElt_A, witElt_B -- so A = B = 0
  witElt_width      -- its span has exactly ONE edge
  witElt_mm_pos     -- and that edge carries a crossing (via mm_eq_mu and mu_pos)
  witElt_edge_lt    -- every real end sits at edge 0
  witElt_hcov0      -- the covering condition holds with phantom edge 1
  witElt_merges     -- **B1 INSTANTIATED**: this element yields a cost-minimal datum
                       on the extended type that merges to a single walk

This is the check that broke the premature green at BLOCK 28, and it passes. The
theorem is applied to a concrete Elt, not to a hypothetical configuration: the element
is built, its span computed, its covering condition proved, and Elt.merges_to_one
applied with every hypothesis discharged.

The hcov0 proof is the informative part. Every end sits at edge 0 (real) or 1
(virtual), so an end with a strict predecessor forces j = 1, and the required top end
at edge 0 exists because the single edge has positive multiplicity. Both facts are
theorems, not computations.

Trap hit again, for the third time tonight: `i : Fin (pdWidth P)` means rewriting
pdWidth in `i.isLt` is never type-correct. Fix is always the same -- state both facts
and let omega combine them, never rw.

B1: YELLOW -> GREEN. Built, covering the whole parameter range (BLOCKS 33-34), and
instantiated on an actual element (BLOCK 35).

## 2026-09-03 — BLOCK 36: M6, M5, M7 restated FOR GROUP ELEMENTS

The four greens carried a "(configurations)" qualifier because nothing in the
development was a group element. Three of them now have element-level forms:

  one_le_walkCount     -- at least one walk, for any datum on an inhabited end type
                          (VEndpt is always inhabited: it carries the two virtual ends)
  Elt.single_walk      -- M6 for an element: EXACTLY one walk
  witElt_single_walk   -- instantiated
  Elt.defect_zero      -- M5/M7 for an element: c(g) = 0
  witElt_defect_zero   -- instantiated

So `thm:nogap` with cost, `cor:localzero` and `prop:travelinv` are now statements about
`Elt`, not about hypothetical configurations, and each has been applied to a concrete
element rather than left as a general form.

SCOPE: kstar > 0. The kstar < 0 branch has its own assembly (merges_to_oneN,
Elt.merges_to_one_neg, BLOCK 34) but the single_walk/defect_zero corollaries have not
been mirrored onto it. That is three lines each and no new mathematics, but it is not
written.

REMAINING QUALIFIER: M3 (prop:cut, c >= |Z|) and M4b (the shield law) are about the cut
set Z, which has no element-level form yet -- Z is defined on a PathData via alphaAt /
betaAt / PhiAt, so the element form needs those transported through the re-indexing.
That is the next genuine piece of work, not bookkeeping.

## 2026-09-03 — BLOCK 37: the cut set of a group element

  pdCutAt        -- a cut site of the SHIFTED configuration: P.cut (P.A + s)
  pdCutAt_iff    -- away from the two virtual sites the three virtual counters vanish
                    and the condition reduces to the plain read-off
                        d(s-1) = 0,  d(s) = 0,  f(s-1) = 0
  pdCutAt_d_zero -- so a cut site has no deposit on either adjacent edge

Both depend on `propext` alone -- no choice, no classical reasoning. The whole content
is that `vArr`, `vL`, `vR` are supported on `s = 0` and `s = kstar`, so off those two
sites the definition of `cut` collapses to the read-off. That collapse is what makes
the element-level cut set computable from `d` and `f`.

Note for the record: this is the same fact that BLOCK 3's `cutSitesZ` got WRONG by
omitting the virtual-event condition. Stated here with the exclusions explicit as
hypotheses (h0, hk) rather than left implicit, which is why it is three lines.

REMAINING FOR M3/M4b at element level: the cut set as a Finset over the shifted range,
and the transport of the shield-law chain (RunInv, local_of_hturn, the runs) from
Endpt to VEndpt. The chain is generic in the end type in ConfigLoop only up to the
Endpt-specific `hZ`; that is the piece to redo.
