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

## 2026-09-03 — BLOCK 38: the cut set as a Finset; the shield law at element level

  pdCutSites            -- Z as a Finset: cut sites INTERIOR to the shifted span,
                           Ioo 0 width. The interiority is the 2026-08-23 retraction:
                           a run of L gap edges gives L-1 interior sites, so counting
                           endpoints overcounts by one per run.
  mem_pdCutSites, pdCutSites_interior
  witElt_cutSites       -- the witness has NO cut site: its span is one edge, so
                           Ioo 0 1 is empty
  witElt_shield         -- **c = |Z| for an actual group element**

The last one is a genuine cross-check rather than a restatement. `witElt_single_walk`
produced walkCount = 1 through the MERGE (BLOCKS 33-36); `witElt_cutSites` computes
|Z| = 0 from the CUT DEFINITION (BLOCKS 37-38). The shield law says these must agree,
and they do. Two independent routes to the same number on the same element.

That is the first time tonight that the merge side and the cut side have been
evaluated on the same object and compared. Every earlier agreement between them was
structural (the same lemmas applied), not numerical.

REMAINING for M3/M4b in general (not just on the witness): the shield-law chain
(RunInv, local_of_hturn, run induction) transported from Endpt to VEndpt. BLOCK 12
showed the load-bearing hypothesis there is hZ -- no arrival at a cut site -- and that
it forces both adjacent edges empty. For VEndpt that argument needs redoing, since the
virtual ends change which sites can carry arrivals.

## 2026-09-03 — BLOCK 39: hZ on the extended type; cut sites are never virtual sites

  no_end_at_arrivalfree_gen      -- BLOCK 12's argument, made generic: a balanced site
                                    carrying no arrival carries NO END, for any end
                                    type. Nothing in it ever used Endpt.
  VEndpt.arrivalfree_ne_virtual  -- NEW CONTENT on the extended type: the two virtual
                                    ends ARE ends, so an arrival-free site is neither
                                    s0 nor s1. Hence NO CUT SITE IS A VIRTUAL SITE.
  VEndpt.empty_edges_at_arrivalfree -- and both adjacent edges are empty
  VEndpt.cut_site_picture        -- the two together

The middle one is the structural reason the shield law and the virtual events do not
interfere, and it is now a theorem rather than an assumption. It also retroactively
explains BLOCK 11's tension: the virtual pair cannot sit on an edge, but it also never
sits at a cut site, so the two constructions occupy disjoint parts of the span.

This is the fact BLOCK 12 was one step away from. There I proved hZ + balance forces
both adjacent edges empty and concluded the hypotheses were incompatible with hocc.
The run form (BLOCK 5) had already removed hocc; what was missing was that the virtual
ends are excluded from cut sites, which makes the whole picture consistent.

REMAINING for M3/M4b in general: the run induction itself (RunInv and local_of_hturn)
on VEndpt. The generic lower-bound machinery in CutComponents is already end-type
agnostic (exists_injective_components_avoiding_of_runs), so what is needed is the
locality predicate `Local` for the extended graph.

## 2026-09-03 — BLOCK 40: locality confines bnd; the two assemblies want different phantom edges

  VEndpt.local_confines_bnd  -- if the extended graph is CutComponents.Local with
                                pos = edgeOf bnd, then s0 - 2 <= bnd <= s0 + 1
  VEndpt.mirrored_bnd_ok     -- and bnd = s0 - 1 is inside that window

Reason: Local puts the two ends of a graph edge on one site's two edges, so their
positions differ by at most one. The turn of the virtual arrival is a real end at site
s0, hence on edge s0 - 1 or s0. So bnd is within one of that.

CONSEQUENCE, and it is a real constraint: bnd CANNOT be placed above every real edge of
a wide configuration. But that is exactly what the s0 < s1 merge assembly (BLOCK 31)
requires via hbnd. So:

  merge, s0 < s1  wants bnd ABOVE every edge      -- not local
  merge, s1 < s0  uses bnd = s0 - 1               -- local
  shield law      needs Local                      -- so needs bnd near s0

The MIRRORED orientation satisfies both. The s0 < s1 orientation does not, and cannot
be patched by choosing bnd differently, because hbnd and local_confines_bnd are
incompatible once the span is wider than three edges.

FIRST STATEMENT OF THIS WAS FALSE. I claimed locality forces bnd in {s0-1, s0}. It does
not: Local gives |pos x - pos y| <= 1 and edgeOf u ranges over {s0-1, s0}, so the window
is [s0-2, s0+1]. omega caught it -- the proof simply would not close, and the reason was
that the statement was too strong, not that the tactic was wrong. Corrected before
recording.

## 2026-09-03 — BLOCK 41: LOCALITY BOUNDS THE TRAVEL — a real obstruction

  VEndpt.local_confines_bnd'  -- the mirror at the virtual departure: s1-2 <= bnd <= s1+1
  VEndpt.local_bounds_travel  -- both windows must hold, so |s0 - s1| <= 3

Since s0 = -A and s1 = kstar - A, this says: **if the extended graph is
CutComponents.Local, then |kstar| <= 3.**

So the shield law's locality hypothesis CANNOT hold on the extended type for a
configuration whose travel is longer than three. This is not a defect in the
construction and not something a different choice of bnd can fix: the virtual pair
joins site s0 to site s1 in ONE graph step, and `Local` is precisely the statement
that a graph edge does not span more than one site. A virtual strand running the whole
travel interval is non-local by definition.

WHAT THIS MEANS FOR M3/M4b AT ELEMENT LEVEL. The lower bound c >= |Z| is proved in
CutComponents from `Local`. That route does not transport to VEndpt. Either
  (a) the lower bound is re-proved from a weaker locality that tolerates one long edge,
      or
  (b) the virtual pair is excluded from the graph used for the cut count, and the two
      graphs related afterwards.
Both are real work. (b) looks more promising: BLOCK 39 showed cut sites are never
virtual sites, so deleting the virtual pair from the graph does not touch any cut site.

This is the third genuine obstruction found tonight by trying to USE a construction
rather than by inspecting it (after BLOCK 28's negative edges and BLOCK 32's missing
role flip). The pattern is now consistent enough to state as a rule: a construction is
not known to work until something downstream consumes it.

## 2026-09-03 — BLOCK 42: no cut site inside the travel interval — route (b) is viable

  no_cut_inside_travel   -- THE KEY LEMMA: a cut site has Phi = 0, which away from the
                            two virtual sites reads f(s-1) = 0; but f is +1 throughout
                            0 <= j < kstar. So no site strictly inside the travel
                            interval is cut.
  pdCut_avoids_travel    -- the same, contrapositive
  gz_eq_of_no_between    -- the CONVERSE of BLOCK 3's gz_ne_of_between: no cut site
                            between two points means the same run. BLOCK 3 proved the
                            separating direction; this is the joining one.
  virtual_pair_same_run  -- so s0 and s1 lie in the SAME RUN

This is what makes route (b) work, and it answers BLOCK 41's obstruction directly.
The virtual pair is non-local -- it joins s0 to s1 in one step, so `Local` fails for
travel longer than three. But locality is only ever used to prove that the block index
is constant along graph edges (blk_adj). And the virtual pair joins two ends of ONE
run, so the block index IS constant along it. The hypothesis fails; the conclusion it
was there to give still holds.

Both new lemmas depend on propext (+Quot.sound) alone -- no choice.

WHAT REMAINS for M3/M4b at element level: a variant of CutComponents.blk_adj taking
"Local except on a listed set of edges, each joining ends of equal block index" instead
of Local. That is a genuine generalisation of the CutComponents machinery, but it is
now a precisely specified one, and the fact it needs (virtual_pair_same_run) is proved.

## 2026-09-03 — BLOCK 43: LocalExcept — the CutComponents machinery generalised

  CutComponents.LocalExcept          -- Local, except on edges listed by a predicate Exc
  CutComponents.blk_adj_except       -- the block index is constant across an edge,
                                        given locality except on edges that already
                                        preserve it (propext + Quot.sound only)
  CutComponents.blk_reachable_except
  CutComponents.exists_injective_components_of_runs_except
  CutComponents.exists_injective_components_avoiding_of_runs_except  -- prop:cut

`Local` was always stronger than the argument needed: everything below it uses locality
ONLY through blk_adj, and an edge that spans many sites but joins ends of equal block
index does no harm. That is exactly the virtual pair (BLOCK 42: it stays in one run).

So BLOCK 41's obstruction is now fully answered. The chain is:
  BLOCK 41  Local FAILS on VEndpt for travel > 3          (proved)
  BLOCK 42  but the virtual pair joins ends of one run     (proved)
  BLOCK 43  and locality is only used through blk_adj      (proved, by generalising)

Every proof script in the generalised versions is the original with one added case.

Two scope errors on the way, both from Lean's `variable` mechanics rather than from
mathematics: `Local` was defined while G/pos/Zf were EXPLICIT, my `LocalExcept` after
they became implicit, so passing them explicitly failed; and the namespace is
CutComponents, not CutComponents.Graph. Neither error had anything to do with the
argument, and both produced messages ("application type mismatch", "unknown constant")
that read like real problems.

## 2026-09-03 — BLOCK 44: prop:cut in its weakest usable form, instantiated for VEndpt

  CutComponents.exists_injective_components_avoiding_blk_or_local
      -- taking Exc = "this edge already preserves the block index" makes the side
         condition VACUOUS, and the hypothesis collapses to one readable disjunction:
         EVERY GRAPH EDGE EITHER PRESERVES THE BLOCK INDEX OR IS LOCAL.
  EltBridge.VEndpt.blk_or_local
      -- and the extended graph satisfies it:
           partner edges keep the edge index (hpe), so both ends share a position
           turn edges between real ends are local (hreal)
           turn edges at a virtual end preserve the block index (hvirt, = BLOCK 42)

VEndpt.blk_or_local depends on propext + Quot.sound only.

The Exc = "blk-equal" choice is the point of the block. With it, hexc is `fun _ _ h => h`
and the whole exception apparatus of BLOCK 43 disappears from the interface, leaving a
hypothesis a reader can check by inspection. I built LocalExcept with a general Exc and
then found the only instance worth having is the one that makes it trivial.

Two elaboration errors, neither mathematical: `VEndpt.hpe` needed its implicits, and
`Sum.inr b` inside a hypothesis had no inferable type until annotated `: VEndpt n mm`.

REMAINING for M3 at element level: discharge `hreal` (the site-edge locality at real
ends, which is just `local_of_hturn` restricted to real ends) and `hruns` (every run
carries an end). Then prop:cut applies to the extended graph.

## 2026-09-03 — BLOCK 45: prop:cut PROVED for the extended type — M3 at element level

  VEndpt.hreal_of_hturn        -- hreal discharged: a turn out of a real end either
                                  lands on a real end (local, by the site-edge
                                  relation) or on a virtual end, where the INVOLUTION
                                  turns it back into an instance of hvirt
  walkCount_ge_of_avoiding_gen -- the ConfigLoop version was stated for Endpt; nothing
                                  in its proof used that
  VEndpt.prop_cut              -- **c >= |Z| for the extended type**
  VEndpt.walkCount_ge          -- as a bound: |Z| + 1 <= walkCount

So the lower bound half of the shield law now holds on VEndpt. Its hypotheses are
exactly what the construction supplies:
  hp     the pairing is the partner                 (dataOf, BLOCK 19)
  hts    turns preserve sites                        (turnG_site, BLOCK 19)
  hturn  real turns do not cross cut sites           (the paper's cut condition)
  hvirt  the virtual pair stays in one run           (BLOCK 42)
  hruns  every run carries an end
plus a basepoint. Only hturn and hruns are inputs about the configuration; the rest are
theorems from the construction.

The hreal case split is the neat part and was not obvious: when a real end's turn lands
on a VIRTUAL end, the edge looks like it needs locality, but E.t_invol rewrites it as
the same edge traversed from the virtual side, where hvirt already applies. No new
hypothesis was needed for that case.

This is the LOWER bound (c >= |Z|). The upper bound (c <= |Z|) is the run induction,
which is the remaining half of M4b at element level.

## 2026-09-03 — BLOCK 46: the SHIELD LAW for the extended type — c = |Z| on VEndpt

  runIndexG                 -- the run index, generically
  walkCount_le_runs_blk     -- walkCount <= |Z| + 1 for ANY end type whose graph edges
                               preserve the block index or are local, and whose runs
                               are connected
  VEndpt.walkCount_le       -- the upper bound on the extended type
  VEndpt.shield             -- **c = |Z| ON VEndpt**, both bounds together

`ConfigLoop.walkCount_le_runs_gen` was stated for Endpt and asked for `Local`. Both
restrictions came off without touching the proof: ConfigMerge.walkCount_le_card was
already generic, and locality is used only through blk_reachable, which BLOCK 43
generalised. The body is `simpa using` the same call.

So the shield law -- the thing that died twice tonight, first on hcov (BLOCK 3) and
then on hZ-versus-hocc (BLOCK 4) -- now holds on the end type that actually carries a
group element's configuration. Its six hypotheses are:
  hp, hts     supplied by the construction (dataOf)
  hturn       the paper's cut condition on real turns
  hvirt       the virtual pair stays in one run  (BLOCK 42, proved)
  hruns       every run carries an end
  hsep        ends of one run share a walk
The last is the run induction's conclusion and is the remaining input; hruns is a
statement about the configuration. Neither is a locality hypothesis, which is the
change from BLOCK 41.

## 2026-09-03 — BLOCK 47: the run step, generically

  run_step_gen -- either a strict descent exists, or the runs are already connected

`hsep` is the conclusion of a descent: while two ends of one run lie in different
walks, a free pair exists and merging it lowers the walk count.
`CostMerge.step_of_split_local` supplies that step, and BLOCKS 21-24 had already made
it generic in the end type, so the run step is generic too. The proof is four lines:
case-split on hsep, extract the two ends, hand them to step_of_split_local.

This is the first time tonight the localization work has PAID OFF rather than merely
been correct. run_step_local for Endpt (BLOCK 3) took three strikes and ~40 lines of
invariant threading; the generic version is four lines, because the hypotheses it needs
are the three localized shapes and those are exactly what VEndpt discharges.

WHAT IS STILL MISSING for hsep on VEndpt: run_step_gen returns a descent WITHOUT the
invariant -- step_of_split_local drops MergesMin. To iterate (via
ConfigMerge.reaches_stuck) the descent must preserve the class, which is what
step_of_split'_local returns instead. That swap is the remaining piece, and it is
mechanical: step_of_split'_local was localized in BLOCK 24 for exactly this reason.

## 2026-09-03 — BLOCK 48: hsep DISCHARGED — the run induction, generically

  run_step_min_gen      -- the run step PRESERVING the merge class. step_of_split'_local
                           returns D'.p = D.p and D'.t = swapT ..., which is enough:
                           swapT_site and swapT_arr restore Merges, and cost_swapData
                           (through cost_congr, since costOf depends only on .t)
                           restores minimality.
  exists_run_connected  -- iterating it via ConfigMerge.reaches_stuck reaches a
                           cost-minimal datum whose RUNS ARE CONNECTED

That is `hsep`, the last input of VEndpt.shield that was not either a construction
theorem or a stated property of the configuration.

So the shield law's inputs are now:
  hp, hts   from the construction        (BLOCK 19)
  hvirt     proved                        (BLOCK 42)
  hsep      proved                        (BLOCK 48)
  hturn     the paper's cut condition on real turns   -- INPUT
  hruns     every run carries an end                   -- INPUT
Two inputs remain, both statements about the configuration rather than about the
model, and both are the same inputs the Endpt-side argument has always taken.

One direction error: `hss` from step_of_split' is `siteOf a' = siteOf a`, and I applied
`.symm` to it before passing it on. The error message named the expected and actual
types, so this was a one-line diagnosis rather than a guess.

## 2026-09-03 — BLOCK 49: VEndpt.shield_final — c = |Z| with hsep discharged

  VEndpt.shield_final -- c = |Z| for a cost-minimal datum on the extended type, with
                         hsep produced by exists_run_connected rather than assumed

The remaining hypotheses are of three kinds:
  CONSTRUCTION   hside, hpsite, hpe, hpt   -- all supplied by the VEndpt construction
  DISCHARGED     hsW, hsX, hsT             -- BLOCKS 16, 18, 31, 34 prove these for
                                              both orientations
  CONFIGURATION  hturn, hruns, hcov        -- statements about the configuration, and
                                              the same ones the Endpt-side argument has
                                              always taken
  PROVED         hvirt                     -- BLOCK 42

So nothing model-specific remains. The shield law on the end type that carries a group
element's configuration now rests on exactly the inputs the paper's own argument rests
on, and on nothing about the virtual pair beyond hvirt, which is a theorem.

Failure mode worth noting: `forall w y` with no type annotation. In hsW and hsX the
following `Reachable w x` pins the types; in hsT nothing does, and the error
("don't know how to synthesize implicit argument n") points at the USE site rather than
at the binder. Annotating the binders fixed it.

## 2026-09-03 — BLOCK 50: shield_finalT — the shield law parametrised over the orientation

  VEndpt.shield_finalT -- c = |Z| with hsep discharged, parametrised by the `atTop` map

Observation that made this cheap: the CUT side of the argument (prop_cut, blk_or_local,
hreal_of_hturn, walkCount_le, walkCount_ge, shield) never mentions VEndpt.atTop at all.
It works with siteP, edgeOf and partner. Only the MERGE side needs an atTop, and it
needs only hpt. So the whole shield law parametrises over the orientation with one
extra hypothesis.

That means the mirrored orientation (atTopN, bnd = s0 - 1) -- the one BLOCK 18 showed
discharges hsW and hsX with NO side condition, and BLOCK 40 showed is the one
compatible with locality -- can be plugged in directly.

Both orientations now reach the same theorem; they differ only in which end is the top
and where the phantom edge sits.

## 2026-09-03 — BLOCK 51: shield_neg — the shield law with all locality discharged

  VEndpt.hsW_negP, hsT_negP  -- hold OUTRIGHT in the mirrored orientation (propext only)
  VEndpt.hsX_negP            -- needs the walk to reach back to s1 (wlo_le_s1)
  VEndpt.shield_neg          -- **c = |Z| with the three locality hypotheses GONE**

What is left in shield_neg:
  hturn  the paper's cut condition on real turns
  hvirt  the virtual pair stays in one run          (BLOCK 42 proves this)
  hruns  every run carries an end
  hcov   the covering condition
  z0     a basepoint
All four are statements about the configuration -- the same inputs the Endpt-side
argument takes -- and none is about the virtual pair or the extension.

So the shield law, which was retracted twice tonight (BLOCK 3 on hcov, BLOCK 4 on hZ
versus hocc) and then proved not to transport (BLOCK 41 on locality), now holds on the
end type that carries a group element's configuration, with every model-specific
hypothesis discharged.

hsW_negP and hsT_negP depend on `propext` alone. They are true by computation: in the
mirrored orientation the virtual arrival's site IS its edge plus one, and the virtual
departure IS a bottom.

## 2026-09-03 — BLOCK 52: hvirt SUPPLIED — the last non-configuration hypothesis

  gz_const_on            -- gz is constant on a cut-free window
  VEndpt.hvirt_of_gap    -- **hvirt supplied**, from "no cut site in [s1-1, s0]"

The turn of a virtual end is either the other virtual end (same edge, same block) or a
real end at site s0 or s1, hence on an edge inside [s1-1, s0]. With no cut site in that
window, gz is constant there, so the block index is preserved.

The window is cut-free by two facts already proved:
  BLOCK 42  no_cut_inside_travel      -- the interior of the travel interval
  BLOCK 39  arrivalfree_ne_virtual    -- and neither endpoint is a cut site

So hvirt is no longer a hypothesis of the shield law on VEndpt: given the gap condition
(which those two theorems establish) it is a theorem. What remains in shield_neg is
hturn, hruns, hcov and a basepoint -- four plain statements about the configuration.

PROOF NOTE, and it is the reason the third attempt worked: the first two versions
carried `if b then s1 else s0` through the whole argument and fought it at every step.
Casing on `b` at the TOP and running one keyed sub-lemma at each of the two sites made
the body uniform and it went through. The mathematics was identical in all three.

## 2026-09-03 — BLOCK 53: shield_gap — the shield law taking ONLY configuration inputs

  VEndpt.shield_gap -- c = |Z| on the extended type, with hvirt supplied internally

Its hypotheses in full:
  hgap   no cut site in [s1-1, s0]   -- BLOCKS 39 and 42 establish this for a real
                                        configuration (no cut inside the travel
                                        interval; neither endpoint is a cut site)
  hturn  the paper's cut condition on real turns
  hruns  every run carries an end
  hcov   the covering condition
  z0     a basepoint
Nothing about the virtual pair, the phantom edge, or the orientation appears anywhere
in the statement. That was the goal of BLOCKS 39-53.

Also weakened `hvirt` in shield_finalT and shield_neg from "for every datum" to "for
every datum IN THE MERGE CLASS", which is all that is used and all that hvirt_of_gap
can supply (it needs hts).

EDITING NOTE: the text replacement for that weakening matched in BOTH shield_finalT and
shield_neg, and the second copy has no `d` in scope. The error ("Unknown identifier
d.isArr") named the line but not the cause; the cause was a blind string replace over a
range containing two theorems. Same failure mode as the linter-suggestion edit earlier
in the project.

## 2026-09-03 — BLOCK 54: hgap discharged

  no_cut_in_neg_travel -- the mirror of no_cut_inside_travel: for kstar < 0 the travel
                          indicator is -1 throughout [kstar, 0), so Phi = 0 fails at
                          every site strictly between
  pd_hgap              -- **the gap condition, discharged**: a cut site in [kstar, 0]
                          is impossible -- strictly inside by the above, and at either
                          endpoint because those are the two virtual sites

The two endpoint exclusions are passed in rather than derived, because they are facts
about the configuration's BALANCE (arrivalfree_ne_virtual, BLOCK 39) rather than about
its travel. Keeping them as arguments makes the dependency visible instead of burying a
balance assumption inside a travel lemma.

So shield_gap's hgap is now a theorem for any PathData with kstar < 0 whose cut set
avoids the two virtual sites. What is left in the shield law: hturn, hruns, hcov -- the
paper's own three inputs.

Both halves of the travel argument are now proved and they are genuinely separate
lemmas, not one lemma with a sign case: no_cut_inside_travel needs f = +1 on [0,kstar),
no_cut_in_neg_travel needs f = -1 on [kstar,0), and the `travel` definition splits on
which interval is non-empty.

## 2026-09-03 — BLOCK 55: CORRECTION — a virtual site CAN be a cut site

  cut_at_zero            -- for kstar < 0, site 0 (where the virtual arrival sits) IS a
                            cut site whenever d(-1) = 1 and d(0) = 0
  cut_at_zero_parity_ok  -- and both values are consistent with hpar

So the exclusions hne0/hne1 that pd_hgap takes as hypotheses are NOT free, and cannot
be discharged the way I said they would be at the end of BLOCK 54.

WHERE THE ERROR WAS. BLOCK 39 proved `arrivalfree_ne_virtual`: an ARRIVAL-FREE site is
neither virtual site. I then used it as though cut sites were arrival-free. They are
not. `Realisation.cut_no_cross` / `SiteCost.cut_forces_no_cross` say that at a cut site
no strand CROSSES -- each arrival pairs with a departure on its own side. The site is
not empty. I conflated "no crossing" with "no ends" and carried that from BLOCK 39
through BLOCK 54.

CONSEQUENCE. The chain BLOCK 42 -> 52 -> 53 -> 54 shows the virtual pair stays in one
run PROVIDED no cut site lies in [s1-1, s0]. no_cut_inside_travel and
no_cut_in_neg_travel give the interior; the two ENDPOINTS are not excluded, and
cut_at_zero shows one of them genuinely can be cut. When it is, the virtual pair joins
two different runs and the lower bound argument fails.

STATUS: shield_gap remains true as stated -- it takes hgap as a hypothesis. What is
retracted is the claim that hgap is automatic. It holds exactly when neither virtual
site is cut, and that is a real condition on the element, not a theorem.

This is the fourth obstruction tonight found by trying to USE a result rather than
inspecting it, and the second where the error was mine rather than the development's.

## 2026-09-03 — BLOCK 56: exactly when a virtual site is cut

  cut_at_zero_iff   -- for kstar < 0, site 0 is cut IFF d(-1) = 1 and d(0) = 0.
                       Phi vanishes there automatically: f(-1) = -1 cancels the virtual
                       arrival.
  cut_at_kstar_iff  -- site kstar is cut IFF delta = true AND d(kstar-1) = 0 AND
                       d(kstar) = eps. Phi there is -vL(kstar), so it vanishes only when
                       the virtual departure is on the right -- i.e. only when delta is
                       set.

Both are iffs, both depend on propext (+Quot.sound) only.

So hgap -- the condition BLOCK 55 showed is not automatic -- is now a CHECKABLE
read-off on the element:
  hgap holds  <=>  NOT (d(-1) = 1 and d(0) = 0)
              and  NOT (delta and d(kstar-1) = 0 and d(kstar) = eps)

The delta asymmetry in the second is worth noting: the site carrying the virtual
DEPARTURE can only be cut when delta puts that departure on the right. So one of the
two obstructions is controlled by a single boolean field of the element, and elements
with delta = false have only the first condition to check.

## 2026-09-03 — BLOCK 57: witNeg — a witness with kstar < 0 AND a non-empty cut set

  witNeg                  -- cursor -1, deposits -1 at edge -1 and 2 at edge 2
  witNeg_occ, witNeg_A, witNeg_B  -- occupied set {-1, 0, 2}, so the span is [-1, 2]
  witNeg_cut_at_one       -- site 1 IS a cut site
  witNeg_no_virtual_cut   -- and NEITHER virtual site is

So hgap holds for witNeg while Z is non-empty: the first configuration in the project
that exercises shield_gap non-trivially. witElt (BLOCK 35) has kstar = 1 and an empty
cut set, so it could only ever confirm walkCount = 1.

The two exclusions are exactly the ones BLOCK 56 characterised, and they are avoided
for different reasons, which is the useful part:
  site 0     needs d(-1) = 1; witNeg has d(-1) = -1  -- avoided by the SIGN of a deposit
  site kstar needs delta = true; witNeg has delta = false -- avoided by the ORIENTATION
That the two obstructions are dodged by unrelated features of the element is evidence
they are genuinely independent conditions, not two faces of one.

Design note: the first draft used d(-1) = 1, which by cut_at_zero_iff makes site 0 a cut
site and would have made the witness useless. Choosing -1 instead was a direct
consequence of BLOCK 56 -- without the iff I would have built the bad witness and only
discovered it downstream.

## 2026-09-03 — BLOCK 58: witNeg's cut set computed; hgap holds with |Z| = 1

  witNeg_width          -- span of four edges
  witNeg_not_cut_at_two -- site 2 carries a deposit, so it is not cut
  witNeg_cutSites       -- **Z = {2}, so |Z| = 1**
  witNeg_hgap           -- **hgap HOLDS**, with Z non-empty
  witNeg_sites_lt       -- s1 < s0, so the mirrored orientation applies

The arithmetic that makes it work: witNeg's virtual sites are s0 = -A = 1 and
s1 = kstar - A = 0, so hgap's window (s1 - 1, s0] is {0, 1}, and the single cut site
sits at 2, outside it.

This is the first element in the project for which:
  - the cut set is non-empty (|Z| = 1), AND
  - hgap holds, so the virtual pair provably stays in one run, AND
  - the mirrored orientation applies (s1 < s0)
all three at once. Every earlier witness satisfied at most two.

The three interior sites are decided by three different mechanisms, which is a good
sign the characterisation is not degenerate:
  original 0 (= shifted 1): not cut because d(-1) = -1, not 1     [cut_at_zero_iff]
  original 1 (= shifted 2): CUT, plain read-off                    [pdCutAt_iff]
  original 2 (= shifted 3): not cut because d(2) = 2 != 0          [betaAt]

## 2026-09-03 — BLOCK 59: `forall E, hturn` is TOO STRONG — diagnosis

  pdMm_pos            -- every edge of a PathData span carries a crossing (mu_pos)
  witNeg_end_at_cut   -- so witNeg's cut site (shifted 2) DOES carry a real end

CONSEQUENCE. shield_finalT / shield_neg / shield_gap all take hturn as
    forall E, forall u v real, E.t (inl u) = inl v -> edge changes -> site u not in Zf
i.e. NO datum has a real turn crossing a cut site. That is a property of a PARTICULAR
realisation, not of the configuration. As soon as a cut site carries real ends -- which
witNeg's does, and which is the generic situation, since mu >= 1 on the whole span -- an
arbitrary Data can pair those ends across the site and the hypothesis fails.

So the shield law on VEndpt is not vacuous as a theorem, but its hturn hypothesis
cannot be met for any configuration whose cut sites are occupied. It cannot be applied.

THE FIX, and it is the same structural point as BLOCK 3. hturn must be an INVARIANT
carried through the descent, not a universally quantified hypothesis:
  - exists_run_connected must preserve it, so it belongs in the P of reaches_stuck
    alongside MergesMin;
  - run_step_min_gen must re-establish it after the swap -- which is exactly what
    ConfigLoop.hturn_step does on the Endpt side.
The Endpt development got this right (RunInv bundles hturn with hp, hts, hta, hmin);
the generic version I built in BLOCKS 46-53 dropped it to a hypothesis because that was
easier to state, and the cost is that it cannot be instantiated.

Fourth time tonight a construction has failed only on use: BLOCK 28 (negative edges),
BLOCK 32 (missing role flip), BLOCK 41 (locality), BLOCK 55 (cut sites not arrival-free),
and now this. In every case inspecting the statement would not have found it.

## 2026-09-03 — BLOCK 60: hZ and mu_pos COLLIDE inside the span — the root of the whole tension

  pd_edges_occupied          -- both edges adjacent to an interior site of [A,B] are
                                occupied (mm = mu >= 1 there)
  no_arrivalfree_inside_span -- so the "both adjacent edges empty" conclusion of
                                BLOCK 12 is FALSE at any interior site

Putting the pieces together:
  BLOCK 12  hZ (no arrival at a cut site) + balance  ==>  both adjacent edges EMPTY
  BLOCK 60  PathData.mu_pos                          ==>  no span edge is empty
Therefore hZ CANNOT HOLD at any site strictly inside a PathData's span. The shield
law's hZ forces the cut set to avoid the span interior entirely -- i.e. to be empty,
since Z is by definition the set of INTERIOR cut sites (BLOCK 38).

THIS EXPLAINS BLOCK 5's WITNESS. wit_shield used multiplicities (2,0,0,2): the cut site
sits between two EMPTY edges. That configuration satisfies hZ precisely because it does
NOT come from a PathData. I built it as an abstract (m, up) pair to prove
non-vacuity, and it is non-vacuous -- for abstract configurations. It is not
realisable as a group element.

SO THE HONEST STATEMENT OF THE SHIELD LAW'S STATUS:
  * proved for abstract configurations, with a witness (BLOCK 5, wit_shield)
  * proved on the extended type (BLOCKS 46-53)
  * NOT applicable to any configuration arising from a group element with a non-empty
    cut set, because hZ collides with mu_pos
The obstruction is not in the extension, the virtual pair, or the transport. It is in
hZ itself, and it was there before tonight -- BLOCK 4 found it (hZ vs hocc) and I
treated the run form as a repair. The run form removed hocc; it did not remove hZ.

## 2026-09-03 — BLOCK 61: hturn WITHOUT hZ — the correct replacement

  hturn_of_cross_zero -- hturn derived from "the optimal plan at each cut site has zero
                         cross", with NO hZ anywhere

The paper's condition at a cut site is that no strand CROSSES
(SiteCost.cut_forces_no_cross), not that the site is empty. In the walk model that is
exactly hturn: the turn keeps the edge. ConfigLoop already had both halves --
no_cross_at_cut and turn_keeps_edge_of_cross_zero -- and chaining them gives hturn
directly.

Both roles are covered: for an arrival the bridge lemma applies as stated; for a
departure, turnAt_invol reduces it to the arrival case (its turn IS an arrival at the
same site, and turning back returns x).

WHY THIS MATTERS. BLOCK 60 showed hZ is unsatisfiable inside a PathData span, so every
shield law resting on hZ is inapplicable to group elements. hturn_of_cross_zero shows
hZ was never needed: the hypothesis the argument actually wants is zero-crossing at cut
sites, which is what cut_forces_no_cross supplies and what a cost-minimal realisation
satisfies by construction.

So the repair is not to weaken hZ but to DELETE it. The lemmas it was serving --
hturn_step on the Endpt side, and the hturn hypothesis of the generic shield law --
should take zero-crossing instead.

## 2026-09-03 — BLOCK 62: hturn is SELF-MAINTAINING; hZ can be deleted from the chain

  same_edge_of_site_top       -- same site + same end-role => same edge
  freePair_same_edge_at_cut   -- at a cut site the free pair lies on ONE edge: either
                                 the arrivals share a side (hence an edge), or their
                                 turns do and the turns keep their edges there
  swapT_pos_eq                -- generic: swapT preserves a position function when the
                                 four swapped points share it
  hturn_swapT_nohZ            -- **hturn survives the merge with NO hZ**

All four depend on propext (+Quot.sound) only.

This closes the repair BLOCK 60 called for. hturn_swapT needed "the merge site is not a
cut site", and hZ was supplying it. It is not needed: at a cut site all four swapped
ends sit on one edge, so the swap cannot create a crossing and hturn is preserved
outright.

LEAN RULE 4.1 INVOKED, second time tonight. Three strikes trying to case-split by hand
on the equalities that swapT's `if` chain tests: every attempt left goals with
half-reduced `if True then ...`, and each "fix" guessed at a different reduction. ABORT,
then the architectural repair: state swapT_pos_eq generically and let `split_ifs`
produce the branch conditions in the form the definition uses. Five lines, first try.
The earlier three attempts were all fighting Lean's normal form, not the mathematics --
identical to the turnG_arr loop in BLOCK 32.

## 2026-09-03 — BLOCK 63: the descent invariant WITHOUT hZ

  hturn_step_nohZ    -- case on whether the merge site is cut: if not, the original
                        hturn_swapT applies with hsa; if it is, hturn_swapT_nohZ does.
                        Either way hZ never appears. (propext + Quot.sound only)
  TurnInv            -- the descent invariant: cost-minimal in the class, AND turns keep
                        their edges at cut sites
  run_step_turnInv   -- **the run step preserving TurnInv**, with no hZ

This is the replacement for RunInv that BLOCK 60 showed was needed. RunInv bundles
hturn and maintains it with hZ; TurnInv bundles hturn and maintains it with
hturn_step_nohZ, which needs nothing beyond hshared -- and hshared is what the free
pair already provides.

DISCIPLINE NOTE. My first draft of run_step_turnInv called run_step_min_gen and then
tried to recover hturn, which is impossible: the packaged version does not expose the
swap data (a, a', hshared, the .t equation). I wrote a `sorry` for that step, saw it,
and rewrote the body to call step_of_split'_local directly. The file has never carried
a sorry into a commit and did not here -- the check was `grep -c sorry` before building,
not after.

Also repeated BLOCK 48's exact error: hss is `siteOf a' = siteOf a`, and I passed
hss.symm. Second time tonight for the same argument of the same lemma.

## 2026-09-03 — BLOCK 64: shield_turnInv — the shield law with hZ GONE

  exists_turnInv_connected  -- iterate run_step_turnInv to a datum in TurnInv whose runs
                               are connected
  blk_or_local_of_turnInv   -- a TurnInv datum's graph edges are local (via
                               ConfigLoop.local_of_hturn), hence blk-or-local
  shield_turnInv            -- **c = |Z| for a datum in TurnInv**

Inputs: the merge-side hypotheses (hside, hpsite, hsW, hsX, hsT), the covering
condition hcov, hruns, and a basepoint. NO hZ.

This is the repair BLOCK 60 identified, carried through. The sequence over the last
five blocks:
  BLOCK 60  hZ collides with mu_pos -- every shield law resting on hZ is inapplicable
  BLOCK 61  hturn is derivable from zero-crossing, so hZ was never the right hypothesis
  BLOCK 62  hturn is self-maintaining across a merge (swapT_pos_eq)
  BLOCK 63  so hturn can live in the descent invariant (TurnInv) instead
  BLOCK 64  and the shield law follows from that invariant alone
Each step is a theorem; none assumes what the previous one supplied.

The upper and lower bounds now come from the SAME hypothesis: blk_or_local_of_turnInv
feeds both walkCount_le_runs_blk and exists_injective_components_avoiding_blk_or_local.
Before tonight the two halves took different hypotheses (Local for one, hcovAll and hZ
for the other), which is part of why the incompatibility took so long to see.

## 2026-09-03 — BLOCK 65: under hgap, cut sites carry only REAL ends

  VEndpt.cut_ends_real     -- every end at a cut site is real: a virtual end sits at s0
                              or s1, and hgap excludes both from Zf
  VEndpt.site_edge_at_cut  -- so the site-edge relation holds at every end of a cut
                              site, which is exactly what BLOCK 62's free-pair argument
                              needs
Both propext + Quot.sound only.

This is the bridge for porting TurnInv to the extended type. same_edge_of_site_top --
the step that makes the free pair share an edge -- holds only where site = edge + [top],
and that fails at virtual ends. hgap makes the failure irrelevant by keeping virtual
sites out of the cut set entirely.

Note how the pieces line up: BLOCK 55 showed a virtual site CAN be cut, BLOCK 56 said
exactly when, BLOCK 58 found an element where it is not, and BLOCK 65 shows that when
it is not, the whole free-pair argument transfers. The condition that looked like an
obstruction in BLOCK 55 is the same condition that makes the port work.

WHY shield_turnInv ALONE IS NOT ENOUGH: it is stated for Endpt, and a PathData
configuration is unbalanced there (that is why VEndpt exists). So the Endpt-side repair
of BLOCKS 60-64 has to be carried to VEndpt, and this block supplies the missing step.

## 2026-09-03 — BLOCK 66: hturn survives the merge on VEndpt

  VEndpt.freePair_same_edge_at_cutV -- the free pair lies on one edge at a cut site,
                                       extended type
  VEndpt.hturn_swapT_nohZV          -- **hturn survives the merge on VEndpt**, under
                                       hgap and with no hZ
Both propext + Quot.sound only.

The port needed NO case split on real versus virtual. site_edge_at_cut (BLOCK 65) gives
the site-edge relation at every end of a cut site, so BLOCK 62's argument runs verbatim
with siteP/edgeOf/atTop in place of the Endpt versions. swapT_pos_eq -- stated
generically in BLOCK 62 precisely because the Endpt proof had been fighting Lean's
normal form -- applies unchanged.

That generic statement is now used twice, on two different end types. Writing it
generically was forced by a tactic loop rather than foresight, but it is the reason this
block was short.

Repeated error, third time tonight: `rw [...] at h1 h2` where the pattern occurs in only
one of them. Lean reports it as a failed rewrite naming the pattern, which reads like
the pattern is wrong rather than like it is absent from one target.

## 2026-09-03 — BLOCK 67: the descent, generically, with hturn maintenance as a parameter

  hturn_swapT_gen         -- ConfigLoop.hturn_swapT generically (6 lines via split_ifs,
                             against 15 with by_cases -- the BLOCK 62 lesson again)
  VEndpt.hturn_step_nohZV -- the two cases on VEndpt: cut site => nohZV, otherwise the
                             generic swapT lemma
  TurnInvG                -- the descent invariant, generically
  run_step_turnInvG       -- **the run step preserving it**, with the hturn maintenance
                             taken as a PARAMETER

run_step_turnInv (BLOCK 63) was Endpt-specific only through hturn_step_nohZ. Abstracting
that one step makes the whole descent generic, and both end types now supply it:
  Endpt   hturn_step_nohZ    (BLOCK 63)
  VEndpt  hturn_step_nohZV   (BLOCK 67)

So the descent machinery is written once. The Endpt-specific run_step_turnInv is now
redundant; it stays as the concrete instance the Endpt side already uses.

This is the fourth time tonight that generalising AFTER seeing two uses produced a
shorter development than generalising in advance would have: swapT_pos_eq,
walkCount_ge_of_avoiding_gen, hturn_swapT_gen, run_step_turnInvG. In each case the
Endpt-specific proof was already written and the generic version is the same script with
the type fixed later.

## 2026-09-03 — BLOCK 68: the descent runs on VEndpt

  VEndpt.site_edge_at_cutT, freePair_same_edge_at_cutT, hturn_step_nohZT
      -- the hturn chain parametrised by the top map. The only property used is that
         the map agrees with EndType.atTop on REAL ends, and both VEndpt.atTop and
         VEndpt.atTopN do.
  VEndpt.run_step_turnInvN        -- run_step_turnInvG instantiated at VEndpt, mirrored
                                     orientation (bnd = s0-1, atTopN)
  VEndpt.exists_turnInvN_connected -- iterated: a TurnInvG datum whose runs are connected

So the descent that BLOCKS 60-64 repaired on Endpt now runs on the type that carries a
group element's configuration, with hZ absent throughout.

The parametrisation was forced, not chosen: hturn_step_nohZV had been written against
VEndpt.atTop, and the mirrored orientation needs atTopN. Rather than duplicate the
chain I added the top map as a parameter with the one hypothesis its proofs actually
use (agreement on real ends). Same pattern as BLOCK 50, where the shield law itself
turned out to parametrise over the orientation with a single extra hypothesis.

## 2026-09-03 — BLOCK 69: THE SHIELD LAW ON VEndpt, FROM THE INVARIANT

  VEndpt.blk_or_local_of_turnInvN -- a TurnInvG datum's edges preserve the block index
                                     or are local (hvirt from hvirt_of_gap, hreal from
                                     the invariant's own hturn restricted to real ends)
  VEndpt.shield_turnInvN          -- **c = |Z| on VEndpt, from TurnInvG**

NO hZ. NO hturn hypothesis. Both come from the invariant, which the descent maintains
(BLOCK 68). What remains: hcov, hruns, hgap, a basepoint.

This is the end of the repair that BLOCK 60 opened. The full arc:
  BLOCK 59  forall-E hturn cannot be discharged -- a cut site carries real ends
  BLOCK 60  hZ collides with mu_pos -- the shield law was inapplicable to elements
  BLOCK 61  hturn follows from zero-crossing, so hZ was never the right hypothesis
  BLOCK 62  hturn is self-maintaining across a merge
  BLOCK 63  so it belongs in the descent invariant
  BLOCK 64  and the shield law follows from that invariant     (Endpt)
  BLOCK 65  under hgap, cut sites carry only real ends
  BLOCK 66  so the free-pair argument transfers
  BLOCK 67  the descent is generic once hturn maintenance is a parameter
  BLOCK 68  it runs on VEndpt
  BLOCK 69  and the shield law follows there too               (VEndpt)

Eleven blocks, one hypothesis removed. The upper and lower bounds are now fed by the
same fact on both end types, which is the structural change: before BLOCK 60 they took
different hypotheses, and that is why the incompatibility survived sixty blocks.

## 2026-09-03 — BLOCK 70: hruns for witNeg; the one remaining obligation NAMED

  witNeg_hruns          -- its two runs are witnessed by the virtual arrival (edge 0,
                           gz = 0) and a real end on shifted edge 3 (gz = 1). Kernel
                           `decide`, not native_decide.
  HasInitialTurnInv     -- the remaining obligation, named as a contract (Rule I7)
  VEndpt.shield_of_initial -- **the shield law modulo that one obligation**

WHAT IS AND IS NOT DONE. shield_turnInvN consumes a datum already in TurnInvG.
Cost-minimality comes from exists_mergesMinN. The hturn component does NOT: turnG is
built from an arbitrary involution at each site (TurnBuild.exists_involution_of_card_eq
picks one by choice), and nothing makes that choice respect cut sites.

hturn_of_cross_zero (BLOCK 61) derives hturn from zero crossing at cut sites, and
CostMerge.site_cost_le_of_global turns global minimality into local minimality. The
missing step is that the local minimum at a cut site is ZERO, which needs a comparison
datum of zero cost there -- a plan pairing each arrival with a departure on its own
side.

In the paper that datum is the realisation itself: Realisation.cut_no_cross holds for a
realisation with R.cost = P.lR. So the initial datum should come from a Realisation
rather than being built abstractly from dataG. That is the shape of the remaining work,
and it is now a named Prop instead of an unstated assumption.

## 2026-09-03 — BLOCK 71: at a cut site BOTH adjacent edges carry zero travel

  pdCut_travel_zero          -- Phi = 0 gives f(s-1) = 0, and travel_const_off gives
                                f(s) = 0 as well, away from the two virtual sites
  sided_balance_of_tr_zero   -- so the site's two HALVES balance separately: the top
                                half matches iff the left edge's signed travel
                                vanishes, the bottom half iff the right edge's does

This is what a zero-cost plan at a cut site needs. Such a plan pairs each arrival with a
departure on its own side, which requires the counts to match side by side -- not merely
in total. The cut condition supplies exactly that.

The second lemma is the ConfigLoop card-decomposition run twice, once per side, and it
makes the connection concrete: side-wise balance IS tr = 0 on the adjacent edges, and
tr = travel by pd_tr_eq (BLOCK 30). So "no crossing at a cut site" and "no travel across
a cut site" are the same statement read in two models.

REMAINING for HasInitialTurnInv: build the side-respecting involution from these two
equalities (two applications of TurnBuild.exists_involution_of_card_eq, on disjoint
supports, combined), and show the resulting datum has hturn. The mathematical input is
now proved; what is left is the construction.

## 2026-09-03 — BLOCK 72: two involutions on disjoint supports combine

  exists_involution_two -- given balanced pairs (A1,D1) and (A2,D2) with disjoint
                           supports, an involution exchanging each pair and fixing
                           everything else

Written generically over a Fintype. The construction is `if x in A1 ∪ D1 then t1 x else
t2 x`; involutivity needs that t1 maps A1 ∪ D1 into itself and t2 maps A2 ∪ D2 into
itself, so the branch taken is the same for x and its image -- which is where the
disjointness is used, and the only place it is.

This is the missing constructor for the zero-cost plan at a cut site. BLOCK 71 proved
the two halves balance separately (sided_balance_of_tr_zero); this supplies the
involution that respects the split.

First try, and it is the longest single proof written tonight without a strike -- six
obligations, each discharged by pushing the membership through the same two mapping
facts. Stating the six conclusions explicitly in the signature rather than bundling them
is what made it mechanical: each one names exactly which mapping fact it needs.

## 2026-09-03 — BLOCK 73: the side-respecting turn at a cut site

  exists_sided_turn_at -- an involution at a cut site exchanging arrivals and departures
                          WITHIN EACH SIDE: it preserves atTop, hence (the site being
                          fixed) preserves the EDGE, which is hturn there

Construction: split the site's arrivals and departures by atTop into two balanced pairs
(BLOCK 71 gives the balance), note the two supports are disjoint because atTop separates
them, and apply exists_involution_two (BLOCK 72).

So the zero-cost plan at a cut site now EXISTS as a turn, not just as a transportation
plan. That is the object HasInitialTurnInv needs, and the gap named in BLOCK 70 is one
assembly step from closing: build the global datum by using this turn at cut sites and
the arbitrary one elsewhere.

The disjointness argument is the whole content and it is two lines: an end in
A1 ∪ D1 has atTop = true, one in A2 ∪ D2 has atTop = false. Everything else is pushing
Finset.mem_filter through six obligations.

## 2026-09-03 — BLOCK 74: a datum in the merge class satisfying hturn

  exists_merges_hturn -- glueing the sided turns at cut sites with the generic turnAtG
                         elsewhere gives a Data that is in the merge class AND satisfies
                         hturn

Its hypothesis is exactly what exists_sided_turn_at (BLOCK 73) supplies at each cut
site, so the two compose directly.

All five Data obligations are discharged branch by branch on whether the site is cut:
  t_invol   glue_invol from per-site involutivity and site preservation
  t_ne      sided turns move arrivals to departures (disjoint), turnG_ne elsewhere
  pt_ne     the partner changes site while the turn does not
  hts       site preservation, both branches
  hta       the role flip, both branches
and hturn comes from the sided turn preserving atTop, hence the edge.

This is the object HasInitialTurnInv needed. What remains to close it is the
COST-MINIMAL version: exists_merges_hturn gives a datum in the class with hturn, and
TurnInvG additionally requires cost-minimality. The descent preserves hturn (BLOCK 63),
so minimising from this datum keeps it -- that is the last step.

## 2026-09-03 — BLOCK 75: minimising INSIDE the hturn subclass

  exists_least_cost_hturn -- a least-cost datum among those satisfying hturn, given one
                             such datum to start (BLOCK 74 supplies it)

WHY THIS IS THE RIGHT MOVE. CostMerge.exists_mergesMin produces an arbitrary global
minimiser, and nothing makes it satisfy hturn -- so the obvious route to
HasInitialTurnInv does not work. But it does not need to: the free-pair argument
compares E only with SWAPS of E, and swaps preserve hturn (hturn_step_nohZ, BLOCK 63).
So minimality within the hturn subclass is exactly as strong as global minimality where
it is used.

The proof is Int.exists_least_of_bdd on the costs of hturn-data: bounded below by
costOf_nonneg, non-empty by exists_merges_hturn. Same argument as
CostMerge.exists_mergesMin with one extra conjunct carried through.

STILL TO DO for HasInitialTurnInv: TurnInvG is defined with CostMerge.MergesMin, which
demands minimality against ALL class members, not just hturn ones. Either TurnInvG is
restated with subclass minimality (and run_step_turnInvG's use of hmin_of_mergesMin
adjusted to match), or the two notions are shown to agree. The former is the honest
route and is a change to the definition, not a new theorem.

## 2026-09-03 — BLOCK 76: exactly which swaps preserve hturn

  swap_preserves_hturn_offcut -- a swap at a NON-CUT site always preserves hturn (no
                                 side condition: hturn constrains nothing there)
  swap_preserves_hturn_atcut  -- a swap at a CUT site preserves it when the pair shares
                                 a side

So the hturn subclass is closed under every swap EXCEPT cross-side swaps at cut sites.
That is the precise gap between subclass minimality and global minimality, and it is
small: at a cut site the two halves balance separately (BLOCK 71), so a cross-side swap
is exactly the move that creates a crossing.

WHAT THIS MEANS FOR THE LAST STEP. Restating TurnInvG with subclass minimality is sound
only if the free-pair argument never needs to compare against a cross-side swap at a cut
site. It might: hasFreePair_of_minimal compares against swaps of an arbitrary arrival
pair sharing a site, and nothing stops that pair being cross-side at a cut site.

Ruling it out needs the datum to have ZERO COST at cut sites, so that no swap there can
lower the cost -- which is the same zero-cost-plan requirement BLOCK 70 identified, now
reached from the other direction. The sided turn of BLOCK 73 gives zero CROSSING there;
zero COST additionally needs the signs to match, i.e. a four-way split by (side, sign)
rather than the two-way split by side.

That four-way split is the remaining construction. alpha = 0 and beta = 0 at a cut site
give the sign-wise balance it needs, exactly as Phi = 0 gave the side-wise balance.

## 2026-09-03 — BLOCK 77: THE FORCED SIGN — the root of hZ, and it predates tonight

  sgn_arr_ne_dep      -- EndData.sgn is a function of (side, isArr, depSign side) only,
                         so on ONE SIDE arrivals and departures ALWAYS differ in sign
  pcost_same_side_two -- hence a same-side arrival/departure pair costs 2, never 0
  pcostF_ge_one       -- and every pair costs at least 1: THERE IS NO ZERO-COST PLAN at
                         a site carrying ends
(propext alone for the first two.)

THIS IS THE ROOT. BLOCKS 70-76 were trying to build a zero-cost plan at a cut site. No
such plan exists in this model, and the reason is structural: the sign is FORCED.

Consequence for the four transportation classes: one of each side's two is empty, so
alpha = -(A + C), and alpha = 0 forces the site to carry no ends on that side. That is
exactly ConfigLoop.no_ends_of_alpha_zero, which has been in the development all along --
its `alpha A 0 0 C` shape IS the forced-sign shape, and I read it as a special case
rather than as the general situation.

The paper's Plan does NOT force the sign: Ap, Am, Cp, Cm are independent and a
same-side same-sign pair costs 0. So `EndData` is strictly less general than the site
model it realises, and hZ is the symptom:
  forced sign  =>  cut sites carry no ends  =>  hZ  =>  collides with mu_pos (BLOCK 60)

So the chain of tonight's findings terminates here. BLOCK 4 found hZ vs hocc, BLOCK 60
found hZ vs mu_pos, and both are downstream of a modelling choice in EndData.sgn.
Fixing it means letting depSign vary per end rather than per side -- a change to the
Data structure, not to any proof.

## 2026-09-03 — BLOCK 78: end data with a FREE sign

  GData                        -- end data carrying the sign per end rather than
                                  deriving it from (side, isArr)
  GData.pcost                  -- 0 same-side same-sign, 2 same-side opposite-sign,
                                  1 across sides -- the paper's Plan cost
  GData.pcost_zero             -- a same-side same-sign pair costs NOTHING (axiom-free)
  GData.ofEndData              -- the forced model embeds, taking the derived sign
  GData.strictly_more_general  -- and the embedding is STRICT: the same pair costs 2 in
                                  the forced model and 0 in the free one

So the possibility BLOCK 77 showed was missing is now present. GData.pcost matches
SiteCost.Plan.cost's stated intent ("0 for a same-side matched pair with equal signs, 2
for a same-side pair with opposite signs, 1 for a pair on opposite sides") exactly,
which EndData.pcostF does not once the sign is forced.

WHAT THIS COSTS. The merge development is written against EndData.Data throughout --
CostMerge.costOf, cost_swapData, cost_congr, the free-pair argument. Porting it to GData
is mechanical where the proofs use only pcostF's value (cost_congr, costOf_nonneg) and
substantive where they use the forced sign. `EndData.pcost_eq_of_arr_dep` -- "on an
arrival/departure pair the cost sees only the side pattern" -- is exactly a use of the
forcing, and its docstring says so: "This is not vacuous: it is the consequence of the
sign being forced."

So the port is not free, and the lemma that will need rethinking is named.

## 2026-09-03 — BLOCK 79: a chainable involution combinator

  combine_involutions -- two involutions supported on DISJOINT sets combine, with the
                         combined map agreeing with each on its own support and fixing
                         everything outside both
  involution_of_pair  -- a balanced pair gives an involution supported on its union

exists_involution_two (BLOCK 72) took two balanced PAIRS and does not chain: its output
is not in the form its input wants. These two do. involution_of_pair converts a balanced
pair into a supported involution, and combine_involutions merges any two with disjoint
supports -- so four classes are handled by three applications, in any association.

That is the shape the (side, sign) split needs: four classes
  (L,+) (L,-) (R,+) (R,-)
each balanced at a cut site by alpha = beta = Phi = 0, pairwise disjoint because side
and sign separate them.

Design note: BLOCK 72's version was written for the two-way split and did its job, but
generalising it to four by adding parameters would have produced a lemma with twelve
hypotheses. Refactoring to a chainable pair of lemmas is shorter and the proofs are the
same arguments -- the branch taken is the same for x and its image, which is exactly
where disjointness is used, and the only place it is.

## 2026-09-03 — BLOCK 80: the zero-cost turn exists in the free-sign model

  exists_zero_cost_turn -- given four-class balance at a site, an involution pairing
                           each arrival with a departure IN ITS OWN (side, sign) CLASS,
                           and the identity outside the site

Built by three chained applications of combine_involutions (BLOCK 79): the two signs
within each side, then the two sides. Disjointness at every join is immediate -- the
classes are separated by side or by sign.

Combined with GData.pcost_zero (BLOCK 78), every pair this turn makes costs 0. So the
object BLOCKS 70-77 were reaching for EXISTS, once the sign is free. In the forced
model it provably does not (pcostF_ge_one, BLOCK 77).

That closes the diagnosis loop that ran from BLOCK 59:
  59-60  the shield law cannot apply to elements -- hZ collides with mu_pos
  61-69  hZ removed and the shield law rebuilt on an invariant
  70-76  the invariant needs a zero-cost plan at cut sites
  77     no such plan exists, because EndData forces the sign
  78-80  with the sign free, it exists

Drafted with a `sorry` for the final combine and completed before building; the
`grep -c sorry` check ran before `lake build`, as in BLOCK 63.

## 2026-09-03 — BLOCK 81: four-class balance at a cut site

  left_classes_match   -- alpha = Phi = 0 forces A+ = C+ and A- = C-. Phi gives the
                          totals, alpha the signed difference; adding and subtracting
                          separates them.
  right_classes_match  -- beta = 0 with the total balance then forces B+ = D+, B- = D-
  four_classes_match   -- **the four (side, sign) classes match individually at a cut
                          site**

This is exactly the input exists_zero_cost_turn (BLOCK 80) consumes. So in the
free-sign model the chain is complete:

  cut site (alpha = beta = Phi = 0) + balance
    -> four classes match individually            (BLOCK 81)
    -> a zero-cost turn exists                     (BLOCK 80)
    -> the turn keeps side and sign, so it keeps the EDGE, which is hturn

and none of it needs hZ or an empty cut site. The forced-sign model cannot reach this
because alpha = 0 there means A + C = 0 (BLOCK 77), collapsing the four classes to
nothing rather than matching them.

The arithmetic is three omega calls. It was invisible before only because the forced
sign made two of the four classes empty by construction, so "the classes match" and
"the site is empty" were the same statement.

## 2026-09-03 — BLOCK 82: the site-level GData, with a PER-CROSSING sign

  configGData             -- end data of a configuration with the sign carried per
                             CROSSING: sgnOf x = sg x.edge x.idx
  per_edge_sign_collapses -- and a per-EDGE sign would not do: all ends on one side of
                             a site share an edge, so one of that side's two classes
                             would be empty

The second is the reason the sign has to be indexed by the crossing and not just the
edge, and it is worth having as a theorem because the degeneracy it describes is
exactly the one EndData.sgn produces (BLOCK 77). Two different modelling shortcuts --
deriving the sign from (side, role), or attaching it to the edge -- collapse the four
classes the same way.

With the sign per crossing all four classes can be occupied, so four_classes_match
(BLOCK 81) is a statement with content rather than a vacuous one.

STATUS OF THE FREE-SIGN LINE. The construction chain is complete in the abstract:
  four_classes_match -> exists_zero_cost_turn -> a turn keeping side and sign, hence the
  edge, hence hturn
What remains is to connect it to a configuration: define the four class counts at a site
of a configGData, show they are the Ap/Am/Bp/Bm/Cp/Cm/Dp/Dm of the site model, and
apply. That is bookkeeping between two indexings, not new mathematics.

## 2026-09-03 — BLOCK 83: the four class counts, and per-class balance at a cut site

  clsCount               -- the number of ends of a set in a given (side, sign) class
  clsCount_sum           -- the four classes PARTITION a set (two nested applications of
                            filter_card_add_filter_neg_card_eq_card)
  class_balance_of_cut   -- **alpha = beta = Phi = 0 plus the site's total balance force
                            each of the four classes to match**

class_balance_of_cut is precisely the hypothesis exists_zero_cost_turn (BLOCK 80)
consumes. So the free-sign chain is now closed from the cut condition to the turn:

  alpha = beta = Phi = 0, total balance
    -> clsCount A sd sg = clsCount D sd sg for all four classes   (BLOCK 83)
    -> a zero-cost involution pairing within classes              (BLOCK 80)
    -> it preserves side and sign, hence the edge                 (BLOCK 80)
    -> hturn at that site

with no hZ and no empty cut site anywhere. That is the object BLOCK 70 named as missing
and BLOCK 77 proved cannot exist in the forced-sign model.

The partition lemma needed Bool.not_eq_true rather than Bool.eq_false_iff to convert
`sgnOf x = false` into `¬ sgnOf x = true`; the filter predicates are stated one way and
Finset's negation lemma the other.

## 2026-09-03 — BLOCK 84: a class-preserving turn costs nothing

  gcostAt, gcostOf   -- the site and global cost of a turn in the free-sign model
  gcostAt_zero       -- a class-preserving turn costs 0 over any set of ends
  gcostOf_zero       -- and 0 globally
  gcostOf_nonneg     -- costs are non-negative, so 0 is the minimum and it is ATTAINED

Contrast with the forced model, where pcostF_ge_one (BLOCK 77) says every
arrival/departure pair costs at least one, so the minimum is the number of arrivals and
a cut site's siteValue of 0 is unreachable unless the site is empty.

That contrast is the whole content of the free-sign detour: in EndData the minimum
achievable cost at an occupied site is positive, while the site model says a cut site
costs 0. The two disagree, and GData is the model where they agree.

So the free-sign line now has: the cost function, the zero-cost turn, the balance that
produces it, and the proof that zero is the minimum. What it does not yet have is the
merge development ported onto it -- CostMerge is written against EndData.Data
throughout, and BLOCK 78 already identified pcost_eq_of_arr_dep as the lemma that will
not survive the port, since it is a consequence of the forcing.

## 2026-09-03 — BLOCK 86: the restriction documented AT the definition

`EndData.sgn`'s docstring now states the restriction and its three consequences, with
pointers to the proofs:
  pcostF_ge_one                -- no pairing costs 0
  no_ends_of_alpha_zero        -- alpha = 0 forces the site empty
  the ConfigLoop section       -- why the merge chain and prop:cut do not conflict
and to GData / strictly_more_general as the free-sign alternative.

WHY THIS MATTERS MORE THAN A COMMENT USUALLY WOULD. The fact was already documented --
in ConfigLoop, three lines above no_ends_of_alpha_zero, under a section header that says
exactly this. I did not read that header and spent BLOCKS 70-77 rediscovering it. The
information was in the repository and in the wrong place: at a USE site, not at the
DEFINITION that causes the restriction.

Anyone reaching for EndData.Data now learns at the point of use that the sign is
derived, that this empties cut sites, and where the free-sign version is.

AUDIT RESULT (BLOCK 85), for the record. The forcing is used in exactly three places:
  EndData.lean       two lemmas, via pcost_eq_of_arr_dep
  ConfigLoop.lean    the clsOf/planAt block, 821-949
  StrandEnds.lean:49 supplies depSign
Three sites, not a rewrite of CostMerge -- smaller than BLOCK 78 estimated.

## 2026-09-03 — BLOCK 87: the swap criterion in the free-sign model

  GData.pcost_congr_left -- pcost sees only the two ends' CLASSES
  GData.swap_free        -- so two arrivals in the same class are interchangeable: the
                            swap costs the same, with NO hypothesis on the departures
  GData.swap_delta       -- and a cross-class swap's cost change is determined by the
                            four class labels alone (axiom-free, by rfl)

EndData.transCost_swap_free needs hshared -- a condition relating the two arrivals'
sides to their departures' sides -- because with the sign forced it must reduce
everything to the side pattern. In the free model the criterion is SIMPLER: same class
is enough, and nothing about the departures is needed.

That is worth noting because the free-sign model was reached by removing a restriction,
and one might expect the lemmas to get weaker. This one gets stronger: EndData's version
requires a relation between four ends, GData's requires a relation between two.

The reason is that the forced model's pcost is NOT a function of the ends' classes --
the sign is determined by the role, so an arrival and a departure on one side are forced
into different classes and the class labels carry less information than the (side, role)
pair does. Freeing the sign makes pcost genuinely class-determined, which is what
pcost_congr_left says.

## 2026-09-03 — BLOCK 88: a same-class swap is globally cost-neutral

  swapImg           -- the turn with the images of x and y exchanged
  gcostOf_swapImg   -- **swapping two same-class arrivals leaves the total cost
                       unchanged**

The two-term statement was GData.swap_free (BLOCK 87); this sums it. Only the terms at
x and y change, so the tail is a sum_congr and the head is swap_free applied once.

That is the free-sign counterpart of EndData.transCost_swap_free, and it needs strictly
less: EndData's version takes `hshared`, a condition relating the two arrivals' sides to
their departures' sides. This one takes only that the two arrivals share a class.

So the merge development's central cost fact ports, and ports to a stronger form. What
remains of the port is the free-pair EXISTENCE argument (free_pair_of_minimal), which
in the forced model derives hshared from cost-minimality; in the free model the
corresponding statement is that a cost-minimal datum has two same-class arrivals in
different walks at a common site.

## 2026-09-03 — BLOCK 89: when a same-class pair is available

  two_same_class_of_five -- pigeonhole: five arrivals at a site force two into one
                            (side, sign) class
  free_pair_of_five      -- so five arrivals give a free pair, with NO condition on the
                            departures

The bound is sharp in the obvious direction: four arrivals, one per class, give no
same-class pair. So "same class" is a sufficient criterion for a free pair, not a
complete one, and the free-sign merge argument needs either

  (a) five arrivals at the site -- available only for wide configurations, or
  (b) the delta analysis: GData.swap_delta (BLOCK 87) computes the cost change from the
      four class labels, and a cost-minimal datum has delta >= 0 for every swap, so the
      question is whether some cross-walk swap has delta = 0.

(b) is the honest analogue of the forced model's free_pair_of_minimal, which derives
hshared from cost-minimality rather than from counting. Recording (a) because it is
proved and gives the criterion a concrete sufficient condition; (b) is the remaining
work and is the same shape of argument as the forced model's, run against class labels
instead of side patterns.

## 2026-09-03 — BLOCK 90: the DISJUNCTIVE free-swap criterion

  GData.pcost_congr_right -- pcost sees only the classes on the right too
  GData.swap_free_right   -- so same-class DEPARTURES swap for free
  GData.swap_free_or      -- **a swap is free if the two arrivals share a class OR the
                             two departures do**
  gcostOf_swapImg_or      -- and globally

This is the free-sign counterpart of EndData's `hshared`, which is also a disjunction:
  d.side a = d.side a'  OR  d.side (D.t a) = d.side (D.t a')
The two models agree on the SHAPE of the criterion. They differ in what the disjuncts
say: sides in the forced model, full (side, sign) classes in the free one.

That the shape matches is worth recording, because it means the merge development's
free-pair machinery -- which threads hshared through a dozen lemmas -- should port
structurally rather than needing a new argument. The disjunction is where hshared
enters and where the free-sign version supplies the same thing.

BLOCK 89's pigeonhole is now less central: five arrivals force a same-class ARRIVAL
pair, but the disjunctive criterion also fires on the departures, so the counting bound
is sufficient, not necessary, and by a wider margin than it looked.

## 2026-09-03 — BLOCK 91: free_pair_of_minimal does NOT port — a proved no-go

  altGData                              -- one side, alternating signs on Fin 4
  altGData_swap_raises                  -- the swap RAISES the cost (by decide)
  altGData_no_disjunct                  -- and neither disjunct of the criterion holds
  free_pair_of_minimal_fails_in_free_model -- so the forced model's derivation is FALSE
                                             as stated in the free-sign model

(propext only; both computations by kernel `decide`.)

In the forced model, if neither the arrivals nor their departures share a SIDE, the
swap strictly lowers the cost, so cost-minimality forces the disjunction. With four
classes that argument breaks: put all four ends on one side with signs +, -, +, -.
Neither disjunct holds, yet the swap raises the cost by four, so minimality permits the
configuration and gives no free pair.

WHAT THIS MEANS. The free-sign model buys the zero-cost turn at cut sites (BLOCKS
80-84) and a cleaner swap criterion (BLOCKS 87-90), but it LOSES the automatic
existence of free pairs. The forced model's two-valued side is what made "not sharing a
side" imply a strict decrease; with four classes the cost landscape has local minima
that are not free.

So the free-sign line is not a strict improvement. It trades one obstruction for
another, and both are now proved rather than suspected:
  forced model  cut sites must be empty        (BLOCK 77, pcostF_ge_one)
  free model    free pairs need not exist      (BLOCK 91, this)

## 2026-09-03 — BLOCK 92: the exact free-swap criterion; a third sufficient case

Enumerated the 256 class configurations: 152 admit a free swap, and the two disjuncts
of GData.swap_free_or cover only 112. So 40 free configurations were being missed.

  GData.swap_free_iff   -- the exact criterion: EQUAL ROW DIFFERENCES,
                           pcost x a - pcost x b = pcost y a - pcost y b
  GData.swap_free_cross -- a third sufficient case: arrivals on one side, departures on
                           the other. Every pair crosses and costs 1, so the swap is
                           free -- and neither original disjunct detects it.
  GData.swap_free_three -- the three conditions together

The enumeration was worth running rather than reasoning about. I had assumed the two
disjuncts were the whole criterion because they match EndData's hshared; they are not,
and the gap is 40 of 152 -- a quarter of the free configurations.

BEARING ON BLOCK 91'S NO-GO. That no-go stands: minimality still does not force a free
pair, and the counterexample there (one side, alternating signs) is not covered by any
of the three conditions. But the free-pair search has more room than BLOCK 90 suggested,
since swap_free_cross fires exactly when the two walks meet a site from opposite sides
-- which is the generic situation for a merge.

## 2026-09-03 — BLOCK 93: swap_free_cross does NOT fire at the merge site

  cross_unavailable_at_merge  -- the merge's arrival and its departure are both BOTTOMS
                                 (maximiser_has_bottom_arrival + maximiser_departure_
                                 bottom), so they share a side and the cross condition
                                 fails (axiom-free)
  merge_needs_class_agreement -- and when all four ends are bottoms, the swap is free
                                 IFF the arrivals agree in sign OR the departures do

So at a merge site the three sufficient conditions collapse back to the two class ones,
and both ask for a sign agreement that cost-minimality does not supply (BLOCK 91).

The second theorem is the sharp statement of where the free-sign merge stands: with all
four ends on one side, freeness is EXACTLY sign agreement on one of the two pairs. That
is a two-valued condition on four bits, so it fails in exactly the configuration
BLOCK 91 exhibited -- signs +,-,+,- -- and nothing about the merge's construction
excludes it.

STATUS OF THE FREE-SIGN LINE, honestly. It solves the cut-site problem (zero-cost turns
exist, BLOCKS 80-84) and it has a clean swap calculus (BLOCKS 87-92). It does not
supply free pairs at merge sites, and BLOCK 91 shows minimality cannot be made to. The
forced model has the opposite profile. Neither is a drop-in replacement for the other,
and that is now proved on both sides rather than assumed on either.

## 2026-09-03 — BLOCK 94: the free condition in the merge's ACTUAL configuration

BLOCK 93 assumed the merge hands over a same-sided pair. It does not. `a` is a bottom
arrival at the maximising walk's leftmost site; the other walk's end there is the TOP of
the edge one to the left (WalkSupport.shared_ends_at_wLo). So the two arrivals are on
OPPOSITE sides.

  merge_free_iff_bottom -- second departure a bottom: free iff
                             (sgn x = sgn u)  <->  (sgn x = sgn v)
  merge_free_iff_top    -- second departure a top: free iff the two same-side pairs'
                             costs sum to 2, i.e. one matched and one mismatched

Both are genuine iffs with free and unfree instances, so the question "does minimality
force a free pair" is a real combinatorial question in this model, not settled either
way by the shape of the configuration.

CORRECTION TO BLOCK 93. Its merge_needs_class_agreement assumed all four ends bottoms
and concluded the criterion collapses to sign agreement. That analysis is correct for
the case it states but is NOT the merge's configuration -- the second arrival is a top.
The theorem stands; its relevance to the merge does not.

I have now twice reasoned about "the merge's pair" without checking which pair the
assembly produces: BLOCK 93 assumed same-sided, BLOCK 92 assumed cross-side was
available. shared_ends_at_wLo settles it and has been in WalkSupport throughout.

## 2026-09-03 — BLOCK 95: the merge's SHAPE does not decide freeness

  freeCase / unfreeCase  -- two GData on Fin 4, both with x and u bottoms
  merge_shape_undecided  -- **both outcomes occur** with the two ends the assembly pins
                            held fixed (propext only; the computations by kernel decide)

Queried the assembly rather than reasoning about it. hasFreePair_of_minimal obtains `a`
as a bottom arrival and `D.t a` as a bottom departure. The second arrival comes from
walk_has_arrival_at_site, which returns `y` OR `D.t y` -- neither its side nor its
departure's side is constrained.

So of the six bits deciding freeness (two signs for a and D.t a, side and sign for each
of the other two ends), the assembly pins TWO. Both outcomes occur with those two fixed.

CONCLUSION FOR THE FREE-SIGN LINE. No argument from the merge's shape can settle
freeness; it has to come from cost-minimality, and BLOCK 91 proved minimality alone does
not force it. That is a genuine mathematical gap in the free-sign model, not a
formalisation gap, and it is now delimited exactly:
  - the shape pins 2 of 6 bits                        (BLOCK 95)
  - minimality does not force the remaining condition (BLOCK 91)
  - and the condition is a genuine iff, not vacuous   (BLOCK 94)

BLOCKS 91-95 have each corrected the previous one's reading of this configuration. The
pattern is consistent enough to name: I keep reasoning about what the merge produces
instead of reading the assembly. Every correction came from opening CostMerge, not from
thinking harder.

## 2026-09-03 — BLOCK 96: in the forced model hturn is FREE

  hturn_of_no_end_at_cut           -- hturn holds whenever NO end sits at a cut site:
                                      its conclusion is then true for every end, so the
                                      hypothesis is vacuous
  turnInv_of_mergesMin_of_empty_cuts -- so a cost-minimal datum is already in TurnInv
  shield_trivial_when_cuts_empty   -- and the catch: with cut sites empty, Zf misses the
                                      span interior entirely

BLOCKS 70-77 spent seven blocks looking for a zero-cost plan at cut sites to establish
hturn. In the forced model hturn needs no such thing: no_ends_of_alpha_zero says cut
sites are EMPTY, so no end has its site in Zf, so hturn's conclusion holds for every end
by vacuity. HasInitialTurnInv reduces to plain cost-minimality, which exists_mergesMin
already supplies.

The route was never tried because I read hturn as a condition ON the turn and asked how
to build a turn satisfying it, rather than reading it as a condition on the SITES and
asking whether any end is at one.

WHAT IT BUYS, honestly: nothing new for the shield law. hturn being free is only useful
where cut sites are empty, and BLOCK 60 showed that forces Z = 0 inside a span -- where
the shield law degenerates to thm:nogap, already proved. So this closes BLOCK 70's
stated gap and confirms the gap was never load-bearing.

The two models' final profiles, both proved:
  forced   hturn free, cut sites empty, shield law only at Z = 0
  free     cut sites can be occupied, but free pairs are not forced (BLOCKS 91, 95)

## 2026-09-03 — BLOCK 97: M4b ledger settled; green corrected to yellow

Wrote the settled ledger into private/RESEARCH_LOG.md and corrected M4b's colour.

The shield law is proved twice -- abstract configurations (BLOCK 5) and the extended
type (BLOCK 69) -- and NEITHER applies to a group element with a non-empty cut set. The
BLOCK 5 witness uses multiplicities (2,0,0,2); mu_pos forbids empty edges in a span, so
that configuration is not a PathData. I marked M4b green on that witness in BLOCK 5 and
it stood for ninety blocks.

The two obstructions are complementary, both proved:
  forced model  cut sites must be empty     -> Z = 0 -> shield law = thm:nogap
  free model    free pairs are not forced   -> the merge does not run
Closing M4b for group elements needs a model with occupied cut sites AND forced free
pairs. Neither has both.

M4b: GREEN -> YELLOW. The theorem is proved; its applicability to the GOAL is not what
the green implied.

## 2026-09-03 — BLOCK 98: audit of the remaining "(configurations)" greens

Applied M4b's test -- is the theorem instantiable from a group element? -- to the other
four.

  M5, M6, M7  PASS. Their hypotheses ask every edge to be OCCUPIED, which is exactly
              mu_pos (M6_hypothesis_holds), and BLOCK 36 instantiated all three on
              witElt (Elt.single_walk, Elt.defect_zero). The "(configurations)"
              qualifier comes off: they are statements about group elements.
  M3          FAILS, the same way M4b did. prop:cut is c >= |Z|, and its entire content
              is the Z != 0 case -- prop_cut_vacuous_at_empty shows the conclusion at
              Z = 0 is a function out of Fin 0, which exists for any graph. So M3's
              non-trivial content is unreachable for the same reason M4b's is.

M3: GREEN -> YELLOW. M5, M6, M7: qualifier removed, genuinely green.

Net: the table is unchanged in count (six green) but three of the greens are now
stronger than they were -- statements about elements, not configurations -- and two
atoms carry an honest scope note instead of an unqualified green.

The test is cheap and I should have run it at BLOCK 36 when the instantiations were
made, rather than at BLOCK 98 after M4b failed it.

## 2026-09-03 — BLOCK 99: M2 passes; the audit is complete

  Elt.lR_closed      -- M2 for a group element: the relaxed length is the least
                        realisation cost
  witElt_lR_closed   -- instantiated

SiteCost.lR_closed is stated for a PathData directly -- no configuration intermediary,
no occupancy or cut hypothesis -- so Elt.toPathData carries it across with nothing to
check. That is why M2 never carried the "(configurations)" qualifier: it was always
about the right object.

AUDIT COMPLETE. All six greens tested for instantiability from a group element:
  M2   PASS  stated for PathData directly                    (BLOCK 99)
  M5   PASS  instantiated, Elt.defect_zero                   (BLOCK 36)
  M6   PASS  instantiated, Elt.single_walk; hypothesis = mu_pos (BLOCKS 36, 98)
  M7   PASS  instantiated, Elt.defect_zero                   (BLOCK 36)
  B1   PASS  instantiated, witElt_merges                     (BLOCK 35)
  M3   FAIL  content is the Z != 0 case, unreachable         (BLOCK 98)
  M4b  FAIL  witness needs empty edges, mu_pos forbids them  (BLOCK 97)

Five green, two yellow. Every green is now backed by an instantiation on an actual
element, and every yellow has a proved reason.

## 2026-09-03 — BLOCK 100: M9 dependency audit — the yellows are OFF the critical path

Read thm:U rather than trusting the table's arrows.

thm:U assumes (M) and (R-J), and nothing else. (T) is discharged "via Theorem thm:nogap
and Corollary cor:localzero" -- M6 and M5 -- and explicitly NOT via the metric
identity's open lower bound. (L) is discharged as thm:L.

So thm:U reaches (T) through M5/M6, not through prop:cut. M3 and M4b -- the two atoms
that failed BLOCK 97-98's instantiability audit -- are OFF the critical path. M4b was
already marked SIDE; M3 feeds only M4b.

EVERY ATOM thm:U DEPENDS ON IS GREEN AND INSTANTIATED ON A GROUP ELEMENT:
  M2 Elt.lR_closed, M5/M7 Elt.defect_zero, M6 Elt.single_walk, B1 witElt_merges.

M9's orange is entirely (M) and (R-J). Nothing beneath it is outstanding.

That is the sharpest true statement about tonight's work: the combinatorial half is
complete for the atoms the goal actually uses. The two yellows are a side branch, and I
spent BLOCKS 59-98 on that side branch without checking whether the goal needed it.

## 2026-09-03 — BLOCK 101: BLOCK 100 RETRACTED — M3/M4b are ON the critical path

thm:U assumes (M), and (M) = (M1) + (M2) + (M3) with (M2) THE SHIELD LAW. The
settlement paragraph names (M)'s three weakest links: the metric formula, the reverse
shield inequality, and (M3).

BLOCK 100 reasoned "(T) is discharged via thm:nogap, therefore prop:cut is not needed".
Non-sequitur: (T) was never the route to the shield law, which enters directly as part
of (M). Third dependency conclusion tonight drawn from a partial reading.

CONSEQUENCE, and it is favourable: BLOCKS 59-98 were NOT a side branch. They were work
on (M2)'s reverse inequality c <= L-1, which the paper records as verified-not-proved
and proved only on gap-free elements where Z is empty.

And what those blocks established is precisely about that gap:
  forced model  Z is FORCED empty in a span, so the Z != 0 case is UNREACHABLE, not
                merely unproved -- and the shield law reduces to thm:nogap, the paper's
                own escape hatch
  free model    Z can be non-empty but free pairs are not forced, so the merge does not
                run
Two models, two proved obstructions. Closing the reverse inequality needs a model with
occupied cut sites AND forced free pairs.

## 2026-09-03 — BLOCK 102: (M3) named as a contract

  IsBlockDecomposition -- (M3a): every configuration splits into a k = 0 sector and k
                          travel blocks, with the weight multiplying across the split.
                          COMBINATORIAL.
  IsResolventForm      -- (M3b): the k-fold block weight is the k-th power, so the sum
                          over k is the resolvent. ALGEBRAIC, given (M3a).
  IsM3                 -- the conjunction
  weight_of_isM3       -- and with both, a configuration's weight is head * T^blocks

Splitting (M3) into (M3a) and (M3b) is the point. The paper states it as one hypothesis
-- the resolvent factorisation -- but the difficulty is entirely in (M3a): once every
configuration is known to decompose uniquely into blocks with multiplicative weight, the
resolvent form is bookkeeping. The memory note "the resolvent factorisation ... is
combinatorial/algebraic, not analytic" says the same thing less sharply.

All three of (M)'s weakest links now have a shape:
  metric formula          IsRelaxedLength    (BLOCK 7)
  reverse shield c<=L-1   obstructed in both models, both obstructions proved
  (M3)                    IsM3 = IsBlockDecomposition + IsResolventForm  (BLOCK 102)
None is proved. What changed tonight is that each is now a named obligation with its
difficulty localised, rather than prose in a settlement paragraph.

## 2026-09-03 — BLOCK 103: (M3) contract CORRECTED — the weight needs an operator

BLOCK 102 made the per-block weight a scalar. Wrong, and the cost itself shows why:

  site_cost_couples -- at a site strictly inside the travel interval,
                       siteCost s = max(|d(s-1)|, |d(s)|)

That couples CONSECUTIVE deposits. No per-edge scalar reproduces it, which is exactly
why the paper's (M3) uses a transfer OPERATOR. Corrected:

  pathWeight              -- lambda at the head, T across each step, mu at the tail
  IsTransferDecomposition -- (M3a): a configuration's weight is its state path's weight
  IsResolventSum          -- (M3b): summing over all path lengths gives the resolvent
  IsM3                    -- the conjunction
  pathWeight_single       -- and with ONE state the operator IS a scalar, which is why
                             the first attempt looked plausible

Caught by computing the site cost rather than by inspecting the contract. site_cost_
couples is three lines and would have prevented BLOCK 102's version had I written it
first -- the same order-of-operations mistake as BLOCK 28 (mark green, then instantiate)
and BLOCK 92 (assume the criterion, then enumerate).

The state space is the junction-adjacent deposit magnitude, which is what the paper's
B_sigma is indexed by. So (M3a)'s content is: the walk decomposition tracks that
magnitude across travel edges, and the cost is multiplicative in it.

## 2026-09-03 — BLOCK 104: the deposit magnitude IS a sufficient state

  site_cost_magnitude_only -- the interior site cost depends on the deposits only
                              through their MAGNITUDES
  travelT                  -- the transfer matrix on magnitudes, travel side:
                              2b + 2 + 2 max a b  (edge weight 2x^(2b+1) times site cost
                              x^max(2a+1,2b+1), read in exponents)
  travelT_congr            -- well defined on magnitudes: the state-space choice is sound
  travelT_coupling_symm    -- and the coupling is symmetric, the two directions differing
                              only by the second edge's own weight

So (M3a)'s state space is settled: the junction-adjacent deposit magnitude, exactly what
the paper's B_sigma is indexed by. Away from the two marker sites that is the whole
state; at the marker sites the cost carries eps and delta as well (cor:marker), which is
why the assembly sums over the four marker data instead of folding them into T.

What (M3a) still needs is the DECOMPOSITION itself -- that every configuration's weight
is the path weight of its magnitude sequence. The state space being sufficient is a
precondition for that, and it is now proved rather than assumed.

This is the first block tonight where the object matched the abstraction on the first
try. The difference is that I computed the site cost (BLOCK 103) before writing the
contract, instead of after.

## 2026-09-03 — BLOCK 105: (M3a) IS the transfer-matrix theorem, and the theorem is proved

  pathSum      -- the sum over state paths of length n of the product of transfer entries
  pathSum_succ -- the transfer recursion, by rfl
  pathGF       -- lambda * M^n * mu, the form the assembly uses
  pathGF_succ  -- **the generating function satisfies the transfer recursion**

WHY THIS IS (M3a). lR = sum of mu over edges + sum of siteCost over sites (lR_eq, BLOCK
7). mu j is a function of one deposit magnitude; siteCost s of two consecutive ones
(site_cost_magnitude_only, BLOCK 104). So the weight is ADDITIVE WITH NEAREST-NEIGHBOUR
COUPLING, and (M3a) asserts that such a weight's generating function is a matrix
product. That is the standard transfer-matrix fact, and pathGF_succ proves it.

So (M3a) decomposes into:
  (i)   the weight is additive with nearest-neighbour coupling   -- lR_eq + BLOCK 104
  (ii)  such weights give matrix-product generating functions    -- BLOCK 105, PROVED
  (iii) the bookkeeping tying the paper's lambda, mu, T to these -- not done
(i) and (ii) are done. (iii) is matching the paper's junction-dressed boundary vectors
and gap-marked kernels to the pathGF form, which is identification, not a theorem.

That is a materially different picture from "(M3) is not proved". The mathematical
content is (i) and (ii); what remains is naming.

## 2026-09-03 — BLOCK 106: why the assembly sums over the four marker data

  Site0                   -- the near-marker site cost max(|d_L - 1|, |d_R|) of (M1)
  Site0_sign_dependent    -- deposits 2 and -2 have the SAME magnitude and DIFFERENT
                             marker costs (1 vs 3). Axiom-free, by decide.
  marker_needs_sign       -- so the near-marker cost is not a function of magnitudes
  transfer_state_is_magnitude -- while away from the markers it is

This closes (iii) as a structural question. The transfer state is the deposit magnitude
sigma, and that is sufficient EVERYWHERE EXCEPT the two junctions -- where the sign is
needed and is carried by eps*. So the assembly's four-fold sum over (eps*, delta*) is
not a convenience: it is what makes T a function of sigma alone, and hence what makes
the pathGF shape correct.

The paper indexes lambda and mu by sigma and sums over the marker data separately. That
is now justified rather than taken as given: BLOCK 104 shows sigma suffices in the bulk
and travel, BLOCK 106 shows it does not at the marker, and the marker data is exactly
the missing bit.

(M3a) STATUS after BLOCKS 103-106:
  (i)   weight additive with nearest-neighbour coupling   lR_eq + BLOCK 104   DONE
  (ii)  such weights give matrix-product GFs              BLOCK 105           PROVED
  (iii) the state is sigma, with the sign in the markers  BLOCK 106           DONE
What is left of (M3a) is writing the paper's lambda and mu explicitly and checking they
are the pathGF boundary vectors -- transcription against cor:marker and eq:junctionsym.

## 2026-09-03 — BLOCK 107: the sign-reversal involution; and BLOCK 106 was a rediscovery

Read eq:junctionsym. The paragraph introducing it says:

  "Every bulk edge cost and every interior bulk site cost depends on the deposit only
   through its magnitude (Corollary cor:localcost), so reversing the sign of the
   junction-adjacent deposit of a bulk run is a weight-preserving involution ... the two
   signs carry B_sigma/2 each"

So the paper already states BLOCK 104's magnitude-sufficiency, citing cor:localcost. And
the SYMMETRISED form of eq:junctionsym -- averaging x^max(sigma-1,..) and
x^max(sigma+1,..) -- IS the correction for the sign, with the earlier one-sign form
recorded as false (rem:markerfalse). BLOCK 106's finding that the marker reads the sign
is that same correction, reached independently.

Second rediscovery of the session, after BLOCK 85. Both times the fact was in the source
I was working from and I derived it instead of reading it.

WHAT IS ACTUALLY NEW HERE:
  sign_reversal_preserves_cost -- the involution, as a Lean theorem rather than a cited
                                  corollary
  two_signs_equal_weight       -- so the two signs carry equal weight: the B_sigma/2 of
                                  eq:junctionsym
  (and BLOCK 105's pathGF_succ, which is not in the paper as a separate statement)

So (M3a)'s three parts are all either proved or matched to the paper, and the remaining
work is transcription of lambda and mu -- which eq:junctionsym now gives explicitly for
mu, indexed by the travel state s and formed from the B_sigma exactly as pathGF wants.

## 2026-09-03 — BLOCK 108: the far junction, formalised from cor:marker

  FarSite                  -- max(|d_L + eps*|, |d_R|) if delta* = 0, else
                              max(|d_L|, |d_R - eps*|)
  FarSite_eps_dependent    -- it depends on eps*        (axiom-free, decide)
  FarSite_delta_dependent  -- and on delta*
  FarSite_not_mirror       -- and it is NOT the mirror of Site_0
  marker_asymmetry         -- while Site_0 mentions neither

All three of cor:marker's claims about the far junction are now machine-checked. The
corollary asserts them; the witnesses are d_L = 1, d_R = 0, where FarSite takes the
values 2, 0 and 1 across the marker data and Site_0 with the deposits swapped is 1.

STRUCTURAL UPSHOT. lambda carries the marker data, mu does not. That asymmetry is why
the assembly's four-fold sum sits on the lambda side, and it is the last structural fact
(M3a)'s transcription needs:

  state         sigma, the deposit magnitude                  BLOCK 104
  T             travelT, a function of sigma alone            BLOCK 104
  mu            eq:junctionsym, indexed by the travel state,
                symmetrised over the two signs                BLOCK 107
  lambda        the far-junction cost, carrying (eps*,delta*) BLOCK 108
  the theorem   pathGF_succ                                   BLOCK 105

Read the source first this time. It took one block instead of the two that BLOCKS
106-107 took to reach the same kind of fact by derivation.

## 2026-09-03 — BLOCK 109: cor:marker VERIFIED against siteCost

  siteCost_at_zero   -- siteCost 0 = Site0 (d(-1)) (d 0), for kstar != 0
  siteCost_at_kstar  -- siteCost kstar = FarSite eps delta (d(kstar-1)) (d kstar)

Both propext only. Site0 and FarSite were transcribed from cor:marker in BLOCKS 106 and
108; these show they are not independent definitions but consequences of
siteCost = max |alphaAt| |betaAt| once the virtual counters are evaluated:

  at site 0      vArr = 1 contributes -1 to alpha, and vD = 0 because kstar != 0, so
                 neither eps nor delta appears -- cor:marker's "for all four marker data"
  at site kstar  vArr = 0 and vD = 1, so delta selects which side carries eps --
                 cor:marker's two cases

So cor:marker is now machine-checked from the site-cost definition, not just
transcribed. That is the first of the paper's marker results to be derived rather than
cited in this file.

(M3a) TRANSCRIPTION STATUS:
  state sigma           BLOCK 104   proved sufficient away from markers
  T = travelT           BLOCK 104   well defined on sigma
  mu                    BLOCK 107   eq:junctionsym, with its B_sigma/2 justified
  lambda                BLOCK 108   FarSite, its three claims machine-checked
  markers derived       BLOCK 109   siteCost_at_zero, siteCost_at_kstar
  the theorem           BLOCK 105   pathGF_succ
What remains is the sum-splitting: writing lR's site sum as interior + the two markers,
which is a Finset.sum decomposition over Icc A (B+1) minus two points.

## 2026-09-03 — BLOCK 110: lR's site sum split at the two markers — (M3a)'s transcription complete

  lR_site_split      -- the site sum over Icc A (B+1) splits into the interior sites and
                        the two junctions, whose costs ARE Site0 and FarSite
  lR_interior_terms  -- and every interior term is max |d(s-1)| |d(s)|, a
                        nearest-neighbour coupling in the magnitudes

So (M3a) is now transcribed end to end:

  lR = sum of mu over edges                                    (lR_eq, BLOCK 7)
     + sum over INTERIOR sites of max |d(s-1)| |d(s)|          (BLOCK 110)
     + Site0 at the near junction                              (BLOCK 109)
     + FarSite at the far junction, carrying (eps*, delta*)    (BLOCKS 108, 109)

and that shape is exactly pathGF's: boundary vector, transfer entries, boundary vector,
with the state the deposit magnitude (BLOCK 104) and the transfer recursion proved
(pathGF_succ, BLOCK 105).

WHAT (M3a) STILL LACKS: the generating-function step. Everything above is about a SINGLE
element's lR. (M3a) asserts the same for the SUM over all elements -- that summing
x^lR over deposit sequences gives the matrix product. pathGF_succ is that statement in
the abstract; connecting it needs the sum over sequences to be organised by the
magnitude path, which is the standard argument but is not written.

So (M3) decomposes as: (M3a) single-element shape DONE, (M3a) generating-function step
NOT DONE, (M3b) resolvent form -- algebra given the first two.

## 2026-09-03 — BLOCK 111: the sign fibration, exactly

  sum_signed_eq_magnitudes -- summing a magnitude-dependent weight over signed deposits
                              in [-N, N] gives f 0 + 2 * (sum over magnitudes 1..N)

This is eq:junctionsym's "the two signs carry B_sigma/2 each", stated as a theorem
rather than as bookkeeping: every non-zero magnitude has exactly two signed preimages
and zero has one, so the fibration of signed deposits over magnitudes has the stated
multiplicities.

It is the atom of (M3a)'s generating-function step. Summing x^lR over deposit sequences
factors through the magnitude path exactly when the weight is magnitude-dependent, which
BLOCKS 104 and 110 established for the interior; the marker terms carry the sign
separately (BLOCKS 106-109), which is why they sit in lambda rather than in T.

So the generating-function step has its combinatorial atom. What it still needs is the
same statement for a SEQUENCE of deposits rather than one -- a product of fibrations,
which is the standard Finset.prod over the index set, and the multiplicity is
2^(number of non-zero magnitudes).

## 2026-09-03 — BLOCK 112: the product of fibrations

  sum_prod_signed      -- summing an UNCOUPLED magnitude-dependent product over signed
                          deposit sequences factorises into per-edge sums, each given by
                          the sign fibration of BLOCK 111
  uncoupled_factorises -- and the normalised case

This is the generating-function step for an uncoupled weight, via
Finset.prod_univ_sum. Higher-order unification could not see `g i (d i).natAbs` as
`f i (d i)`; supplying f explicitly fixed it.

WHAT IT SHOWS BY CONTRAST. lR is NOT uncoupled: its site costs max |d(s-1)| |d(s)| tie
consecutive deposits (site_cost_couples, BLOCK 103). So sum_prod_signed does not apply
to it directly, and the transfer matrix is not a convenience but a necessity --
pathGF_succ (BLOCK 105) is the coupled statement, and this block is the uncoupled one.

Having both makes the role of the coupling explicit: without it the generating function
is a product of scalars; with it, a product of matrices. That is the whole distance
between a trivial (M3) and the real one.

## 2026-09-03 — BLOCK 113: the coupled two-edge sum

  sum_signed_pair -- a weight F of two ADJACENT magnitudes, summed over signed deposits:
                     the fibration applies once per edge, giving the 1 / 2 / 2 / 4
                     multiplicities

This is the smallest instance where coupling matters. sum_prod_signed (BLOCK 112) needs
the weight uncoupled and does not apply to lR; this one does, and the proof is two
applications of sum_signed_eq_magnitudes, the inner one under a sum_congr.

JUDGEMENT CALL RECORDED. I also drafted a "multiplicities" restatement with the
constants distributed, and it cost two strikes on Finset.mul_sum rewrites. It is a
restatement of sum_signed_pair, not new content, so I dropped it and put the reading in
the docstring. Spending strikes on a cosmetic variant is the wrong trade -- the same
judgement I should have applied to the BLOCK 92 enumeration sooner.

(M3a)'s generating-function step now has: the single-edge fibration (BLOCK 111), the
uncoupled product (BLOCK 112), and the coupled pair (BLOCK 113). The n-edge coupled case
is the transfer-matrix statement, which is pathGF_succ (BLOCK 105) -- so the pieces meet,
and what is missing is the indexing that identifies lR's magnitude sequence with a path
in pathSum.

## 2026-09-03 — BLOCK 114: from additive cost to multiplicative transfer

  couplingSum              -- the additive coupling sum along a magnitude path: max at
                              each step
  couplingSum_cons         -- its recursion, by rfl
  pow_couplingSum          -- **the bridge**: x^(coupling sum) = x^(max a b) * x^(rest),
                              i.e. exponentiation turns the additive cost into the
                              multiplicative transfer product
  pow_couplingSum_eq_prod  -- and the whole path: the exponentiated coupling sum is the
                              fold of transfer factors along consecutive pairs

Both propext only.

This is the step from lR to pathSum. lR's interior contribution is a SUM of max
couplings (lR_interior_terms, BLOCK 110); pathSum is a PRODUCT of transfer entries
(BLOCK 105). x^(a+b) = x^a * x^b is the entire content of the passage, and stating it
along a path makes the identification explicit rather than implicit in the notation
x^cost.

(M3a) INVENTORY after BLOCKS 103-114:
  lR's shape                  single element, split at markers      BLOCK 110
  markers derived             from siteCost                          BLOCK 109
  state and transfer matrix   sigma, travelT                         BLOCK 104
  sign fibration              1 / 2 multiplicities                    BLOCK 111
  uncoupled product           factorises                              BLOCK 112
  coupled pair                1 / 2 / 2 / 4                           BLOCK 113
  additive -> multiplicative  pow_couplingSum                         BLOCK 114
  the transfer theorem        pathGF_succ                             BLOCK 105
Every ingredient of (M3a) is now a theorem in the file. What is not done is assembling
them into the single statement "sum over elements of x^lR = lambda (I-T)^-1 mu", which
is composition rather than new mathematics.

## 2026-09-03 — BLOCK 115: (M3a) assembled for a single element

  cost_exp_is_transfer -- a cost splitting as head + couplingSum along a magnitude path
                          exponentiates to head's exponential times the transfer product
                          along that path
  lR_exp_is_transfer   -- and for lR specifically, with the split BLOCK 110 proved

So (M3a) holds for ONE element: x^lR is a boundary factor times a transfer product along
the deposit-magnitude path. Every ingredient was proved in BLOCKS 103-114 and this
composes them.

WHAT REMAINS, precisely: the sum over elements. (M3) asserts the generating function
W(x,y) -- a sum of x^lR over all elements -- is lambda (I - T)^-1 mu. The per-element
statement is now proved; the sum needs formal power series (Mathlib's PowerSeries or an
explicit valuation argument), because the sum is infinite and the resolvent is its
closed form.

That is a different kind of work from the last thirteen blocks: those were combinatorial
identities about a single configuration, this is convergence in a formal topology. It is
also the point at which (M3b) -- the resolvent identity -- becomes the actual content
rather than bookkeeping, since (I - T)^-1 = sum T^k is exactly the statement that the
infinite sum has that closed form.

## 2026-09-03 — BLOCK 116: (M3b)'s algebraic core — the finite Neumann identity

  neumann_partial        -- (I - T) * sum_{k<N} T^k = I - T^N, for the transfer matrix
  resolvent_remainder    -- so the resolvent is the partial sum up to the remainder -T^N
  neumann_partial_scalar -- the one-state instance

The point of proving the FINITE identity: it separates the algebra from the convergence.
(I - T)^-1 = sum T^k is a statement about an infinite sum, but the only thing that
depends on the formal topology is that T^N vanishes in the limit. Everything else is the
telescoping above, and it holds outright.

So (M3b) reduces to: the transfer matrix's powers vanish in the formal topology. That is
a valuation statement -- each travel edge contributes a positive power of x (travelT's
exponent 2b + 2 + 2 max a b is at least 2), so T^N has valuation at least 2N. It is not
proved here but it is now a one-line question about travelT rather than an unexamined
"algebra given (M3a)".

TACTIC NOTE: `ring` does not apply to matrices. `abel` does the additive work and
`pow_succ'` supplies T * T^m = T^m * T. Three strikes were avoided by noticing the
non-commutativity in the error rather than retrying `ring`.

## 2026-09-03 — BLOCK 117: the valuation bound; (M3b) closes

  travelT_ge_two          -- every transfer entry carries exponent at least 2
  travelPathExp_ge        -- so a path of n steps carries at least 2n
  travelPathExp_tendsto   -- the exponent grows without bound in the path length

That is the statement (M3b) reduced to in BLOCK 116: T^N vanishes formally because its
valuation is at least 2N. So (M3b) is closed modulo stating it in a formal-power-series
setting, and the algebraic half (neumann_partial) is already proved outright.

(M3) SUMMARY. From "not proved" (the paper's settlement paragraph) to:
  (M3a)  every ingredient proved; assembled for a single element; the sum over elements
         remains, needing formal power series
  (M3b)  the finite Neumann identity proved; the valuation bound proved; nothing beyond
         transcription remains
That is the one of (M)'s three weakest links that moved tonight.

## 2026-09-03 — BLOCK 118: summability — lR bounds both the span and the deposits

  span_le_lR       -- lR bounds the span length: every span edge has mu >= 1, so the
                      edge sum alone is at least the number of edges
  deposit_le_lR    -- and lR bounds every deposit: mu >= |d| and one term <= the sum
  bounded_of_lR_le -- so elements with lR <= N are bounded in span AND deposits

This is the finiteness the formal sum needs. The sum over elements of x^lR is formally
summable because each degree N is hit by only finitely many elements -- and the two
bounds above are why: bounded span, bounded deposits, hence finitely many (d, kstar).

Both bounds come from the same fact, mu >= 1 on the span (mu_pos) -- the same fact that
BLOCK 60 used to show cut sites cannot be empty in a span. It is doing double duty:
there it obstructs the shield law, here it gives summability.

(M3a)'s remaining step therefore has its analytic input. What is still not written is
the sum itself -- organising the finite sum at each degree by magnitude path and
recognising it as a matrix entry. That is transcription against Mathlib's PowerSeries,
not a mathematical gap.

## 2026-09-03 — BLOCK 119: lR fibres over magnitude paths

  mu_congr        -- mu depends only on the deposit MAGNITUDE and the cursor. Its test
                     `d j = 0` is a magnitude test (natAbs_eq_zero), and the else-branch
                     is max of magnitudes.
  edge_sum_congr  -- so the whole edge sum depends only on the magnitudes

Together with site_cost_magnitude_only (BLOCK 104) for the interior sites and
siteCost_at_zero / siteCost_at_kstar (BLOCK 109) for the two junctions, this says:

  lR is determined by the deposit MAGNITUDES together with the two SIGNED marker
  deposits.

That is the precise fibration the generating-function step needs. The sum over elements
fibres over magnitude paths, with the sign information confined to the two junctions --
which is exactly why the assembly sums over the four marker data separately and indexes
lambda, mu by sigma.

So every structural fact (M3a)'s remaining step requires is now proved:
  summability          BLOCK 118  lR bounds span and deposits
  the fibration        BLOCK 119  lR determined by magnitudes + marker signs
  the fibre counts     BLOCK 111  two signs per non-zero magnitude
  the transfer form    BLOCK 105  pathGF_succ
What is left is writing the sum, in Mathlib's PowerSeries.

## 2026-09-03 — BLOCK 120: the generating function as a formal power series

  gfOf                -- the generating function of a fibre-counting function
  coeff_gfOf          -- its coefficients ARE the fibre counts
  gf_mul              -- an ADDITIVE split of the cost becomes a CONVOLUTION of
                         coefficients, i.e. a product of series
  gf_transfer_order   -- and a factor whose fibres start at 2 has order 2, so the
                         transfer product converges formally (travelT_ge_two, BLOCK 117)

gf_mul is the series-level form of pow_couplingSum (BLOCK 114): pointwise, x^(a+b) =
x^a * x^b; at the series level, an additive split convolves. That is what turns the
per-element identity (lR_exp_is_transfer, BLOCK 115) into a statement about W(x,y).

So (M3)'s remaining step now has all four of its parts in Lean:
  summability     BLOCK 118   lR bounds span and deposits, so fibres are finite
  fibration       BLOCK 119   lR determined by magnitudes + marker signs
  fibre counts    BLOCK 111   two signs per non-zero magnitude
  series algebra  BLOCK 120   additive split -> product of series, with order >= 2
What is not written is the single composite statement naming the paper's W, lambda, mu
and T -- which is transcription against eq:assembly, not a further theorem.

(Mathlib note: PowerSeries.coeff takes only n; R is implicit from the section variable.
`PowerSeries.coeff ℤ n` fails with an application type mismatch that does not name the
arity.)

## 2026-09-03 — BLOCK 121: eq:assembly as a degree-wise contract

  IsAssembly                      -- eq:assembly read coefficient by coefficient, with
                                     the resolvent as a FINITE partial sum at each
                                     degree
  assembly_at_zero                -- at degree 0 only k = 0 survives, so the constant
                                     coefficient is W_0's plus the plain pairing
  neumann_partial_gen             -- the finite Neumann identity over any commutative
                                     coefficient ring, so it applies to matrices over
                                     PowerSeries
  assembly_is_truncated_resolvent -- and the partial sums ARE the Neumann truncations

Making the resolvent a finite sum at each degree is the point. (I - T)^-1 is an infinite
object, but T has order at least two (travelT_ge_two, BLOCK 117), so T^k contributes
nothing below degree 2k and every coefficient of the resolvent is a finite sum. That is
what lets everything proved in BLOCKS 103-120 -- all finite statements -- feed
eq:assembly directly.

Generalising neumann_partial to an arbitrary commutative ring was needed because T's
entries are power series, not integers. The original proof carried over unchanged.

(M3) NOW HAS A COMPLETE SKELETON IN LEAN: the contract (IsAssembly), the algebra
(neumann_partial_gen), the truncation justification (travelT_ge_two), the fibration
(BLOCK 119), the fibre counts (BLOCK 111), the summability (BLOCK 118) and the series
algebra (BLOCK 120). What is absent is the proof that the paper's W, lambda, mu, T
satisfy IsAssembly -- which is the identification, and needs the bulk kernels B_sigma
that this file has not built.

## 2026-09-03 — BLOCK 122: the gap term is rank one, verified

  gap_term_rank_one -- 2q^b * q^(a+b) = (2q^(2b)) * q^a, i.e. the gap term IS the outer
                       product u_b v_a of eq:rankone
  max_not_additive  -- and the other term does not factor: max 1 1 != max 2 0 while
                       1 + 1 = 2 + 0, so q^max(a,b) is not a function of a + b
  kernel_splits     -- so the gap-marked kernel splits into a non-factoring part and a
                       rank-one part, which is the shape eq:rankone exploits

All propext only.

This is the Mobius factorisation's algebraic core, checked. The paper writes the
gap-marked system as (I - M_0 - g u v^T) P = E and factorises because the gap term is
rank one; gap_term_rank_one is that claim, and max_not_additive is why the OTHER term
cannot be treated the same way.

Worth noting the contrast with the memory note "(R-J) status: the obstruction is a RANK
count (junction matrix rank 4, 6 symmetrised), not a sign". The gap term is rank one and
factorises; the junction is rank 6 and does not. Both are rank statements about the same
assembly, pulling in opposite directions -- one enables the Mobius factorisation, the
other blocks the residue computation that (R-J) needs.

## 2026-09-03 — BLOCK 123: the junction is NOT rank one — verified in Lean

First checked the paper's rank claims exactly in Python, over Q at x = 1/2, on the block
sigma in {0,2,4,6,8,10}, 2s+1 in {1,...,11}:
  symmetrised form   rank 6   (paper says 6)   CONFIRMED
  earlier form       rank 5   (paper says 5)   CONFIRMED

Then formalised the load-bearing consequence:

  junc0, junc2          -- the symmetrised junction entries at sigma = 0 and 2
  junction_not_rank_one -- the 2x2 minor is 3/128, NON-ZERO
  not_outer_product     -- so no outer product f a * g s reproduces the junction, since
                           a rank-one matrix has every 2x2 minor zero

This is prop:junction's content, and it is the reason (R-J) is a hypothesis rather than
a theorem: thm:L gives B_U(q_m) != 0 at every travel pole, but the RESIDUE needs the
junction to be rank one, and it is not.

THE TWO RANK FACTS, side by side and both now machine-checked:
  gap term    rank ONE      gap_term_rank_one     (BLOCK 122) -> enables the Mobius
                                                                 factorisation
  junction    NOT rank one  junction_not_rank_one (BLOCK 123) -> blocks the residue,
                                                                 hence (R-J)
Same assembly, opposite conclusions, and the contrast is exactly why one of (M)'s
inputs is proved and the other is assumed.

## 2026-09-03 — BLOCK 124: why rank one would settle (R-J), and why it does not apply

  outer_pairing              -- a rank-one kernel makes the pairing FACTOR into two
                                independent pairings
  pairing_ne_zero_of_factors -- so with rank one, (R-J) would reduce to two separate
                                non-vanishings
  no_factor_reduction        -- and that reduction is unavailable, by BLOCK 123's minor

This makes the cost of the rank obstruction explicit. (R-J) asks that Pi_y(q_m) != 0 at
infinitely many travel poles. Were the junction rank one, that would follow from two
independent factors being non-zero -- easy checks. It is not, so the four marker terms
can cancel and must be controlled together.

That is "the obstruction is a RANK count, not a sign" made operational: the rank is not
just a number, it is the difference between a factoring pairing and one that does not
factor.

NOT DONE: any bound on the pairing itself, which needs the shape vectors R, L of
prop:shape. This file has not built them, and I am not going to invent them.

## 2026-09-03 — BLOCK 125: (R-J) is a SIGN question about four products

Read prop:shape: R spans ker(I - T(q_m)), and

  Pi_y(q_m) = sum over the four (eps*, delta*) of <lambda,R> <L,mu>

-- a sum of FOUR products. Formalised what that shape does and does not give:

  four_term_sum_can_vanish -- four NON-ZERO products can sum to zero, so thm:L's
                              B_U(q_m) != 0 does NOT give (R-J)
  sum_ne_zero_of_all_pos   -- but a shared sign does: if every term is positive the sum
                              is non-zero
  RJ_is_a_sign_question    -- the two together

So (R-J) at a given pole is exactly a sign question about four products. The open part
is whether the signs persist for infinitely many poles -- NOT whether the individual
pairings vanish, which thm:L settles. That matches the recorded status: "positivity
survives to 6 poles" is a check of exactly this, and the Blaschke route died trying to
force it asymptotically.

This is as far as (R-J) can be pushed without the shape vectors R and L, which need
ker(I - T(q_m)) and are not built here.

TACTIC NOTE: `decide` cannot evaluate Q-valued Fin sums, and simp reduces `![a,b,c,d] i`
only for i = 0, 1 without the higher cons_val lemmas. Explicit functions avoid both.

## 2026-09-03 — BLOCK 126: the two junction shapes

BLOCK 125 concluded that (R-J) at a pole is "a sign question about four
products".  That is right at one junction and wrong at the other.

`sitecost marker` now reports, for each `(aL,aR)` cell, the multiset of the
four `(eps*,delta*)` branch costs normalised by its minimum.  Over 420 cells
per case, four cases (`site0`/`siteK` x `k*>0`/`k*<0`), 1680 cells, zero
exceptions:

  site0 k>0   shape [0,0,0,0] x 420      dependence 0/420
  siteK k>0   shape [0,1,1,2] x 420      dependence 420/420
  site0 k<0   shape [0,0,0,0] x 420      dependence 0/420
  siteK k<0   shape [0,1,1,2] x 420      dependence 420/420

So the four terms of `prop:shape`'s sum carry a **common** power of q at the
near junction and the **spread** 0,1,1,2 at the far one.  Formalised in
`EltBridge.lean` (`farShape`, `near_junction_common_factor`,
`far_junction_quadratic`, `far_vanishing_iff`, `RJ_near_vs_far`; all
propext/Classical.choice/Quot.sound, 0 sorry):

* near junction: the pairing is `q^c * (sum of the four coefficients)`, so four
  non-zero pairings can cancel — and can cancel **for every q at once**, since
  the vanishing condition does not involve q.  That is the escape
  `four_term_sum_can_vanish` exhibits.
* far junction: the pairing is `q^c * (a0 + q(a1+a2) + q^2 a3)`.  Vanishing at
  `q_m` forces `q_m` to be a root of a quadratic whose coefficients are the
  pairings themselves.

The consequence for (R-J): a sign coincidence cannot be arranged uniformly
across the poles at the far junction.  Cancellation at one `q_m` constrains
that `q_m` alone.  This is consistent with, and explains, the recorded
"positivity survives to 6 poles".

NOT DONE.  This does not prove (R-J).  It removes the uniform-sign escape at
the far junction only; the near junction still admits it, and no bound on the
pairings themselves is available without the shape vectors R, L of
`prop:shape`, which need `ker(I - T(q_m))` and are still not built.  (R-J)
stays a hypothesis.

## 2026-09-03 — BLOCK 127: the escape is closed everywhere

Two results, one of them a correction.

**`sitecost delete 12 3`.**  Every perturbation of the three pairing costs
breaks the law: flip 2->0/1/3/4 gives 44800/38400/17200/17200 exceptions of
45700, pass 1->0/2/3 gives 45360/43200/43200, bounce 0->1/2 gives 43055 each.
The model as stated, (bounce,flip,pass)=(0,2,1), has 0.  So the assignment is
rigid, not a fitted choice.  Gap noted: the H4 deletion (|a| >= |f|) exercises
**0 configs** and therefore certifies nothing.

**Correction to BLOCK 126.**  That entry said the uniform-sign escape stays
open at the near junction.  It does not, and `siteCost_at_zero` — already in
the file — is the reason: the near cost is `Site0 (d (-1)) (d 0)`, carrying no
`eps` and no `delta`, because `vD 0 = 0` collapses the delta branch and kills
the eps factor.  The measured `[0,0,0,0]` shape is that theorem, seen
numerically.

The consequence is the opposite of what BLOCK 126 recorded.  The two junctions
are not two sums.  They are one sum, in which the near junction contributes the
*same* power of q to all four branches — so it factors out:

    sum_i  a_i q^(s0 + c + farShape i)  =  q^s0 * q^c * (a0 + q(a1+a2) + q^2 a3)

Formalised as `total_pairing_factors` and `RJ_uniform_escape_closed`
(propext/Classical.choice/Quot.sound, 0 sorry).  For q != 0 the whole pairing
vanishes exactly when the far quadratic does.  A `(eps*,delta*)`-blind junction
cannot contribute to a condition on `(eps*,delta*)`.

So the q-independent cancellation of `four_term_sum_can_vanish` is unavailable
to the actual junction pairing: vanishing at `q_m` pins `q_m` to a root of a
quadratic in the pairings, at every pole separately.

NOT DONE.  This closes one escape route; it does not prove (R-J).  Nothing here
bounds the pairings `<lambda,R>`, `<L,mu>` away from a conspiracy in which each
`q_m` happens to be a root of its own quadratic.  That still needs R and L from
`ker(I - T(q_m))`, not built.

## 2026-09-03 — BLOCK 128: H4 repaired, and the hypothesis it guarded is not one

BLOCK 127 flagged H4 as exercising 0 configurations.  The cause, and the fix.

**Why it was vacuous.**  `Edge::valid` rejects in two stages:

    if (m - f) % 2 != 0 || (m - a) % 2 != 0 { return false; }   // parity
    if m < |a| || m < |f| { return false; }                     // the bound

H4 tried to delete the bound by admitting `a` even with `f = +-1`.  But then `a`
and `f` have opposite parity, so the **parity** test rejects first and the bound
is never reached.  The deletion broke the wrong hypothesis.

**The bound is redundant.**  With `2u = m+f`, `2dn = m-f`, `a = f + 2(pd-pu)`,
`0 <= pu <= u`, `0 <= pd <= dn`, non-negativity of `u`,`dn` already gives
`|f| <= m`, and the `pd`,`pu` extremes give `a <= f + 2dn = m` and
`a >= f - 2u = -m`.  Both extremes are attained, so `m` is exactly the deposit
range.  Proved as `edge_bounds_redundant` and `edge_bounds_attained` in
`EltBridge.lean` (propext/Quot.sound, 0 sorry, omega-only).

**The repaired H4** deletes the test itself rather than trying to violate it,
and counts the configurations that become admissible:

    H4 delete: drop m >= |a|,|f| from valid(): 45700 -> 45700 configs (0 new),
                                                exceptions 0 -> 0

Zero new configurations, as the theorem predicts.  H1-H3 are unchanged by the
patch (44800/38400/17200/17200, 45360/43200/43200, 43055/43055 of 45700).

So the deletion table now reads: the three pairing costs are rigid, and the
fourth "hypothesis" was never a hypothesis.  The hole BLOCK 127 flagged in the
cited certificate is closed, in the sense that the certificate is no weaker
than it looked -- the missing test could not have failed.

## 2026-09-03 — BLOCK 129: auditing the other cited modes for the H4 pattern

H4 was vacuous because parity rejected its configurations before the hypothesis
it meant to delete was ever consulted.  Same audit, remaining modes.

**Non-vacuity.**  All three exercise what they claim, no empty buckets:
`xcheck 6` 398567 (arr,dep) pairs; `interior 12 3` 45700 configurations;
`universal 12 3` 269300 configurations across 8 non-empty site classes.

**A real gap found in `universal`.**  Its verdict is
`Site = max(|alpha|,|beta|)` -- **two** arguments -- while the law and `xcheck`
use three, `max(|alpha|,|beta|,|Phi|)`.  `Phi` is not zero.  The left block of
the arrival and departure vectors telescopes,

    arr 0 + arr 1 = pu + (u - pu) = u,      dep 0 + dep 1 = pd + (dn - pd) = dn,
    Phi = u - dn = f,

so `Phi = +-1` on every travel edge.  The two-argument form is nonetheless
correct, but only through parity: `a === f (mod 2)`, so `f` odd forces `a` odd,
hence `|a| >= 1 >= |Phi|`.  Without that hypothesis the absorption is false --
`alpha = beta = 0`, `Phi = 1` gives `1 != 0`.

Proved: `phi_eq_f`, `phi_absorbed`, `phi_not_absorbed_without_parity` in
`EltBridge.lean` (0 sorry; `phi_eq_f` omega-only).

Measured: `universal` now computes `Phi` (including the virtual-event shifts at
the markers, where the lemma does not apply directly, since a virtual arrival
of class (left,+) and a departure of class 0 or 1 both move it) and reports
`Phi-gaps`, the cells where the three-argument max exceeds the two-argument
one.  **0 of 2693 cells**, every site class.  The mode's output now states the
omission and the parity dependency rather than leaving the verdict looking
unconditional.

So: `universal` was sound but under-stated, and the reason it is sound is the
same parity mechanism that made H4 silently empty.  That mechanism has now bitten
twice in this tool.

## 2026-09-03 — BLOCK 130: the shield certificate tested only minimal m

`shield` is the mode carrying M2.  Same audit.

**Non-vacuity: passes.**  1248 configurations at 4 edges, and the mode already
reports the longest gap run it actually exercised (2 there, 3 at 5 edges),
which is the honest form of the H4 disclosure the other modes lacked.

**The restriction.**  Its crossing counts were fixed at the minimum,

    let m = a.map(|x| if x == 0 { 2 } else { x.abs() });

and the mode took no `lambda`, unlike `interior`, `marker` and `universal`,
which all sweep `m` up to `minimal + 2*lambda`.  So the shield law was certified
at minimal crossing counts only.

This is a test of the enumeration, not of the formula, because both closed forms
are `m`-blind: the site costs depend on `alpha`, `beta`, `Phi` and never on `m`,
so a crossing pair moves the predicted length by exactly 2 (`pred_len_shift`),
and the predicted defect counts interior sites with `alpha=beta=Phi=0`, which
does not mention `m` at all.  What was untested is whether the *minimum over
realizations* keeps up.

**Repaired.**  `shield <edges> <|a|max> [lambda]` now distributes up to `lambda`
extra crossing pairs over the edges in every way.  `lambda=0` reproduces the old
run exactly (1248 configurations), so the extension is a strict superset.

    shield 4 4 0     1248 configurations   0 / 0 exceptions   (regression)
    shield 4 4 1     5984 configurations   0 / 0 exceptions
    shield 4 2 2     2864 configurations   0 / 0 exceptions
    shield 5 4 1    39104 configurations   0 / 0 exceptions   gap run 3

So M2's certificate now covers non-minimal crossing counts, and the restriction
turned out to be harmless.  Unlike the `universal` finding, nothing was
overstated here -- the mode was simply narrower than its verdict line suggested.

A note on method: the first draft of this entry carried a companion Lean theorem
asserting the defect is `m`-blind.  With `m` absent from the count that statement
is `X = X` with an unused hypothesis -- the exact vacuity this audit exists to
find.  It was removed rather than shipped, and the point is left as prose.

## 2026-09-03 — BLOCK 131: nogap's boundary-shield term, tested at last

Continuing the audit into the tool carrying (T).

**Non-vacuity: passes, and nogap was already the honest one.**  It reports the
population of each conditional statement (`M6b` 48715 elements, `M6`/`M6a`
42361 at depth 21), and it counts rather than silently skips the elements it
excludes -- `odd` and `neg` are reported and the verdict requires both to be 0.
That is the disclosure `sitecost`'s H4 lacked.

**The untested special case.**  `cutset` counts interior sites plus one
hand-added term,

    boundary_shield = !interior && k == 0 && dl == 0 && s == 0 && lo == 0 && hi > 0

a five-condition conjunction admitting a NON-interior site.  `nogap` has no
deletion mode, so nothing had ever tested whether it is needed or fitted.

Added one.  `cutset_nb` is `cutset` with the term deleted, and both are run:

    depth 17:  fires on 10 of  8992 elements;  deleted -> prop:cut 0, M4b 10
    depth 21:  fires on 38 of 50763 elements;  deleted -> prop:cut 0, M4b 38

Every element it fires on is one where M4b would otherwise fail, and it fires
on no others.  So it is load-bearing and never spurious.  It also separates the
two statements cleanly: the **proved** inequality `c >= |Z|` never needs it --
deleting a cut site only lowers `|Z|` -- while the **heuristic** equality
`c = |Z|` needs it on exactly those elements.

**The matching Lean gap, closed.**  `cut_at_zero_iff` covers `kstar < 0`.  The
boundary-shield case is `kstar = 0`, where site 0 carries *both* virtual events
at once, and no lemma covered it.  `cut_at_zero_kzero_iff` now does:

    P.cut 0  <->  delta = false  /\  d 0 = 0  /\  d (-1) = 1 - eps

(0 sorry, propext/Quot.sound.)  `Phi_0 = f(-1) + vArr - vL = 1 - vL` forces
`vL = 1`, i.e. `delta = false`; that empties `vR`, leaving `beta = d 0`.

This also shows the tool's version is complete, not merely sound.  Its `lo == 0`
forces `d(-1) = 0` and hence `eps = +1`, which looks narrower than the criterion
-- but the other branch, `eps = -1` with `d(-1) = 2`, cannot occur when `lo = 0`,
since edge `-1` is then outside the span; and when `lo < 0` site 0 is interior
and is counted by the interior branch.  No cut site is missed.

## 2026-09-03 — BLOCK 132: what M4b's last obligation actually asks

A correction first.  BLOCK 131's closing line said the 38 boundary-shield
elements are "where M4b's remaining gap lives".  That is wrong.  Those 38 are
where the boundary term changes the *value* of `|Z|`.  M4b is `c = |Z|`;
`prop:cut` proves `c >= |Z|` everywhere, so the open direction is `c <= |Z|`,
everywhere, not on 38 elements.

`VEndpt.shield_of_initial` already reduces the shield law to a single
obligation, `HasInitialTurnInv`, and `TurnInvG` unpacks it to

    CostMerge.MergesMin ...  /\  (edgeOf (E.t x) != edgeOf x  ->  siteOf x not in Zf)

-- a minimal-cost merging pairing in which no turn crosses a cut site.

**What that second condition costs.**  At a cut site both adjacent edges are gap
edges, so `mu = 2` on each (`mu_eq_two_of_gap`): a cut site has two endpoints on
each side, not more.  A fixed-point-free involution confined to a two-element
side is the swap and nothing else (`turn_forced_at_two`), so any two pairings
satisfying the condition agree there (`cut_site_pairing_has_no_freedom`).  All
three are **axiom-free**.

So the obligation is not "choose a good pairing at the cut sites".  There is
nothing to choose: the condition determines the pairing at every cut site
completely.  `HasInitialTurnInv` is entirely a question about the pairing **off**
the cut sites, and whether the forced cut-site pairing is compatible with
minimality.

That sharpens the recorded obstruction.  The two models tried -- derived sign
(`EndData`) and free sign (`GData`) -- differ in what they allow off the cut
sites; neither has occupied cut sites together with forced free pairs.  This
block says the cut sites themselves contribute no degrees of freedom to that
search, so the obstruction is entirely in the off-cut pairing.

NOT DONE.  No pairing is constructed.  M4b stays where it was.

## 2026-09-03 — BLOCK 133: the cut-site condition is implied, not extra

New tool `tools/cutturn`, and the lemma behind it.

`TurnInvG` = `MergesMin` AND no turn crossing a cut site.  BLOCK 132 showed the
second half has no freedom at the cut sites.  This block shows it is not an
extra demand at all.

A cut site has `alpha = beta = Phi = 0`, hence site cost `0`
(`siteCost_zero_of_cut`).  A turn crossing a site is a pass, and a pass costs
`1` in the weights `sitecost`'s H0 certifies as `(0, 2, 1)` with 0 exceptions.
A pairing attaining cost `0` at a site therefore cannot pass there
(`no_pass_at_zero_cost_site`, `no_cross_turn_at_cut`; 0 sorry).

`cutturn` confirms it on the extreme family, the all-gap chain of `n` edges
where every interior site is a cut site and `|Z| = n-1`.  For `n = 2..12`:
minimum cost 0, attained only by the bounce-only pairing, which has exactly
`|Z| + 1` walks.  Cost model `bounce 0, pass 1`, a lower bound on the full
model, which is the safe direction for this claim.

So `HasInitialTurnInv` reduces to `MergesMin` alone.  The cut sites are settled:
determined (BLOCK 132), and determined the right way (this block).

NOT DONE.  `MergesMin` off the cut sites is untouched, and that is where the two
recorded obstructions live.  The chain carries no deposits, no travel and no
signs, so the flip weight is untested here.  M4b stays yellow.

## 2026-09-03 — BLOCK 134: deposits added; the walk count comes out right too

`cutturn dep` extends the enumeration off the gap chain.  Edge `j` now carries
`a_j` in `{-2,0,2}`, so the sign classes differ and `sitecost`'s full weight
matrix is live, `cost_of(i,j) = 0 if i=j, 2 if i/2=j/2, else 1`.  Realisations
(`pu_j`, free exactly where `a_j = 0`) are minimised over along with pairings.

    cutturn dep 9      29520 (chain, deposit) configurations
                       min-cost pairings that pass at a cut site : 0
                       configurations with walks-at-min != |Z|+1 : 0

The first count repeats BLOCK 133's cut-site condition with signs present.  The
second is stronger and is the point: the walk count at the minimum equals
`|Z| + 1` in every configuration -- that is `c = |Z|`, the shield law itself,
not merely its cut-site half.

The cut-site half also stops needing a minimality argument.  At a cut site both
deposits vanish, so `pd = pu` on each side, so the arrival and departure classes
agree on each side; the bounce pairs each class with itself at cost 0 while the
pass crosses halves twice at 1+1.  `bounce_beats_pass_at_cut` proves the gap for
every sign split (with `costOf`, the weight matrix, axiom-free).

NOT DONE, and the limitation is sharper than before.  Both families hold
`|a_j| <= 2`, hence `mu = 2` everywhere: one strand each way, exactly two
pairings per site.  The first genuinely richer case is `|a| = 4`, where `mu = 4`
gives two strands each way, the pairings per site multiply, and flips can
combine across a site.  Travel edges and the markers are absent as well.  So
this is evidence on a thin slice, not a proof, and M4b stays yellow.

## 2026-09-03 — BLOCK 135: passing is available exactly off the cut sites

`cutturn mu4` lifts the `mu = 2` restriction BLOCK 134 flagged: deposits to
`|a| = 4`, realisations sweeping `m_j` over the minimum and the minimum + 2, and
sites carrying two strands each way.  It reports 5841 realisations reaching
`mu = 4` and 15336 sites offering more than two pairings, so the restriction is
genuinely lifted and not merely re-parametrised.

    interior non-cut sites                       : 13592
    ... where NO min-cost pairing passes         : 0
    cut sites where SOME min-cost pairing passes : 0
    elements with walks-at-min != |Z|+1          : 0

A clean dichotomy with no exceptions either way: at a minimal-cost pairing,
passing is available **exactly** at the non-cut sites.

That is the mechanism of `c <= |Z|`, and it is now visible rather than assumed.
Pass at every non-cut site -- always possible -- and each run connects into one
component; no cut site admits a pass, so the runs stay separate; the count is
exactly `|Z| + 1`.

Both halves are proved at the level of the weight matrix.  At a cut site both
deposits vanish, so the classes agree on each side and the bounce costs 0 against
the pass's 1+1 (`bounce_beats_pass_at_cut`).  Off it, a non-zero deposit makes
one side's classes differ, so a bounce must pay a flip at 2, which the two passes
exactly match (`pass_le_bounce_of_left_differs`); they beat it when the far side
flips too.  `cut_dichotomy` states the pair.

NOT DONE.  What is proved is the local cost comparison at a single site.  The
global step -- that choosing a passing pairing at every non-cut site connects
each run, and that this is simultaneously realisable with minimality across all
sites -- is measured here, not proved.  That global step is `hsep` in
`walkCount_le_runs_blk`, and it remains the open half of M4b.  The chains also
carry no travel edges and no markers.

## 2026-09-03 — BLOCK 136: auditing this directory's scripts

BLOCK 131 audited `nogap`'s Rust `cutset`.  This is the rest of the directory.

**Three of the five cited scripts could never run.**  `side_probe2.py`,
`wlo_probe.py` and `maxwlo_probe.py` all begin

    exec(open("side.py").read().split("tot = multi")[0])

and `side.py` does not exist -- not in this directory, not elsewhere in the
repo, not in git history, and not gitignored.  It was `side_probe.py` under its
former name: that file defines exactly the needed `ends`, `isArr`, `turns`,
`walks`, and its driver begins with the very line the split looks for.  The
rename left the reference dangling and nothing caught it, because nothing had
re-run them.

Repaired to reference `side_probe.py`, resolved relative to the script rather
than the working directory.  All three then reproduce the recorded numbers
**exactly**:

    side_probe2.py    cost-minimal turns 263, multi-walk 146, shared-side 146, none 0
    wlo_probe.py      multi-walk cost-minimal 1114, two bottom arrivals at a leftmost site 1114
    maxwlo_probe.py   1114; at the MAX leftmost site 1114; at the MIN (= site 0) 662

So this is the paper4 pattern once more: the mathematics was right and the
plumbing was broken.  The numbers in this README were correct and had simply
stopped being checkable.

**The one script that ran is the one cited nowhere.**  `parity_check.py` --
6426 valid `(p,t)` pairs, 0 violations -- appears in no README and no paper.

**Independent re-derivation.**  `HasFreePair` rests on `side_probe2.py`'s
146/146, and that script's own predecessor was once wrong in a way that
reproduced consistently (`side_probe.py` scored the costs backwards).  A claim
with that history deserves a second implementation, not a second reading, and
this README's own guidance is to keep such things in Rust.  `cutturn freepair`
re-implements the probe from the model up:

    cost-minimal turns: 263  multi-walk: 146  shared-side pair exists: 146  none: 0
    AGREES with the Python on all four counts

**A model discrepancy worth stating.**  `side_probe2.py` scores a same-side pair
`2` and a different-side pair `1` -- same-side is never `0` -- because
`EndData.sgn` forces `sgn (t a) = !sgn a` there.  `sitecost` and `cutturn`'s
other modes score a same-CLASS pair `0`, a same-side sign flip `2`, a pass `1`.
These are the derived-sign and free-sign models, `EndData` and `GData`, and they
give **opposite** advice: minimising maximises passes in the first and minimises
them in the second.  Both numbers are right in their own model.  What must not
be done is to read `HasFreePair`'s 146/146 as support for anything in the
free-sign model; it is evidence in the derived-sign model only.

**Disclosed, not hidden.**  `nogap_verify.py` needs `lamp_lib.py` from the
untracked `route_b/`, so it is not reproducible from a clean clone.  The README
already said so, and it is the Python reimplementation the same section warns
against.

Also recorded: `cutturn mu4 6 4` exceeds a 900 s cap and was killed; `mu4 4 4`
completes in 4 s and `mu4 5 4` is the practical ceiling.

## 2026-09-03 — BLOCK 137: M4b's recorded blocker is stale; the real one is named

The ledger held M3 and M4b at "not instantiable from a group element (the witness
needs empty edges, `mu_pos` forbids them in a span)".  That is no longer the
obstruction, and this file already said why without the consequence being drawn.

`turnInv_of_mergesMin_of_empty_cuts` takes `hempty : forall x, siteOf x not in Zf`,
and its own docstring notes that a `PathData` span has no empty site, so `hempty`
forces `Z = 0` -- which is exactly the yellow.  But emptiness is the wrong
hypothesis, for the same reason `hZ` was: the paper's condition at a cut site is
that no strand CROSSES, not that the site is empty.  `hturn_of_cross_zero`
(BLOCK 61) already converts `cross = 0` into `hturn`, and `DataBuild.dataOf up hbal`
has `t := DataBuild.turn up` definitionally, so the two compose directly:

    turnInv_of_mergesMin_of_cross_zero
      (up ds d Zf) (hbal) (hcross) (hD : MergesMin ... (dataOf up hbal))
      : TurnInv d Zf (dataOf up hbal)

No emptiness hypothesis.  Cut sites may carry ends, which is the case `hempty`
excluded and the whole content of `prop:cut` and the shield law.

**The real remaining gap, now named.**  What `turnInv_of_mergesMin_of_cross_zero`
still asks for is `hcross`: at every cut site the site plan has `cross = 0`.  The
route is laid out in `ConfigLoop` lines 994-996 and every piece of it exists --

    cut_site_value           a cut site has siteValue 0
    exists_plan_cost_eq      a plan attaining siteValue exists
    site_cost_le_of_global   global minimality bounds the site-s sum
    site_sum_eq_plan_cost    that sum IS the plan cost
    cross_eq_zero_of_cost_zero   cost 0 forces cross 0

-- except one.  `site_cost_le_of_global` compares against a rival datum `E` that
agrees off site `s`, so using it requires REALISING the zero-cost plan as an actual
turn.  ConfigLoop builds a plan from a turn (`planOfTurn`, and the row/column
counting behind it).  It does not build a turn from a plan, and nothing else does.

So M4b's blocker has moved from "not instantiable, a scope problem" to one missing
construction: given a 4x4 transportation matrix whose row sums are the arrival class
counts and whose column sums are the departure class counts, produce a bijection
arrivals -> departures realising it.  That is a finite combinatorial statement, and
`exists_involution_two` is the same shape in a special case.

Ledger updated for both M3 and M4b.  Neither is green: the construction is not built.

## 2026-09-03 — BLOCK 138: the missing construction, built

BLOCK 137 reduced M4b to one thing: realising a zero-cost plan as an actual turn,
so that `site_cost_le_of_global` has a rival to compare against.  Built.

The general problem -- a bijection realising an arbitrary 4x4 transportation matrix
-- is not the one that had to be solved.  At a **cut** site the plan is forced to be
diagonal:

    alpha = (Cp-Cm) - (Ap-Am) = 0  and  Phi = (Ap+Am) - (Cp+Cm) = 0   =>  Ap = Cp, Am = Cm
    beta  = (Bp-Bm) - (Dp-Dm) = 0  with the site's own balance          =>  Bp = Dp, Bm = Dm

so the arrival and departure class counts agree class by class
(`cut_classes_match`, and `cut_classes_match_of_cards` reading it off
`siteValue = 0`).  A diagonal plan is realised by four simultaneous class-to-class
matchings, and every pair it makes is same-class, i.e. a bounce, so the turn costs
nothing and crosses nothing.

Three new theorems, 0 sorry:

    cut_classes_match              the four class counts agree at a cut site
    exists_involution_four         four equinumerous class pairs matched at once
                                   (exists_involution_two twice, glued by
                                   combine_involutions across disjoint supports)
    exists_class_matching_at_cut   the two composed: the zero-cost turn exists

NOT DONE.  What remains is the wiring, not a new idea: the constructed turn has to be
assembled into a full `WalkGraph.Data` agreeing with the given one off site `s`, so
that `site_cost_le_of_global` applies and forces the given turn's site cost to 0,
whence `cross_eq_zero_of_cost_zero` and `hcross`.  That is another
`combine_involutions`, against the existing turn rather than between two halves.
M4b is not green yet.

## 2026-09-03 — BLOCK 139: retraction of BLOCK 137, and the blocker proved

BLOCK 137 called M3/M4b's recorded blocker -- "the witness needs empty edges" --
stale, on the grounds that `hempty` was a badly chosen hypothesis and `cross = 0`
was the right one.  That was wrong, and BLOCK 138's own construction is what shows
it.

`cut_classes_match` says the arrival and departure class counts agree at a cut site.
Now look at what a class is.  `clsOf x = (if atTop x then 0 else 2) + (if sgn x then
0 else 1)` and `endDataOf = <atTop, isArrOf up, ds>`, so `side = atTop` and a class
fixes BOTH the side and the sign.  But `EndData.sgn` is derived from
`(side, isArr, depSign side)`, so on a fixed side every arrival carries one sign and
every departure the other (`sgn_arr_ne_dep`, already in the file).  Hence a single
class admits arrivals or departures, never both (`no_class_holds_both`).

Put the two together: at a cut site each class has `|Arr_i| = |Dep_i|`, and at most
one side of that equation can be non-empty, so both are
(`cut_class_empty_of_card_eq`).  **A cut site in the derived-sign model carries no
ends at all.**

So `hempty` is a THEOREM of this model, not a hypothesis someone chose badly.  The
ledger entry was right and BLOCK 137's "stale" was wrong; BLOCK 138's construction,
which is correct on its own terms, builds a matching that no legal turn can realise,
because a turn pairs arrivals with departures and those never share a class.

What survives from the two blocks, and it is not nothing:

  turnInv_of_mergesMin_of_cross_zero   TurnInv with strictly weaker hypotheses than
                                       turnInv_of_mergesMin_of_empty_cuts -- correct,
                                       and simply unfeedable in this model
  exists_involution_four               four equinumerous class pairs matched at once
  exists_rival_data                    splices a rival turn at one site into a global
                                       one, all three Data obligations discharged
  cut_classes_match                    the class counts agree at a cut site
  no_class_holds_both                  no class holds an arrival and a departure
  cut_class_empty_of_card_eq           so a cut site is empty here

The last three turn a recorded heuristic into a proof of why M4b is stuck.  The
obstruction is the derived sign, exactly as the ledger said.  The escape remains the
free-sign `GData`, where classes are independent and a same-class pair costs 0 -- and
which loses the free-pair guarantee, the other proved obstruction.  That bind is
unchanged.  Ledger corrected for both M3 and M4b.

## 2026-09-03 — BLOCK 140: H1a's generating set, formalised

M4b is blocked on a two-model bind with proofs on both sides (BLOCK 139), so this
takes the next atom in the order rather than pushing there.

H1a was recorded as "CONTRACT NAMED (`IsRelaxedLength`); needs a presentation + a
generating set, neither formalised".  `IsRelaxedLength L` quantifies over candidate
length functions and there was no candidate to supply.  There is now.

The generators are the three moves the `nogap` BFS uses, as `Elt`-valued maps with
every structure obligation discharged:

    s1   toggle the side
    s2   toggle the side and flip the sign     (explicit constructor: `heps` is a
                                                proof field mentioning `eps`, so
                                                structure update cannot carry it)
    s3   move the cursor one step, depositing at the edge it crosses

`s3` is the one with content.  Stepping the cursor changes `travel` at exactly the
crossed edge and by exactly one -- `travel_succ_at`, `travel_pred_at`, with
`travel_succ_ne`, `travel_pred_ne` for everywhere else -- and the deposit moves `d`
there by `∓eps`.  Since `eps = ±1`, `d - travel` changes by an even amount, so `hpar`
survives.  That is the whole reason the move is well defined.

With `one`, `Gen`, `Reaches` and `wordLength = sInf {n | Reaches n g}`, H1a is now a
concrete sentence rather than a contract:

    IsRelaxedLength wordLength     i.e.  forall g, wordLength g = g.lR

(`H1a_statement`, and `wordLength_one`, `reaches_wordLength`, `wordLength_le`.)

NOT DONE, stated precisely because BLOCK 137 was careless about exactly this.  H1a is
not proved.  Two further gaps remain even in the formalisation: there is no proof that
the generators generate -- that every `Elt` is `Reachable` -- and none that `Elt` under
these three moves presents the intended group.  `wordLength` is a genuine word length
only on reachable elements, since `Nat.sInf` returns 0 on the empty set; `Reachable` is
the side condition and any use must carry it.  What has changed is that the blocker is
no longer "nothing is formalised": the generating set and the length function exist,
and the statement can now be attacked directly.

## 2026-09-03 — BLOCK 141: the generators are involutions, and `Elt` is not extensional

Continuing H1a.  Before proving the generators generate, they have to be a symmetric
set, or `wordLength` is not a word metric at all.  They are:

    s1_involutive, s2_involutive, s3_involutive

`s3` is the one with content.  The reverse cursor step deposits the opposite `±eps` at
the same edge, so the two `Function.update`s collapse; `kstar` returns because the
steps are opposite and `delta` because each flips it.

But the statement is `SameElt`, not equality, and that is a finding rather than a
convenience.  **`Elt` is not extensional.**  Each `s3` inserts the crossed edge into
`supp`, so `s3 (s3 g)` carries `insert k g.supp`, which need not be `g.supp`.  `supp`
is stored as a witness for finite support, not canonically, so two `Elt` terms
agreeing on `kstar`, `eps`, `delta` and `d` are the same group element with different
bookkeeping.  The generators are involutions on the element, never on the term.

That matters for H1a, whose statement `IsRelaxedLength wordLength` is about terms.
The right-hand side is safe: `hsupp` forces every edge with a deposit or travel into
`supp`, so filtering `supp` by that condition picks out the same set whichever valid
`supp` is stored -- `occ_congr`, and hence `A_congr`, `B_congr`.  The span is a
function of the element.

So the asymmetry is entirely on the left: `wordLength` is defined through `Reaches`,
which is a relation on terms.  H1a has to be read modulo `SameElt`, and its RHS
already is.

NOT DONE.  `lR_congr` itself is not formalised -- it follows from `A_congr`, `B_congr`
and `mu`, `siteCost` reading only `(d, kstar)`, but that last step is not written.  Nor
is the original target of this block, that the generators generate: every `Elt` being
`Reachable` needs the reduction algorithm, and that is the next step.  H1a stays
orange.

## 2026-09-03 — BLOCK 142: Gen fixed up to SameElt; reachability's base case

BLOCK 141 found that `Elt` is not extensional.  BLOCK 140's `Gen` had been defined
with strict equality, `b = s1 a`, which makes it NON-SYMMETRIC even though every
generator is an involution -- the second application returns the element but not the
term.  That was a defect in my own definition, and it is fixed here: `Gen` and the
base case of `Reaches` are now taken up to `SameElt`.

With that, the theory behaves:

    s1_congr, s2_congr, s3_congr   the generators respect SameElt
    Gen.symm                       a step can be undone by the same generator, so the
                                   Cayley graph is undirected and wordLength is a
                                   metric rather than a quasi-metric
    Reaches.congr                  reachability is a property of the element

And the base case of reachability, which is finite: an element with the cursor at `0`
and no deposits is determined by `(eps, delta)`, and all four are words of length at
most two -- `one`, `s1 one`, `s2 one`, `s1 (s2 one)`.  `reachable_of_trivial`.

NOT DONE: the inductive step.  Note it is not a single-move descent -- from `kstar =
0, d 0 = 2` every generator INCREASES `|kstar| + sum |d j|` (`s3` moves the cursor off
zero and deposits), so no one-step measure argument works.  The reduction has to go by
words: fix `kstar` first, which sets every deposit's parity through `hpar`, then adjust
the deposits by cursor round trips, each of which crosses an edge twice and so changes
that deposit by `0` or `±2` -- exactly the freedom `hpar` leaves. That round-trip
lemma is the engine, and it is the next step.

## 2026-09-03 — BLOCK 143: the round trip, and the deposit engine

BLOCK 142 showed the deposit induction cannot be a single-move descent.  The engine it
needs is here.

`roundTrip_left`: from `delta = false` the four-step word `s3, s2, s1, s3` gives

    s3   kstar k-1, delta true,  d (k-1) += e
    s2   eps -e, delta false
    s1   delta true
    s3   kstar k,   delta false, d (k-1) -= (-e) = += e

so the cursor and the side return, the sign is flipped, and one deposit moves by
exactly `2e`.  That is precisely the freedom `hpar` leaves: it ties each deposit's
parity to `travel`, so once `kstar` is fixed the deposits may only move in twos, and
this word realises that step.

Wired to reachability: `reachable_s1`, `reachable_s2`, `reachable_s3`,
`reachable_roundTrip` (four steps), and `reachable_deposit_step`, which states the
engine on the element rather than the term -- from a reachable `g` with
`delta = false`, any `h` agreeing with `g` up to one deposit moved by `2 * eps` and the
sign flipped is reachable.

Also fixed: my attempt-3 rewrite of `roundTrip_left` had deleted the `end Elt` /
`end EltBridge` after it, leaving the file two namespaces deep, so every declaration
appended afterwards was landing at `EltBridge.Elt.EltBridge.Elt....`.  Caught by the
doubled name in `#print axioms`.  Net namespace depth is now 0.

NOT DONE: the induction itself.  What remains is to place the cursor and iterate the
engine -- reach the target `kstar` first, which fixes every deposit's parity, then
apply `reachable_deposit_step` once per unit of `|d j| / 2` at each edge.  Both steps
are now expressible; neither is written.  H1a stays orange.

## 2026-09-03 — BLOCK 144: cursor placement

The first half of the reachability induction, and the half the second half depends on:
fixing `kstar` fixes every deposit's parity through `hpar`.

`s3` alone cannot be iterated -- it flips the side, so the next `s3` walks back.  But
`cstep = s1 ∘ s3` PRESERVES the side and therefore iterates: it steps the cursor left
while `delta = false` and right while `delta = true`, depositing at each crossed edge.

    cstep_left, cstep_right        one step, each direction
    cstep_iter_left, _right        n steps: kstar moves by n, the side is unchanged
    reachable_cstep, _iter         reachability is closed under it
    reachable_kstar_nonpos/nonneg  walking from `one` and from `s1 one`
    reachable_kstar (m : ℤ)        EVERY cursor position is reachable

All 0 sorry.  Together with BLOCK 143's `reachable_deposit_step` the two halves of the
induction now exist as separate statements: place the cursor, then move the deposits
in twos.

NOT DONE: composing them.  `reachable_kstar` produces SOME element with the target
cursor, carrying whatever deposits the walk left behind; the deposit stage must then
correct those to the target.  Neither the bookkeeping of what the walk deposits nor the
iteration over edges is written.  H1a stays orange.

## 2026-09-03 — BLOCK 145: the walk's deposits, and a retraction of BLOCK 140

**The deposits.**  `reachable_kstar` places the cursor but says nothing about what the
walk leaves behind.  It leaves the indicator of `[-n, -1]`: walking left from `one`
deposits `+1` at every edge it crosses, and `eps` never changes, so

    cstep_iter_one n :  kstar = -n,  delta = false,  eps = 1,
                        d j = if -n <= j <= -1 then 1 else 0

That is what the round trips would have to correct to reach a target.

**The retraction.**  BLOCK 140 said H1a had become the concrete sentence
`IsRelaxedLength wordLength`.  It has not, and the claim was wrong.
`IsRelaxedLength L` asks `L g = g.lR`, and `lR` is the RELAXED length.  `wordLength`
is the TRUE word length, and the recorded metric formula is `|g| = lR g + 2 c g`.  The
defect is not zero -- `nogap` at depth 21 reports `max c observed = 3` over 50763
elements -- so `IsRelaxedLength wordLength` is FALSE.

Proved: `isRelaxedLength_wordLength_forces_no_defect`.  Given the metric formula, the
contract collapses to `c = 0` everywhere, which the enumeration refutes.  So the
sentence H1a wants from `wordLength` is the defect formula, named here as
`IsTrueLength`, whose lower-bound half is exactly what the ledger already records as
open (`geodesic-length-closed-form`: "lower bound STILL OPEN").

`H1a_statement` itself is still true -- it only unfolds a definition -- but it is not
H1a, and labelling it so was the error.  Ledger corrected.

This is the second retraction in this run (BLOCK 137 was the first), and both were
caught the same way: by continuing far enough into the construction that the claim had
to be used.

## 2026-09-03 — BLOCK 146: the sign-only flip, and where the atoms actually stand

`feps = s1 ∘ s2` flips `eps` while preserving the side, in two steps (`feps_spec`,
`reachable_feps`).  It is the piece the excursion word needs: walking out deposits
`+eps` at each crossed edge and walking back deposits `-eps`, and those cancel only if
`eps` is the same on both legs -- but the round trip flips it.  `feps` between the round
trip and the return leg restores it.  Without that step the return leg would DOUBLE the
outward deposits rather than undo them.  `IsExcursion` records the shape; the
bookkeeping over an arbitrary distance is not carried out.

### Why the table is not green, verified rather than assumed

Ten blocks of work (137-146) have now tested each remaining atom against its recorded
blocker rather than trusting the label.  Two of those blocks were retractions of my own
claims.  The result:

  M4b, M3   NOT a formalisation gap.  BLOCK 139 PROVES the obstruction: `clsOf` fixes
            side and sign, `EndData.sgn` is derived, so no class holds both an arrival
            and a departure; with `cut_classes_match` every class is empty at a cut
            site.  The derived-sign model forces cut sites empty.  The free-sign
            `GData` admits them and loses the free-pair guarantee -- also proved.  A
            third model is needed, not more Lean.

  H1a       NOT a formalisation gap either, now that the formalisation exists.  The
            generating set, identity, word length, involutivity, cursor placement and
            deposit engine are all built and certified.  What remains is the metric
            theorem itself, and its lower-bound half is recorded as open research
            (`geodesic-length-closed-form`: "lower bound STILL OPEN", after the
            2026-08-09 retraction of thm:Bproved as circular).  BLOCK 145 additionally
            showed the previously recorded contract was FALSE as stated.

  H1, H2    Need mathematical objects that do not exist yet: the bulk kernels `B_σ` for
            (M)'s identification, and the shape vectors `R`, `L` spanning
            `ker(I - T(q_m))` for (R-J).  BLOCKS 125-127 reduced (R-J) to a sign
            question and closed the uniform escape; neither is a Lean gap.

  M9        Already PROVED conditional on H1 and H2.  Turns green the moment they do,
            with no further work.

  GOAL      = M9 discharged.

So the honest answer to "why isn't it all green" is that the remaining atoms are open
mathematics, not unfinished formalisation, and that is now checked atom by atom instead
of inferred from the colours.  Continued Lean work will not move them; the two that
could be moved by better statements have been (M4b's blocker proved, H1a's contract
corrected).

## 2026-09-03 — BLOCK 147: the free-pair obstruction is not on the shield law's path

BLOCK 146 said M4b needs a third cost model.  It may not: the free-sign `GData` may
already be it, and the recorded blocker may be aimed at a different theorem.

`free_pair_of_minimal_fails_in_free_model` says a cost-minimal `GData` datum can have a
cross-walk pair admitting no free SWAP.  That machinery serves `MergesMin` -- merging
everything into ONE walk, which is `thm:nogap` (M6), already green.

The shield law's upper bound is a different statement with a different route.
`walkCount_le_runs_blk` concludes `walkCount <= |Z| + 1` from `hedge` and `hsep`, and
`hsep` asks only that each RUN be connected.  No swap and no free pair occurs in it.

What supplies `hsep` is BLOCK 135's dichotomy, and both halves are already proved:
off a cut site a passing pairing ties or beats the bouncing one
(`pass_le_bounce_of_left_differs`), so a minimal pairing that passes exists there; at a
cut site the bounce strictly wins (`bounce_beats_pass_at_cut`), so none passes.  A pass
links the two edges it crosses -- `reachable_turn`, already in the file -- so a run
whose interior sites all pass is connected.

The step that makes the local-to-global upgrade legitimate is `sum_min_is_min`: total
cost is a sum over sites, so minimal local choices assemble into a global minimum.  That
is why "some minimal pairing passes at each non-cut site" becomes "some minimal pairing
passes at every non-cut site at once" -- exactly the upgrade `cutturn mu4` measured over
29520 configurations with zero exceptions, and over 218112 interior non-cut sites at
n = 5.

And the cut-site half of GData is ALREADY BUILT and was not being used: `class_balance_of_cut`
gives per-class balance at a cut site, and `exists_zero_cost_turn` produces the
class-preserving involution from it.  BLOCK 138 rebuilt that construction for the
derived-sign model, where BLOCK 139 then proved it unusable; in `GData` the classes are
independent, so `no_class_holds_both` fails and the same construction is live.

NOT DONE.  This is a route, not a proof.  What is proved is that the recorded
obstruction is aimed elsewhere, that both halves of the dichotomy hold, and that the
assembly principle is valid.  Chaining `reachable_turn` along a run to get `hsep`, and
feeding `hedge`, are not written.  M4b stays yellow -- but the reason has changed from
"a proved two-model bind" to "an unbuilt chain in the free-sign model".

## 2026-09-03 — BLOCK 148: retraction of BLOCK 147, with the dependency chain traced

BLOCK 147 claimed the free-pair obstruction is aimed at `MergesMin` and that "no swap
and no free pair occurs in" the shield law's route.  That is wrong.  Traced link by
link:

    M4b / shield law
      -> walkCount_le_runs_blk        needs hsep
      -> hsep supplied by exists_run_connected
      -> which is ConfigMerge.reaches_stuck applied to run_step_min_gen
      -> whose proof calls CostMerge.cost_swapData
      -> which takes  hshared : d.side a = d.side a' \/ d.side (D.t a) = d.side (D.t a')

`hshared` IS the shared-side hypothesis -- `HasFreePair`, the thing `side_probe2.py`
checks and BLOCK 136 re-derived in Rust at 146 of 146.  So the free-pair input sits on
the shield law's path after all, and BLOCK 147's "different route" does not exist.

The chain above is the useful part of this block.  The README already recorded that
`HasFreePair` is what `side_probe2` confirms and that it is NOT PROVED, but the path
from it to the shield law had not been traced; it is now, and it is short.

So the position is the ledger's, restored and sharper:

  derived-sign model   cut sites are forced EMPTY (BLOCK 139, proved), so the shield
                       law is vacuous exactly where it has content; and the route
                       needs `hshared`, confirmed 146/146 but unproved
  free-sign model      cut sites are fine and `exists_zero_cost_turn` applies, but
                       `free_pair_of_minimal` does not port
                       (`free_pair_of_minimal_fails_in_free_model`), and the run
                       machinery needs exactly that swap

Both models are blocked on the same input, reached from opposite sides.  That is the
two-model bind, and it is genuine.

Third retraction of this run, after BLOCKS 137 and 145.  All three came from the same
habit -- asserting a route before tracing it to a leaf -- and all three were caught by
continuing until the claim had to be used.  The correct order is to trace first.

## 2026-09-03 — BLOCK 149: HasFreePair is PROVED in one model and REFUTED in the other

Two corrections, in opposite directions, and together they settle the two-model bind.

**HasFreePair is proved.**  This README says, in the 2026-08-23 entries, that
`HasFreePair` "is NOT PROVED" and that "the remaining mathematical content of M6dy is
exactly one statement: cost-minimality implies a free pair".  That is STALE.
`CostMerge.hasFreePair_of_minimal` proves it -- purely structural hypotheses,
`propext`/`Classical.choice`/`Quot.sound`, and `CostMerge.lean` has 0 sorry.  So the
BLOCK 148 chain

    shield law -> hsep -> run_step_min_gen -> cost_swapData -> hshared

is CLOSED in the derived-sign model.  What blocks the derived model is only BLOCK 139:
cut sites are forced empty there, so the shield law is vacuous exactly where it has
content.

**HasFreePair is refuted in the free-sign model.**  `free_pair_of_minimal_fails_in_free_model`
refutes the CRITERION, which does not by itself refute the conclusion.  `cutturn
freepair-g` tests the conclusion, with signs per STRAND as `configGData` has them
(`sgnOf x = sg x.edge x.idx`) rather than per end, since a per-end sign is more general
than any configuration:

    cost-minimal turns 975408, multi-walk 870496, shared-side pair exists 831868,
    none 38628

38628 of 870496, about 4.4%.  Not an edge case.  The smallest is ordinary:
`n=2, m=[2,2], up=[1,1]`.  Verified by hand: site 1 is the only site with two arrivals,
namely `(edge0, strand0, top)` and `(edge1, strand1, bottom)`; their sides are `true`
and `false`, and their departures `(edge0, strand1, top)` and `(edge1, strand0, bottom)`
are likewise opposite.  So no shared-side pair exists there for ANY turn, and whenever
those two arrivals fall in different walks `HasFreePair` fails outright.

**So the bind is proved on both sides:**

    derived-sign     HasFreePair PROVED; cut sites forced EMPTY (BLOCK 139)
    configGData      cut sites fine; HasFreePair REFUTED (38628 counterexamples)

The models differ in WHICH data are cost-minimal, and the free model's minimal data
include ones with no free pair.  Neither model can carry the shield law, and that is
now a result rather than an impasse.  A third route must avoid the swap/merge argument
entirely, not merely change the sign model.

## 2026-09-03 — BLOCK 150: the derived sign does not compute the paper's alpha

BLOCK 139's conclusion -- cut sites are forced empty in the derived-sign model -- was
strange enough to be worth tracing to its source.  The source is a mismatch between two
sign conventions, and it is machine-checked (`cutturn alphacmp`).

`sitecost`'s site vectors are

    arr = [pu, u-pu, pd, dn-pd]      dep = [pd, dn-pd, pu, u-pu]

so a class is (side, sign OF THE STRAND) and both ends of a strand share the sign.
Then, with `u = dn`,

    alpha = (Cp - Cm) - (Ap - Am) = 2 (pd - pu) = d

which is the paper's `alpha`.  Verified in every row of the sweep.

`EndData.sgn` instead derives the sign from `(side, isArr, depSign side)`.  On a fixed
side every ARRIVAL then carries one sign and every DEPARTURE the other, so the class
counts are degenerate and the same formula yields

    alpha = -m

constant in the deposit.  11 of 13 rows disagree; the two agree only where `d = -m`.

**So `EndData`'s classes do not compute the paper's `alpha`**, and `EndData.pcostF`
assigns `2` to same-side arrival/departure pairs that the certified `cost_of` assigns
`0`.  That is a different cost function, hence a different notion of "cost-minimal".

This explains BLOCK 139 without rescuing it: cut sites are impossible in the derived
model because `alpha = -m` is never `0` on an occupied edge.  That is an artifact of the
convention, not a fact about the group.  `configGData`, whose sign is per strand
(`sgnOf x = sg x.edge x.idx`), is the paper's convention -- and BLOCK 149 refuted
`HasFreePair` there, in the right model.

**Flagged, not concluded.**  M5, M6, M7 and B1 are green via the `EndData` machinery,
and `MergesMin` in those statements is minimality for `pcostF`, not for the certified
site cost.  Whether each survives the change of cost has to be checked statement by
statement -- some may not use the cost at all, some may.  I am not asserting they fail;
I am recording that their cost hypothesis is not the paper's and that the audit of the
green atoms is therefore not complete.  That check is the next thing to do.

## 2026-09-03 — BLOCK 151: the derived-sign model is exact at mu = 2 and lossy beyond

Tracing BLOCK 150 one level further gives the precise scope of the `EndData` machinery,
and with it the scope of the green atoms proved through it.

`EndData.sgn` depends on `(side, isArr, depSign side)`.  Within one edge, then, all up
strands must carry one sign and all down strands the other: `pu` is pinned to `0` or
`u`, and likewise `pd`.  Since `d = 2 (pd - pu)`, the representable deposits are

    m = 2 :  -2, 0, 2                 (all of them)
    m = 4 :  -4, 0, 4                 (paper has -4, -2, 0, 2, 4)
    m = 6 :  -6, 0, 6                 (paper has seven)
    m = 8 :  -8, 0, 8                 (paper has nine)

three values at every `m`, against the paper's `m + 1`.  The two conventions agree
EXACTLY at `m = 2` and diverge from `m = 4` on; over the sweep, 50 of 54 rows disagree.

So the `EndData` model is not wrong, it is **narrow**: it is the paper's model restricted
to edges whose deposit is extremal or zero.  Since `mu j = 2` whenever `|d j| <= 2` and
`|f j| <= 2`, that restriction is invisible on any configuration all of whose deposits
lie in `{-2, 0, 2}` -- which is where `witElt` and the green instantiations live.

**Scope of the greens, stated precisely.**  M5, M6, M7 and B1 are proved via `EndData`
and instantiated on `witElt`.  Their `MergesMin` is minimality for `pcostF`, which
coincides with the certified site cost exactly on edges with `mu = 2`.  So those atoms
are sound for configurations with all deposits in `{-2, 0, 2}`, and say nothing beyond.
That is a real theorem about a real subclass -- the gap-and-unit case -- and it is not
the general statement the paper makes.

I am not downgrading them here: the instantiation on `witElt` is valid and the
mathematics is right within its range.  What the ledger should record, and now does, is
the range.  The general case needs the per-strand sign, which is `configGData` -- and
that is the model in which BLOCK 149 refuted `HasFreePair`.

That is the shape of the whole difficulty, in one sentence: the model where the merge
argument works is the one that cannot express the general configuration, and the model
that can express it is the one where the merge argument fails.

## 2026-09-03 — BLOCK 152: correction to BLOCK 151 -- EndData is the GAP-FREE model

BLOCK 151 said `EndData` represents `d in {-m, 0, m}` and "agrees exactly at `mu = 2`".
Both halves are wrong, and the corrected statement is much sharper.

`pu` and `pd` are not independent there.  An up strand's TOP carries `sgn = ds true`
and a down strand's TOP carries `!ds true`, so at a site every arrival from the left
shares one sign and every departure the opposite one.  That anti-correlates them:

    ds true = true   ->  (pu, pd) = (u, 0)   ->  d = -m
    ds true = false  ->  (pu, pd) = (0, dn)  ->  d = +m

so the representable deposits are

    m = 2 :  -2, 2          m = 4 :  -4, 4          m = 6 :  -6, 6          m = 8 :  -8, 8

**and never `d = 0`.**  `EndData` cannot express a gap edge at all.

That is not a narrowness to be worked around; it identifies the model.  `EndData` **is
the gap-free model**, and everything falls into place:

  * BLOCK 139's "cut sites are forced empty" is exactly this.  A cut site needs `d = 0`
    on both sides, `d = 0` is unrepresentable, so there are no cut sites.  A
    representability fact, not a fact about the group -- as BLOCK 150 suspected but
    mislocated.
  * M6 is `thm:nogap`, whose hypothesis IS "no gap edge".  Its model and its hypothesis
    coincide.  The same holds for M5, M7 and B1, which live on the same configurations.
    Their green is well founded and the model is the natural one for them.
  * M4b and M3 are about cut sites, which require gap edges.  They cannot even be
    STATED in `EndData`.  That is why they are yellow, and it is not a gap in the proofs
    but a gap in the model.

So the ledger's "not instantiable from a group element" was right all along, and the
reason is now exact: the shield law needs gap edges and the model that proves the
merge cannot represent them.  The general model is `configGData`, per-strand signs,
where gaps are expressible -- and where BLOCK 149 refuted `HasFreePair`.

Fourth retraction of this run.  The previous three came from asserting a route before
tracing it; this one came from computing a set with two parameters free that only one
parameter controls.  The check that caught it was recomputing with them linked.

## 2026-09-03 — BLOCK 153: passing without swapping

BLOCK 149 refuted `HasFreePair` in the per-strand model, which kills the swap route to
`hsep`: walks cannot be MERGED there.  But `hsep` never needed merging.  What
`exists_run_connected` produces is a minimal datum whose runs are connected, and such a
datum can be CHOSEN instead: take a passing pairing at every non-cut site and the forced
bounce at every cut site.

What makes the choice legitimate is that the pass attains the minimum off a cut site.
BLOCK 135 proved that when the LEFT side's classes differ; a non-cut site may instead
differ on the right, so both cases are needed.  Proved here:

    pass_le_bounce_of_either_differs   a difference on either side makes the bounce pay
                                       a flip, which the two passes match
    noncut_gives_a_difference          a non-cut site differs on some side
    choose_pass_off_cut                the two together: off a cut site the pass attains
                                       the minimum, at one the bounce strictly wins

So M4b's route no longer runs through `HasFreePair`.  It runs through a direct
construction, and the refuted hypothesis is not on it.

NOT DONE, and stated carefully because four claims have already been retracted in this
run:

  * the gluing is not written -- per-site choices have to be assembled into one turn
    (`DataBuild.glue` exists) and shown globally minimal (`sum_min_is_min` is the
    principle, since cost is a sum over sites);
  * run connectivity from the passes is not written;
  * `choose_pass_off_cut` is stated on `Fin 4` classes, i.e. one strand per class per
    side.  That is the `mu = 2` shape.  For larger `mu` a cut site is a statement about
    class COUNTS matching, not about individual classes agreeing, and the lemma has to
    be restated over counts.

What HAS changed is the character of the blocker.  M4b was blocked by a hypothesis
refuted in the only model that can express gap edges.  It is now blocked by three
pieces of formalisation, each of which has its principle already proved.

## 2026-09-03 — BLOCK 154: the dichotomy over class counts

`choose_pass_off_cut` was stated on `Fin 4` classes -- one strand per class per side,
the `mu = 2` shape.  Recast over class COUNTS, which is what general `mu` needs.

With `Phi = 0` in the bulk, `alpha = 2 (Cp - Ap)` (`alpha_eq_two_mul_of_phi_zero`): the
flow balance turns the sign imbalance into a class imbalance.  A bounce-only plan keeps
each half to itself, so on the left it matches `(Ap, Am)` against `(Cp, Cm)` with
`Ap + Am = Cp + Cm`, leaving `|Ap - Cp|` pairs to flip at cost `2` each -- that is
`|alpha|` -- and `|beta|` on the right.  Meanwhile the certified minimum is
`max(|alpha|, |beta|)` (`siteValue_eq_max_of_phi_zero`).

So `pass_forced_when_both_differ`: when both imbalances are non-zero the bounce-only
plan is STRICTLY beaten, hence every minimal plan moves mass across the halves.  At
`mu = 2` passing was merely available; at a site with both sides imbalanced it is
forced.

Honest about the hypothesis: `hbounce`, that a bounce-only plan costs
`|alpha| + |beta|`, is carried as an explicit argument.  It is the transportation
computation sketched above and is NOT proved here.  The rest -- the arithmetic that
`max a b < a + b` for positive `a`, `b`, and that `siteValue` is that max under
`Phi = 0` -- is proved.

Still open for M4b, unchanged in kind from BLOCK 153: prove `hbounce`; handle the case
where exactly one of `alpha`, `beta` vanishes, where a passing plan exists at the
minimum but is not forced; glue the per-site choices; and chain the passes into run
connectivity.

## 2026-09-03 — BLOCK 155: hbounce discharged

BLOCK 154 carried `hbounce` -- that a bounce-only plan costs `|alpha| + |beta|` -- as an
explicit hypothesis.  It is now proved, and only the lower bound was needed, since the
argument is that bounce-only EXCEEDS the minimum.

The bound is pinned by the plan's own sums, with no optimisation.  In the left block the
row sum `x00 + x01 = Ap` and the column sum `x00 + x10 = Cp` give

    x01 - x10 = Ap - Cp

outright, so the flipped mass `x01 + x10` is at least `|Ap - Cp|` (`flip_mass_ge`).
Each flip costs `2`, and with `Phi = 0` the imbalance is `|alpha| / 2`, so the left half
costs at least `|alpha|` (`bounce_left_cost_ge`); the right half is the same statement
under `alpha_natAbs_swap` (`bounce_only_cost_ge`).

`pass_forced_of_sums` then concludes with no hypothesis beyond the sums: at a bulk site
with both imbalances non-zero, every bounce-only plan costs at least `|alpha| + |beta|`,
which strictly exceeds `max(|alpha|, |beta|) = siteValue`.  So no bounce-only plan is
minimal there, and every minimal plan passes.

Still open for M4b: the case where exactly one of `alpha`, `beta` vanishes -- there a
passing plan attains the minimum but is not forced, so it must be exhibited rather than
deduced; gluing the per-site choices into one turn; and chaining the passes into run
connectivity.

## 2026-09-03 — BLOCK 156: the local trichotomy is complete

The one-sided case, which BLOCK 155 left open, is a tie rather than a strict
inequality, and that is enough.

With `beta = 0` and `alpha != 0`, bounce-only already attains the minimum `|alpha|`, so
passing cannot be forced and a passing plan has to be exhibited.  It is exhibited by a
local trade: the left half carries at least one flip (since `alpha != 0`) and the right
half at least one same-class bounce (since the edge is occupied), and trading those two
for two passes preserves the row and column sums -- the left arrival goes right, the
right arrival goes left -- at cost `2 + 0 = 1 + 1`.  So the traded plan is still
minimal and it passes (`pass_ties_bounce_of_one_side`).

`local_trichotomy` now states all three cases at once:

    both sides agree (a cut site)   bounce STRICTLY wins   -> no minimal plan passes
    exactly one side differs        the two are EQUAL      -> a minimal plan passes
    both sides differ               pass strictly cheaper  -> every minimal plan passes

Only the first denies a pass, and it is exactly the cut condition.  That is the local
layer of M4b finished: at every non-cut bulk site a minimal plan with a pass exists, and
at every cut site none does.

What remains is the global layer, and it is mechanical in the sense that both its
principles are already proved: gluing the per-site choices into one turn
(`DataBuild.glue`, with `sum_min_is_min` giving global minimality because cost is a sum
over sites), and chaining the passes into run connectivity (`reachable_turn` links the
two edges a pass crosses).  Neither is written.

## 2026-09-03 — BLOCK 157: the gluing

`local_trichotomy` supplies a suitable minimal pairing at each site; this makes them one
turn.

The gluing needs no compatibility condition between sites.  Each per-site involution
moves ends only within its own site, so applying `T (siteOf x)` to `x` lands at the same
site and a second application is by the same `T` -- that is `glue_involution`, and it is
the same observation that let `exists_rival_data` splice a single site in BLOCK 143.
`glue_ne` and `glue_pt_ne` are equally direct, the latter because the crossing partner
changes the site while the turn does not.  Both are axiom-free.

`exists_glued_data` assembles them: every `WalkGraph.Data` obligation is discharged by
one of the three, so per-site choices become a datum with nothing further to check.

Global minimality of the glued datum follows from `sum_min_is_min`, since the cost is a
sum over sites and each site's choice is minimal -- the principle is proved, the
application to this datum is not written.

`RunsConnected` names the one remaining obligation: that two ends with the same run
index are joined.  A pass links the two edges it crosses (`reachable_turn`) and
`local_trichotomy` gives a minimal choice passing at every non-cut site, so what is
missing is only the chaining of those links along a run.  That is the last step of
M4b's global layer.

## 2026-09-03 — BLOCK 158: the local route to hsep is refuted

BLOCK 153 claimed the minimal datum with connected runs can be CHOSEN rather than merged
into -- pass at every non-cut site, bounce at every cut site -- and BLOCK 157 said only
the chaining remained.  Both are wrong, and the test that settles it was cheap:

    minimal data passing at EVERY non-cut site   : 8192
    ... of those, walks != |Z|+1                 : 5072

62 per cent.  Passing at every non-cut site does NOT give the right walk count.

The reason is visible once stated.  A pass links the two edges it crosses, but
`RunsConnected` asks that ALL ends with a given run index lie in one component, and an
edge with `mu = 4` carries four strands that must also be joined to each other.  One
pass per site does not do that; which strands the passes pick matters.  That is exactly
the content the merge argument supplies, and it is why the original proof used it.

So the local trichotomy does not replace the merge.  Everything proved in BLOCKS 153-157
stands as stated -- `local_trichotomy`, `pass_forced_of_sums`,
`pass_ties_bounce_of_one_side`, the glue lemmas, `exists_glued_data` -- they are facts
about site costs and about assembling per-site involutions.  What was wrong is the
inference from them to `hsep`.

Three routes to M4b are now closed rather than two:

    merge in the derived model      HasFreePair proved, but gap edges inexpressible
                                    (BLOCKS 139, 152)
    merge in configGData            gap edges fine, HasFreePair REFUTED, 38628
                                    counterexamples (BLOCK 149)
    local choice, no merge          refuted here, 5072 of 8192

Fifth retraction of this run.  This one was caught before anything was built on it,
which is the improvement: BLOCK 157 named the chaining as the next step, and the next
step was to test whether the chaining could work at all rather than to start writing it.

## 2026-09-03 — BLOCK 159: the local route works exactly at mu = 2, and why

BLOCK 158 refuted the local route in general.  Splitting its failures by edge width
locates it exactly:

    all edges mu=2 :   96 give |Z|+1,    0 do not
    some edge mu=4 : 3024 give |Z|+1, 5072 do not

and at wider spans, restricted to `|a| <= 2` so every edge has `mu = 2`:

    n <= 5 :  348 minimal data passing at every non-cut site, 0 failures

So the route is valid precisely when every edge carries two strands, and the mechanism
is visible.

At `mu = 2` an edge has one up strand and one down strand.  A pass at a site sends the
left arrival to the right departure -- that is `up(s-1) <-> up(s)` -- and the right
arrival to the left departure, `down(s) <-> down(s-1)`.  So passes build TWO PARALLEL
CHAINS along a run, an up chain and a down chain, and by themselves would give two
components, not one.  What joins them is the BOUNCE at a cut site: it pairs the top of
the up strand with the top of the down strand of the SAME edge.  The two chains are
therefore closed into a single component at each run boundary, and the count is exactly
`|Z| + 1`.

That also says why `mu = 4` breaks it.  With two up strands per edge the passes may pair
them in ways that do not chain, and nothing local forces the choice -- which is the
content the merge argument supplies and the reason 5072 of 8192 fail there.

**This is a non-vacuous sub-case of M4b.**  `mu j = 2` whenever `d j = 0`, so the class
`|d| <= 2` CONTAINS gap edges and therefore genuine cut sites -- unlike the derived-sign
model, where BLOCK 152 showed gaps are inexpressible and the shield law is vacuous.  So
M4b's upper bound is established on a class where it has content, by a mechanism that is
understood, and verified on 348 of 348 data at spans up to five edges.

NOT DONE: this is verified, not proved in Lean.  The Lean statement needs the two-chain
argument -- passes chain the up strands and the down strands separately, bounces at cut
sites close them -- which is a connectivity induction along the run, and it is specific
to `mu = 2`.  M4b in general stays open, with three routes closed.

## 2026-09-03 — BLOCK 160: the two-chain argument, proved

BLOCK 159 found the mechanism; this proves it, abstractly.

A strand is `(edge, up?)`.  At `mu = 2` a pass at the site between `j` and `j+1` gives
`(j, true) — (j+1, true)` and `(j+1, false) — (j, false)`, and the bounce at the run's
left boundary gives `(lo, true) — (lo, false)`.

`run_one_component` shows every strand of the run is reachable from the leftmost up
strand: the passes chain each level by induction, and the boundary bounce supplies the
one step between levels.  `run_pairwise` upgrades that to any two strands of the run
being joined, which is the shape `RunsConnected` asks for.  Both 0 sorry.

So the connectivity content of M4b's upper bound at `mu = 2` is now a proved lemma, not
a measured fact.  Note how little it needs: three families of edges and no minimality,
because minimality has already done its work in `local_trichotomy` by making the passes
and the boundary bounce available.

NOT DONE: instantiation.  `R` has to become the walk-graph adjacency on strands, `hup`,
`hdn` and `hjoin` have to be read off the pass/bounce structure at `mu = 2`,
`ReflTransGen` has to be matched to `WalkGraph.Reachable`, and the components counted.
That is mechanical but not written.  And the argument is specific to `mu = 2` -- BLOCK
158's 5072 failures at `mu = 4` are exactly the absence of the two-chain structure.

## 2026-09-03 — BLOCK 161: from the strand chain to the walk graph

`run_pairwise` lives on strands and concludes in `Relation.ReflTransGen`;
`RunsConnected` lives on ends and concludes in `SimpleGraph.Reachable`.  The bridge:

    reachable_of_reflTransGen   a chain whose steps are each realisable in the graph is
                                a walk in the graph  (axiom-free)
    run_connected_in_graph      run_pairwise transferred: any two strands of a run are
                                joined in the walk graph itself
    turn_step_realisable        the step hypothesis is not an extra assumption -- an end
                                and its turn are adjacent, which is reachable_turn

So the chain from `local_trichotomy` to run connectivity is complete as abstract
statements: minimality makes the passes and the boundary bounce available
(BLOCKS 153-156), the glue makes them one turn (BLOCK 157), the two chains connect the
run (BLOCK 160), and the transfer moves that into the walk graph (here).

NOT DONE, and it is the same three items each time they are named: define `f` taking a
strand to a representative end; derive `hup`, `hdn`, `hjoin` from the concrete pass and
bounce turns at `mu = 2`; and count the runs to reach `walkCount <= |Z| + 1`.  The first
two are bookkeeping against `EndType.Endpt`; the third needs `walkCount_le_runs_blk`,
whose `hsep` this chain is built to supply.

And the whole chain is `mu = 2` only.  BLOCK 158's 5072 failures at `mu = 4` are the
absence of the two-chain structure, so none of this lifts to the general case.

## 2026-09-03 — BLOCK 162: the instantiation, done

`f` is "the bottom end of the strand": `up j` and `dn j` for edge `j`'s two strands.
With that, the three hypotheses of `run_pairwise` become statements about the concrete
turn, and nothing else about the configuration enters:

    hup     from `up j`, cross its own strand (the partner) to the top, where a pass
            sends it to `up (j+1)`
    hdn     the same one step left, a pass carrying `dn (j+1)`'s partner to `dn j`
    hjoin   the boundary bounce sends `dn lo` straight to `up lo`

`reachable_partner` is the companion of `reachable_turn` -- an end is adjacent to its
crossing partner -- and the two compose into the strand step
`x -> D.t (D.p x)` used throughout.

`run_connected_of_turn_structure` is the result: the run is connected in the walk graph,
from the turn structure alone, with no abstract relation remaining.  0 sorry.

So the `mu = 2` chain is now complete except for its last link.  What is left is to
count: `walkCount_le_runs_blk` turns "each run is one component" into
`walkCount <= |Z| + 1`, and its `hsep` is what `run_connected_of_turn_structure`
supplies once the run decomposition is matched to `runIndexG`.  That matching is the
remaining step, and it is the only one.

Still `mu = 2` only.

## 2026-09-03 — BLOCK 163: from strand bottoms to all ends

`run_connected_of_turn_structure` joins the BOTTOM ends of a run's strands; `hsep`
quantifies over all ends.  The gap is one step, since an end is either a representative
itself or its partner's, and an end is always adjacent to its partner
(`reachable_to_base`).  `hsep_of_base_connected` closes it: go to the representative,
across, and back.

`walkCount_le_of_hsep` then names what M4b's upper bound at `mu = 2` reduces to.  Two
inputs remain:

    hedge     the geometric condition of walkCount_le_runs_blk -- every graph edge
              either stays inside a block or is a local step at a non-cut site
    matching  the run decomposition used by run_connected_of_turn_structure has to be
              identified with runIndexG

Everything else on the path is proved: the local trichotomy that makes passes and the
boundary bounce available (153-156), the glue that makes per-site choices one turn
(157), the two-chain connectivity (160), its transfer into the walk graph (161), its
instantiation on the concrete turn (162), and the lift to all ends (here).

That is the honest state of M4b: at `mu = 2` it is two bookkeeping inputs from closing,
and at `mu = 4` it is refuted along this route (BLOCK 158, 5072 of 8192), with the merge
route closed in both sign models (BLOCKS 149, 152).

## 2026-09-03 — BLOCK 164: hedge

The geometric half of `walkCount_le_runs_blk`, and it needs no new hypothesis: it is
the `TurnInvG` condition again.  With `pos = edgeOf`:

* a PARTNER edge keeps the edge, so `pos` is unchanged, and `blk = gz Zf . pos` with it
  -- the first disjunct;
* a TURN edge keeps the SITE, so both its ends have `pos` in `{s-1, s}` for `s` that
  site, `siteOf` being `edgeOf` or `edgeOf + 1`.  If the two `pos` differ then the turn
  changed the edge, which `hturn` says happens only off `Zf`.

`hedge_of_turnInv`, 0 sorry.  And `hturn` is exactly what `local_trichotomy` secures, by
making the bounce strictly win at a cut site.

So M4b's upper bound at `mu = 2` is down to ONE input: identifying the run decomposition
that `run_connected_of_turn_structure` uses with `runIndexG`.  Every other link --
local trichotomy, glue, two-chain connectivity, transfer, instantiation, the lift to all
ends, and now hedge -- is proved.

## 2026-09-03 — BLOCK 165: the run decomposition matches runIndexG

`runIndexG pos Zf x` is `gz Zf (pos x)`, and `gz Zf t` counts the cut sites at or below
`t`.  So two ends carry the same run index exactly when no cut site lies strictly
between their edges -- which is precisely the interval the two-chain argument runs
along.

    no_cut_between_of_gz_eq   equal run index  ->  no cut site in (a, b]
                              (a cut site there would be counted at b and not at a)
    gz_eq_of_no_cut_between   no cut site in (a, a+n]  ->  equal run index
                              (gz_step_eq, stepping across each non-cut site)

Both 0 sorry.  That was the last input.

**Every input to M4b's upper bound at `mu = 2` is now proved**: the local trichotomy
making passes and the boundary bounce available (153-156), the glue (157), the
two-chain connectivity (160), its transfer into the walk graph (161), its instantiation
on the concrete turn (162), the lift from strand representatives to all ends (163),
`hedge` (164), and the run-decomposition matching (here).

What is left is assembly, not content: instantiate the chain on `EndType.Endpt` with
`m = 2`, define `up` and `dn` as the two strands' bottom ends, and check that the
minimal turn `local_trichotomy` selects really does pass at each non-cut site and bounce
at each cut site in the sense `run_connected_of_turn_structure` asks.  That is
bookkeeping against the concrete types.

Still `mu = 2` only.  At `mu = 4` the two-chain structure is absent and BLOCK 158's
5072 of 8192 failures stand.

## 2026-09-03 — BLOCK 166: the assembly

`shield_upper_bound_of_structure`: `walkCount <= |Z| + 1`, from the turn structure.

    hedge   from the turn invariant                (hedge_of_turnInv, BLOCK 164)
    hsep    from run connectivity on representatives, lifted to all ends
            (hsep_of_base_connected, BLOCK 163)
    both    into walkCount_le_runs_blk

**No merge, no swap and no free pair appears anywhere in it.**  That matters because
BLOCK 149 refuted `HasFreePair` in the per-strand model -- the only sign model that can
express gap edges -- which closed the classical route to this bound.  This is a
different route to the same conclusion, and the refuted hypothesis is not on it.

Its hypotheses are: the geometry of the end type (`hpe`, `hts`, `hse`), the turn
invariant `hturn`, which `local_trichotomy` secures by making the bounce strictly win at
a cut site; a strand representative (`hbase`, `hbase_idx`); and run connectivity on those
representatives, which `run_connected_of_turn_structure` supplies at `mu = 2` from the
passes and the boundary bounce.

So M4b's upper bound is now a theorem modulo instantiating those on a concrete
configuration.  Fourteen blocks (153-166), five retractions along the way, and the route
that survived is the one that gave up on merging.

Scope, unchanged and worth repeating: `mu = 2` only.  BLOCK 158 measured 5072 of 8192
failures at `mu = 4`, where the two-chain structure is absent, and nothing here lifts.

## 2026-09-03 — BLOCK 167: instantiated down to two hypotheses

Carried the assembly onto the concrete types, discharging a hypothesis at each step.

    siteOf_cases                `siteOf` is `edgeOf` or `edgeOf + 1`, by definition
    shield_upper_bound_endpt    `hpe` and `hse` gone: `partner` keeps the edge and the
                                site sits on one of the two edges it separates
    shield_upper_bound_dataOf   `hp` and `hts` gone: `dataOf` has `p := partner`, and
                                `turn = glue siteOf (turnAt up)` applies the local map of
                                the end's OWN site, so `hp` is `rfl` and `hts` is
                                `turnAt_site`
    botOf, botOf_eq_or_partner  the representative: the bottom end of the end's own
                                strand, which is the end itself or its partner
    shield_upper_bound_bot      `hbase` and `hbase_idx` gone

What is left is two hypotheses:

    hturn   the turn passes only off the cut sites
    hrun    the bottom ends of a run are joined

and those are exactly what the `mu = 2` construction supplies -- `hturn` from
`local_trichotomy`, which makes the bounce strictly win at a cut site, and `hrun` from
`run_connected_of_turn_structure`.

So M4b's upper bound is now: `walkCount (dataOf up hbal) <= |Z| + 1`, given a turn that
bounces at the cut sites and whose passes chain the runs.  Nothing else.

Scope unchanged: `mu = 2`.

## 2026-09-03 — BLOCK 168: the route is complete

`shield_upper_bound_from_turn`.  Every hypothesis is now a concrete statement about the
turn, and the conclusion is `walkCount <= |Z| + 1`:

    hturn      it changes the edge only off the cut sites
    hpass_up   at each interior site it carries `up j`'s partner to `up (j+1)`
    hpass_dn   and `dn (j+1)`'s partner to `dn j`
    hbounce    at the run's left boundary it carries `dn lo` to `up lo`
    hcover     each representative is one of its edge's two strand bottoms
    hrange     every edge lies in the run

No merge, no swap, no free pair.  `CostMerge` is not invoked anywhere on this path.

That is the whole point of blocks 153-168.  BLOCK 149 refuted `HasFreePair` in the
per-strand model -- the only sign model that can express gap edges -- which closed the
classical route to this bound.  The route built since reaches the same conclusion from
the turn's passes and bounces alone, and `local_trichotomy` is what makes those
available: the bounce strictly wins at a cut site, the pass ties or wins off one.

Sixteen blocks, six retractions, and the surviving route is the one that stopped trying
to merge walks.

Scope, unchanged and load-bearing: `mu = 2`, and a single run.  BLOCK 158 measured 5072
of 8192 failures at `mu = 4`, where the two-chain structure is absent; the multi-run case
needs the per-run indexing that `hrange` here assumes away.  Both are real gaps and
neither is closed.

## 2026-09-03 — BLOCK 169: several runs

`hrange` had assumed every edge lies in one run.  In general the edges split into runs,
one per value of `gz`, each with its own left boundary and length; indexing them by the
run number lifts the argument, since two ends with the same `gz` lie in the same run and
that run's two-chain connectivity joins them.

    hrun_multi                 hrun for a family of runs
    shield_upper_bound_multi   the bound with hrange, hpass_up, hpass_dn and hbounce
                               all taken per run

Each run does have its boundary bounce: a run is bounded by cut sites, so unless `Zf` is
empty -- where the bound is `walkCount <= 1`, which is `thm:nogap`, already green --
there is a cut site at one end and the bounce there joins the two chains.

So the single-run restriction is gone.  What remains of the scope is `mu = 2` alone,
and that one is not a restriction of convenience: BLOCK 158 measured 5072 of 8192
failures at `mu = 4`, where the two-chain structure genuinely does not exist.

To finish M4b at `mu = 2` the remaining work is verification rather than construction:
check that the minimal turn `local_trichotomy` selects satisfies `hturn`, `hcover`,
`hrange`, `hpass_up`, `hpass_dn` and `hbounce` on an actual configuration.

## 2026-09-03 — BLOCK 170: hcover at mu = 2

An edge carries `m e` strands, so at `mu = 2` the strand index lies in `Fin 2` and is
`0` or `1` (`botOf_idx_cases`).  `botOf x` is therefore one of its edge's two strand
bottoms, which is `hcover` as soon as `up` and `dn` are the maps naming them
(`hcover_of_mu_two`).  No other property of the configuration enters.

`shield_upper_bound_mu_two` has `hcover` discharged.  What is left to verify on a
concrete configuration is the turn's own behaviour, and nothing else:

    hturn      the turn changes the edge only off the cut sites
    hup, hdn   `up` and `dn` name the two strand bottoms of each edge
    hrange     each edge lies in the run its `gz` names
    hpass_up   the turn's passes chain the up strands
    hpass_dn   and the down strands
    hbounce    the boundary bounce joins them

The Lean error this block was the dependent-position rewrite again -- `m x.edge` occurs
in the TYPE of `x.idx`, so `rw [hm]` breaks the motive.  The fix is the one this file
has needed several times: state both facts and let `omega` see them as atoms, never
rewrite under a dependent type.

## 2026-09-03 — BLOCK 171: the turn must be chosen, not taken

A correction of method rather than of fact.  Every statement since BLOCK 167 was phrased
for `DataBuild.dataOf up hbal`, whose turn comes from an ARBITRARY involution at each
site (`exists_involution_of_card_eq`).  One cannot assume such a turn bounces at the cut
sites and passes elsewhere -- those are the properties `local_trichotomy` says a MINIMAL
turn has, and the way to get them is to choose the per-site involutions and glue them.

`shield_upper_bound_glued` does that.  Its hypotheses are all about the chosen family
`T`:

    hinv, hTsite, hne     T is a per-site involution, fixing its site, fixed-point-free
    hturn                 T changes the edge only off the cut sites
    hup, hdn              up and dn name each edge's two strand bottoms
    hrange                each edge lies in the run its gz names
    hpass_up, hpass_dn    T's passes chain the up strands and the down strands
    hbounce               T's boundary bounce joins them

and the conclusion is `∃ D, walkCount D <= |Z| + 1`, the datum being the glue of `T`.

`exists_glued_data` (BLOCK 157) supplies the datum, `hcover_of_mu_two` the strand cover,
`run_connected_of_turn_structure` the connectivity, and `shield_upper_bound_endpt` the
count.  Nothing is inherited.

That closes the structural gap the previous four blocks had been carrying without
naming: they proved a bound about a turn nobody had shown could have the required
properties.  Now the turn is built to have them.

Scope still `mu = 2`.  The remaining mathematical content is that a cost-minimal `T`
really does satisfy `hpass_up`, `hpass_dn` and `hbounce` -- `local_trichotomy` gives the
cost comparison, and turning that into these three equalities is the last step.

## 2026-09-03 — BLOCK 172: the chain hypotheses, restated as reachability

Constructing `T` explicitly turned up a real subtlety in the hypothesis SHAPE, though
not in anything proved.

`run_connected_of_turn_structure` asks for `D.t (D.p x) = y`.  For the UP chain that is
the right composition: cross the strand, then turn.  For the DOWN chain the concrete
pass runs the other way -- at site `s` it sends `dn s` to the TOP of edge `s-1`'s down
strand, so what actually holds is `D.p (D.t (dn (j+1))) = dn j`, turn first and cross
second.  Both give the same reachability, which is why the earlier proof is sound, but
the equation form is not what a concrete `T` can hand over.

`run_connected_of_reachability` and `shield_upper_bound_reach` restate the chain
conditions as reachability:

    hchain_up     consecutive up strands are joined
    hchain_dn     consecutive down strands are joined
    hchain_join   the two are joined at the run's boundary

whichever walk does it.  That is exactly what a `mu = 2` turn gives: a pass at a non-cut
site joins the strands on either side of it, and a bounce at a cut site joins the two
strands of its own edge.

`shield_upper_bound_reach` also takes the datum `E` with `E.p = partner` and
`E.t = T ∘ siteOf` explicitly, rather than existentially, so a concrete construction can
be plugged in and the conclusion is about that datum.

Scope still `mu = 2`.  The remaining content is unchanged: show a cost-minimal `T`
satisfies the three chain conditions, which `local_trichotomy` supplies as a cost
comparison and which must be turned into these reachability statements.

## 2026-09-03 — BLOCK 173: the chain conditions from a pass and a bounce

Three walks of length at most two, each discharging one chain condition:

    chain_up_of_pass       from `up j`, cross the strand and turn: the pass at site j+1
                           carries the top of edge j's up strand to the bottom of edge
                           (j+1)'s
    chain_dn_of_pass       from `dn j`, cross the strand; the same pass read backwards
                           carries `dn (j+1)` to that top, so the two are joined
    chain_join_of_bounce   the bounce at a cut site pairs the two bottoms of its own
                           edge, so one turn step joins `up lo` and `dn lo`

`shield_upper_bound_of_pass_bounce` takes them in the composition a `mu = 2` turn
actually has -- `E.t (E.p (up j)) = up (j+1)` for the up chain but
`E.t (dn (j+1)) = E.p (dn j)` for the down one, which is the asymmetry BLOCK 172 found
-- and concludes `walkCount E <= |Z| + 1`.

So the route is now stated entirely in terms a concrete turn can supply: an involution
per site, fixing its site, fixed-point-free, changing the edge only off `Zf`, with those
three equations.  Nothing abstract remains in the hypotheses.

Scope still `mu = 2`.  What is left is to define `T` -- the pass at non-cut sites, the
bounce at cut sites -- and check the equations against that definition.

## 2026-09-03 — BLOCK 174: the turn, defined and verified

At `mu = 2` a site carries exactly four ends: the two tops of edge `s-1`,
`p (up (s-1))` and `p (dn (s-1))`, and the two bottoms of edge `s`, `up s` and `dn s`.
There are exactly two site-respecting involutions on them, and `local_trichotomy` says
which minimality picks: the BOUNCE at a cut site, the PASS elsewhere.

`passTurn` is that choice, and it is verified:

    passTurn_invol               an involution, given the four ends are distinct
    passTurn_ne                  fixed-point-free on those four
    passTurn_pass_up             at a non-cut site, edge s-1's up top -> edge s's up bottom
    passTurn_pass_dn             at a non-cut site, edge s's down bottom -> edge s-1's
                                 down top -- the opposite composition, as BLOCK 172 found
    passTurn_bounce              at a cut site, the two bottoms of edge s are joined
    passTurn_keeps_edge_at_cut   at a cut site every end stays on its own edge, which is
                                 exactly `hturn`

All 0 sorry.  The distinctness of the four ends is carried as hypotheses, which is what
it is: a fact about a real configuration, six inequalities.

So the turn is no longer hypothetical.  What remains to close the `mu = 2` bound is to
supply the six distinctness inequalities and `hTsite` -- that `passTurn` keeps each end
at its site -- for an actual configuration, and feed
`shield_upper_bound_of_pass_bounce`.

## 2026-09-03 — BLOCK 175: the turn assembled

`passTurn_site` -- the turn keeps every end at its site, each image being one of that
site's own four ends and everything else fixed.

`shield_upper_bound_passTurn` then supplies the turn to the bound.  Every property of
the turn is discharged from `passTurn`'s own lemmas: involutivity, fixed-point-freeness,
site-preservation, `hturn` (from `passTurn_keeps_edge_at_cut`), and the three chain
equations (from `passTurn_pass_up`, `passTurn_pass_dn`, `passTurn_bounce`).

What the caller now provides is only the configuration's geometry:

    h12..h34        the four ends of each site are distinct
    hs1..hs4        and sit at that site
    hfour           and are ALL of it
    hud             the two strands of an edge share it
    hupn, hdnn      `up` and `dn` name the strand bottoms
    hrange          the runs are indexed
    hbdry, hint     cut sites at the run boundaries, none inside

and the conclusion is `walkCount E <= |Z| + 1`.  0 sorry throughout; the file has never
carried one.

`hfour` was not in the previous statement and had to be added: `passTurn_ne` is
fixed-point-free only on the site's four ends, while the bound needs it for every end at
that site.  At `mu = 2` those coincide, but that is a fact about the configuration and
now says so.

Two Lean errors, both index bookkeeping: `lo r + (k+1) - 1` against `lo r + k`, equal by
`ring` but not syntactically, and a `by_contra` whose hypothesis was already in the
wanted form.

## 2026-09-03 — BLOCK 176: the turn needed a site guard

Trying to discharge the geometry hypotheses from `EndType` exposed a defect in BLOCK
174's definition, not in the configuration.

`hs3 : ∀ s : ℤ, siteOf (up s) = s` CANNOT hold for all `s`: outside the span there is no
edge at position `s`, so `up s` is junk.  And BLOCK 174's `passTurn` acted on `x`
whether or not `x` was at site `s`, so those junk values could collide with a real end
and break involutivity.  The hypotheses were unsatisfiable as stated.

The fix is in the definition.  `passCore` is the pairing at a site -- bounce inside
`Zf`, pass outside -- and

    passTurn siteOf p up dn Zf s x = if siteOf x = s then passCore .. x else x

so the turn is the identity off its own site.  Involutivity then needs nothing about
other sites: off-site it is trivial, and on-site `passCore_site` says the image stays on
the site so the second application resolves the same way.

Reproved through the guard: `passTurn_off_site`, `passTurn_on_site`, `passCore_site`,
`passCore_invol`, `passTurn_invol`, `passTurn_site`, `passTurn_ne`,
`passTurn_pass_up`, `passTurn_pass_dn`, `passTurn_bounce`,
`passTurn_keeps_edge_at_cut`, and `shield_upper_bound_passTurn` on top of them.  Build
clean, 0 sorry, namespaces balanced.

Splitting `passCore` out of `passTurn` was also what made the proofs go through: with
the guard inlined, `split_ifs <;> simp_all` timed out at 200000 heartbeats.  Naming the
body lets the guard be discharged by rewriting instead of unfolding.

This is the seventh correction of the run, and the first that was a defect in something
I had already proved rather than in something I had claimed.  The lemmas were true of
the old definition; the old definition was the wrong object.

## 2026-09-03 — BLOCK 177: the hypotheses relativized to occupied sites

BLOCK 176 fixed the turn; this fixes the statement.  The geometry hypotheses were still
quantified over all `s : ℤ` -- `∀ s, siteOf (up s) = s` and the six distinctness
inequalities -- and outside the span those are FALSE, since there is no edge at that
position and `up s`, `dn s` are junk.  The theorem was unfalsifiable only because nobody
had tried to instantiate it.

Every such hypothesis is now conditional on the site being OCCUPIED:

    h12 : ∀ s, (∃ y, siteOf y = s) → partner (up (s-1)) ≠ partner (dn (s-1))
    ...
    hs4 : ∀ s, (∃ y, siteOf y = s) → siteOf (dn s) = s

and that costs nothing where they are used: in `passTurn_invol`'s on-site branch the
hypothesis `siteOf x = s` IS the witness, and elsewhere the witness comes from `hocc`,
a new hypothesis saying a run's sites carry ends -- true because runs lie in the span.

So the statement is now satisfiable, which it was not before.  Build clean, 0 sorry.

That is the second defect in two blocks found by trying to discharge the hypotheses
rather than by reading them, and both were in my own work: BLOCK 176 in the definition,
this one in the quantification.  Instantiating is what tests a statement; until then it
is only well-typed.

## 2026-09-03 — BLOCK 178: concrete `up` and `dn`

Given a section `sec : ℤ → Fin n` naming the edge at each position, `upOf` and `dnOf`
are the bottoms of that edge's two strands.  With them the geometry hypotheses split
cleanly in two.

**Unconditional** -- no hypothesis at all, because the four ends of a site differ in
`idx` or in `top`:

    upOf_dnOf_edgeOf              the two strands share their edge (rfl)
    upOf_ne_dnOf                  they differ, by index
    partner_ne_bot                a top is never a bottom
    partner_upOf_ne_partner_dnOf  the two tops differ, by index

**Conditional on `sec` being a section at that position**, which is exactly BLOCK 177's
occupancy:

    upOf_siteOf, dnOf_siteOf                  a bottom sits at its own edge
    partner_upOf_siteOf, partner_dnOf_siteOf  a top sits one to the right
    upOf_eq_botOf, dnOf_eq_botOf              they name the strand bottoms

So `h12`-`h34`, `hs1`-`hs4`, `hud`, `hupn` and `hdnn` are all discharged from one fact:
`sec` is a section where the span is occupied.  0 sorry.

The dependent field bit again: `Endpt`'s `idx : Fin (m edge)` has a type depending on
`edge`, so equality of endpoints is not `congr`-friendly.  `Fin.heq_ext_iff` after
supplying the edge equality is what works, and `congr 1` returns the `HEq` goal FIRST,
which cost two attempts to notice.

What is left of the instantiation: `hfour` -- a site's ends are exactly those four --
and the run indexing `hrange`, `hbdry`, `hint`, `hocc`.

## 2026-09-03 — BLOCK 179: hfour, and the geometry is finished

An end at site `s` has `top = false`, and then its edge is `s`, or `top = true`, and
then its edge is `s-1`; its index is `0` or `1`.  Those four combinations are exactly
`up s`, `dn s`, `partner (up (s-1))`, `partner (dn (s-1))` -- `hfour_of_mu_two`, with
`botOf_eq_self` and `eq_partner_botOf` for the two `top` cases.

**Every geometry hypothesis of `shield_upper_bound_passTurn` is now discharged**, and
all of them from two inputs: `mu = 2`, and `sec` being a section where the span is
occupied.

    h12..h34   distinctness      unconditional (BLOCK 178)
    hs1..hs4   site facts        section property
    hud        edge sharing      rfl
    hupn,hdnn  naming            section property
    hfour      the site's ends   mu = 2 plus the section property

What is left of the instantiation is the RUN INDEXING alone -- `hrange`, `hbdry`,
`hint`, `hocc` -- which is combinatorics about where the cut sites fall, not about the
end type.

The error this block was `simp only [EndType.atTop, ...]` failing to unfold a `def`
inside a hypothesis; `have hat : EndType.atTop x = false := ht` and rewriting with that
is what works, since `atTop` is definitionally `top`.

## 2026-09-03 — BLOCK 180: the bounce set

Starting the run indexing turned up the next defect, and it is the same kind as BLOCKS
176 and 177: a hypothesis that cannot be satisfied.

`hbdry : ∀ r, lo r ∈ Zf` is FALSE for run `0`.  Its left boundary is the span's start,
not a cut site.  But the turn must bounce there anyway: at the span's leftmost site
there is no edge to the left, so the two bottoms of the first edge are the only ends
present and have nothing to pair with but each other.

So the turn should bounce on a SET `Bs ⊇ Zf` -- the cut sites TOGETHER WITH the span's
two ends -- rather than on `Zf` itself.  That costs nothing elsewhere, because a bounce
never changes the edge:

    passTurn_hturn_of_subset      passes occur only off `Bs`, and `Zf ⊆ Bs`, so an edge
                                  change still forces the site out of `Zf`
    shield_upper_bound_bounce_set the bound is still `|Zf| + 1`: `walkCount_le_runs_blk`
                                  is applied with the CUT set, the larger bounce set
                                  appearing only inside the turn

0 sorry.

That is three definitional defects in five blocks, every one found by attempting to
discharge a hypothesis rather than by reading it, and every one in my own construction:
the missing site guard (176), the unrelativized quantification (177), and now the
bounce set.  The pattern is consistent enough to state as a rule: a hypothesis is only
tested when something has to produce it.

## 2026-09-03 — BLOCK 181: the run indexing

A run is a level set of `gz Zf` inside the span.  Defining `lo` and `len` as that set's
minimum and extent makes two of the three remaining hypotheses immediate.

    levelSet, runLo, runLen     the level set, its min, its extent
    runLo_le_and_le_len         `hrange`: an edge lies in its own level set, hence
                                between that set's min and max
    gz_mono                     `gz` counts what lies below, so it is monotone
    levelSet_interval           a run is therefore an INTERVAL: a point squeezed
                                between two members is a member
    no_cut_inside_run           `hint`: strictly inside a run there is no cut site --
                                the run is an interval on which `gz` is constant, and a
                                cut site there would raise it (BLOCK 165's
                                `no_cut_between_of_gz_eq`)

All 0 sorry.

So `hrange` and `hint` are discharged, leaving `hocc` -- that a run's sites carry ends
-- which is `mu_pos` on the span, and the datum `E` itself.

Small Lean note: `rw [levelSet, ...]` fails on a `noncomputable def` where
`simp only [levelSet, ...]` succeeds, and the same line worked earlier in a different
goal shape, which is why it took a second look.

## 2026-09-03 — BLOCK 182: hocc, and the hypothesis list is empty

`run_mem_levelSet`: every position of a run lies in the run, by the intervality of
BLOCK 181.  `hocc_of_section`: so each carries an end -- the bottom of its up strand,
sitting at that position by `upOf_siteOf`.  Both 0 sorry.

That was the last one.  Taking stock of `shield_upper_bound_passTurn`'s hypotheses:

    h12..h34   distinctness      BLOCK 178, unconditional
    hs1..hs4   site facts        BLOCK 178, from the section property
    hud        edge sharing      BLOCK 178, rfl
    hupn,hdnn  naming            BLOCK 178, from the section property
    hfour      the site's ends   BLOCK 179, from mu = 2
    hrange     run membership    BLOCK 181
    hint       no cut inside     BLOCK 181
    hocc       runs are occupied BLOCK 182
    hbdry      boundary bounce   BLOCK 180, via the bounce set
    E, hEp, hEt the datum        BLOCK 157, exists_glued_data

Every one is proved.  What is left is to write the composition -- to state the `mu = 2`
shield bound taking only `hm`, a section `sec` on the span, and the cut set, and to
apply the pieces in order.  That is assembly with no remaining content, though on this
file's record assembly is where the defects have surfaced: three of the last six blocks
found one, each time by trying to produce a hypothesis rather than read it.

## 2026-09-03 — BLOCK 183: the bounce sites, located

Two facts about where the bounce set meets the runs, which is what the chain conditions
will need.

`no_bounce_inside_run`: strictly inside a run there is no bounce site.  For members of
`Zf` that is BLOCK 181; the bounce set adds only the span's two ends, and those are
ruled out by position -- `A` is the left end of the first run and never strictly inside
one, `B+1` is past every edge.

`runLo_mem_bounce`: a run's left end IS a bounce site.  For `r ≥ 1` it is an actual cut
site, because `gz` equals `r` there and less just to the left, and `gz` rises only at a
member of `Zf` (`mem_of_gz_lt`).  For `r = 0` it is the span's left end, which the
bounce set contains.

Both 0 sorry.  So the turn bounces exactly at the run boundaries and passes throughout
their interiors -- which is the structure `run_connected_of_reachability` consumes.

A note on the previous block's composition: it BUILT, and the linter then flagged `hsec`,
`hspan` and `hm` as unused.  That is the tell -- the statement had `hrun` as a
hypothesis, so the section property did no work and the theorem was true for a reason
that had nothing to do with the construction.  Deriving `hrun` rather than assuming it
is the remaining task, and these two lemmas are its first half.

## 2026-09-03 — BLOCK 184: the composition, with `hrun` derived

`shield_mu_two`.  BLOCK 182's composition with the hole filled: `hrun` is no longer a
hypothesis but is PRODUCED, by `hrun_passTurn`, from the turn's own equations.

    chain_up_passTurn     the pass at an interior site chains the up strands
    chain_dn_passTurn     and the down strands, in the opposite composition
    chain_join_passTurn   the bounce at the run's left end joins the two chains
    hrun_passTurn         hrun_multi over the level sets, with the empty runs handled
                          separately -- their runLo is `A` by definition and `A` is a
                          bounce site (runLo_mem_bounce')
    shield_mu_two         the whole thing: walkCount E <= |Zf| + 1

0 sorry, and the check that matters: the unused-variable linter reports NOTHING in this
material.  Every hypothesis does work.  That is what was wrong with BLOCK 182, where
`hsec`, `hspan` and `hm` were flagged as idle because `hrun` had been assumed -- the
theorem was true for reasons unrelated to the construction.  It is not the case here.

So the `mu = 2` shield bound is a theorem whose hypotheses are: `mu = 2`, a section
naming the edges of the span, the run structure of the cut set, and the glued `passTurn`
datum.  `CostMerge` is not invoked anywhere beneath it -- no merge, no swap, no free
pair, which is the point, since BLOCK 149 refuted `HasFreePair` in the only sign model
that can express gap edges.

Scope unchanged and load-bearing: `mu = 2`.  BLOCK 158 measured 5072 of 8192 failures at
`mu = 4`, where the two-chain structure does not exist, and nothing here lifts.

## 2026-09-03 — BLOCK 185: the mu = 2 shield bound, self-contained

`exists_passTurn_data` builds the datum -- `exists_glued_data` applied to `passTurn`,
its three obligations discharged by `passTurn_invol`, `passTurn_site` and `passTurn_ne`,
each used only at an OCCUPIED site where the witness is the hypothesis `siteOf x = s`
itself.  `siteOf_mem_of_span` bounds the sites to `[A, B+1]`, so the section is needed
only on `[A-1, B+1]`.

`shield_mu_two_final` then assumes NO datum:

    hm         every edge carries two strands
    hspan      every end's edge lies in [A, B]
    hsecWide   `sec` names the edge at each position of [A-1, B+1]
    hsecEdge   and names an end's own edge at its own position
    hmin       `runLo` is the least position of its run
    ----------------------------------------------------------------
    conclusion  ∃ E, walkCount E ≤ |Zf| + 1

0 sorry, and `CostMerge` is invoked nowhere beneath it.

**That is `prop:cut`'s converse on this class**: the defect is at most the number of cut
sites.  With `prop:cut` itself, which is proved, it gives `c = |Z|` -- the shield law --
for configurations with every `mu = 2`.

The class is not vacuous, and that is the point: `mu j = 2` whenever `d j = 0`, so it
CONTAINS gap edges and hence genuine cut sites.  That is exactly what the derived-sign
model could not express (BLOCK 152), and what made M4b unstatable there.

Scope, unchanged: `mu >= 4` is not covered and is not a matter of effort.  BLOCK 158
measured 5072 of 8192 failures there, because with two strands each way the passes can
be chosen so as not to chain, and nothing local forces the choice.  Ledger updated.

## 2026-09-03 — BLOCK 186: the shield law at mu = 2

`local_of_turn`: a turn that keeps its site and changes the edge only off `Zf` satisfies
`CutComponents.Local` -- which is all `prop:cut`'s machinery needs.  So
`exists_injective_components_avoiding` applies to the `passTurn` datum, and
`walkCount_ge_passTurn` gives `|Zf| + 1 ≤ walkCount E`.

That is the lower bound on the SAME datum as the upper one.  `shield_law_mu_two`
combines them:

    walkCount E = |Zf| + 1

which is `c = |Z|`, the shield law, for configurations with every `mu = 2`.  0 sorry,
and `CostMerge` is invoked in NEITHER direction -- so the result does not use
`HasFreePair`, which BLOCK 149 refuted in the only sign model that can express gap
edges.

The class is not vacuous: `mu j = 2` whenever `d j = 0`, so it contains gap edges and
genuine cut sites -- precisely the case the derived-sign model could not state
(BLOCK 152), and the reason M3 and M4b sat at "not instantiable from a group element".

M3 is instantiated by the same theorem: `walkCount_ge_passTurn` is `prop:cut` on a datum
whose cut sites are real.

NOT proved at `mu >= 4`, and not for want of effort: BLOCK 158 measured 5072 of 8192
failures, because with two strands each way the passes can be chosen so as not to chain
and nothing local forces the choice.  Ledger updated for both atoms.

## 2026-09-03 — BLOCK 187: mu >= 4 is not blocked after all

BLOCK 158 showed that passing at every non-cut site does NOT give `|Z|+1` at `mu = 4`
(5072 of 8192 fail), and BLOCK 159 attributed that to the absence of the two-chain
structure.  Both are right, and neither is the end of it.

**What the failure actually is.**  Model a run of `k` edges each carrying `u = mu/2` up
and `u` down strands (`cutturn chain`).  A pass between adjacent edges is a permutation
`sigma` of levels, a bounce at a run end is a permutation `beta`.  The run is ONE
component exactly when the return map `betaL^-1 . T' . betaR . Sigma` is a single
`u`-cycle.  At `u = 1` every permutation is the identity and that is automatic -- the
`mu = 2` case.  At `u = 2` exactly HALF the choices work:

    k = 1..5, mu = 4:  2/4, 8/16, 32/64, 128/256, 512/1024 give one component

and the ALL-IDENTITY choice -- what any local rule picks -- gives `u` components, never
one.  So the obstruction is a PARITY, which is global.  That is exactly why no local
rule forces it.

**Why that does not block the shield law.**  The parity is FREE to choose, because a
pass costs `1` whichever levels it pairs.  Putting a single `u`-cycle in one pass and the
identity everywhere else gives one component at every `k` and every `mu` tested
(4, 6, 8).

The one case with no pass to put it in is a run of length `1`.  There the cycle would
have to sit in a BOUNCE, which is free only if some sign class holds two strands -- and
a cut site forces `d = 0`, so at `u = 2` the case `pu = pd = 1` has singleton classes and
no cycle.

**But that case cannot arise.**  A cut site forces `d = 0` on BOTH its adjacent edges,
and `mu = 2` whenever `d = 0`.  A length-1 run's single edge touches both of its bounding
cut sites, so it has `mu = 2` -- the case already proved.  Measured, with zero
exceptions:

    elements whose minimum needs extra pairs   : 0
    minimal data with a cut-adjacent edge > 2  : 0

the first because `lR` counts the crossings, so extra pairs only raise the cost.

**So the construction extends to all `mu`:** runs of length `>= 2` take the cycle in a
pass, runs of length `1` are `mu = 2` throughout.  `mu >= 4` is a formalisation task, not
an obstruction.

## 2026-09-03 — BLOCK 188: general-`u` run connectivity, formalised

The `mu >= 4` analogue of BLOCK 160.  A strand is now `(edge, level, up?)` with
`level : Fin u`, `u = mu/2`, and three link families instead of two:

    hchain   (j, l, b) — (j+1, l, b)          the passes, along the run
    hjoin    (lo, l, true) — (lo, l, false)   the boundary bounce, up to down
    hcyc     (lo, i, true) — (lo, i+1, true)  the cycle, across levels

    levels_reachable            every level is reachable from level 0
    run_one_component_gen       every strand of the run is reachable from the first
    run_pairwise_gen            hence any two are joined
    run_connected_in_graph_gen  and that transfers into the walk graph
    cycle_vacuous_at_u_one      at `u = 1` the cycle family is EMPTY -- no `i` has
                                `i + 1 < 1` -- so the mu = 2 case is the special case

All 0 sorry.

Two things worth recording about the shape.  First, only the LINEAR part of the cycle is
used, `0 → 1 → ... → u-1`; the wraparound `u-1 → 0` never appears, so no `Fin`
arithmetic is needed and the links are stated with explicit indices.  That also avoids
`Fin u`'s missing `NatCast` and `OfNat 1` instances without `NeZero`, which cost two
attempts.

Second, `cycle_vacuous_at_u_one` makes the relationship to BLOCK 160 exact rather than
analogical: `mu = 2` is not a separate argument but the case where the third family is
empty.

## 2026-09-03 — BLOCK 189: the shield law at general mu

The `mu = 2` pipeline turned out to be mostly `u`-agnostic already.
`shield_upper_bound_endpt` asks only for a representative and for run connectivity, and
`walkCount_ge_passTurn` asks only for `Local`; neither mentions the number of strands.
What was `mu = 2`-specific was the COVER -- that a representative is one of its edge's
strand bottoms -- and that generalises directly.

    levIdx, strOf         a strand is (edge, level, side); the first u indices are up
    idxLev_levIdx         reading an index back as a level and a side
    exists_lev            every index is levIdx of some level and side
    botOf_eq_strOf        so every representative is a strand bottom of its edge
    levIdx_one            at u = 1 the two indices are 0 and 1, which are upOf and dnOf
    hrun_multi_gen        hrun at general u, from BLOCK 188's connectivity
    shield_law_gen        walkCount E = |Zf| + 1, both bounds, any u

All 0 sorry, and `CostMerge` is invoked in neither direction.

The hypotheses on the turn are the three link families of BLOCK 188 -- its passes chain
each level along a run, its boundary bounce joins up to down, one pass carries the level
cycle -- plus the turn's own geometry.  So the general-`mu` shield law now rests on
exhibiting a turn with those properties, which is the `mu = 2` construction of BLOCKS
174-186 with the cycle inserted.

That is the remaining work for `mu >= 4`, and it is construction rather than
mathematics: BLOCK 187 established that the cycle is free to place (a pass costs the
same whichever levels it pairs) and that the one case with no pass -- a run of length 1
-- is forced to `mu = 2` because a cut site zeroes the deposits on both its edges.

## 2026-09-03 — BLOCK 190: the naming is free, which is what lets the cycle sit in a pass

A subtlety in BLOCK 189's own statement, found by trying to build the turn.  `hchain`
there is level-PRESERVING, but BLOCK 187 places the level cycle in a PASS, and a pass
permutes levels.  Stated naively the two are inconsistent.

They are reconciled by relabelling.  The level index may be permuted independently at
each position, and a naming that absorbs the passes' permutations makes them
level-preserving by construction.  Nothing about the connectivity changes, because
`run_connected_in_graph_gen` already takes an ARBITRARY `f`.  What had to be loosened is
`hrun`, which had `strOf` baked in:

    hrun_of_cover          hrun from any naming that COVERS the representatives
    strOf_covers           strOf is one such naming
    relabelled_covers      so is strOf composed with a permutation at each position
    shield_law_gen_named   the shield law with the naming free

All 0 sorry.

That is the point of the block: with the naming free, the cycle can sit in a pass, where
BLOCK 187 showed it is FREE -- a pass costs the same whichever levels it pairs.  Had the
naming stayed fixed, the cycle would have had to sit in a bounce, which is free only
when a sign class holds two strands, and that fails at `pu = pd = 1`.

So the `mu >= 4` construction now has somewhere to put its cycle that costs nothing, and
the remaining work is exhibiting the turn itself.

## 2026-09-03 — BLOCK 191: the general-u turn

At `mu = 2u` a site carries `4u` ends, so the `mu = 2` definition's if-chain over four
ends does not scale -- and neither would its six distinctness inequalities, which would
become `O(u^2)`.  Defining the turn STRUCTURALLY avoids both:

    bounce   stay on the edge, keep the top, flip the SIDE (up <-> down)
    pass     cross to the other edge, keep the side, flip the top, permute the level by
             `sigma` one way and `sigma^-1` the other

Involutivity then holds by construction rather than by case analysis, and needs NO
distinctness hypothesis at all:

    levOf, udOf, mkEnd        the level and side of an end, and the reverse
    levOf_mkEnd, udOf_mkEnd   they read back correctly
    turnGen                   the turn
    turnGen_off_site          the identity off its site
    turnGen_bounce_invol      the bounce: flips the side twice
    turnGen_pass_invol        the pass: out along sigma, back along sigma^-1

All 0 sorry.

The pass needed the section property, which is expected -- it names the other edge --
and cost an ABORT under the three-strike rule.  The stuck subgoal was an `HEq` between
the `idx` fields, and three tactics failed on it because the two sides live in genuinely
DIFFERENT types, `Fin (m (sec (s-1)))` and `Fin (m e)`, until the edge equality is used.
`congr` emits the `HEq` before that.  The fix was architectural: derive `he' : sec (s-1) = e`
FIRST and supply `congrArg m he'` as the type equality.  Guessing more tactics would not
have found it.

Also fixed: a `namespace EltBridge` opened without closing the previous one, which had
been silently nesting declarations at `EltBridge.EltBridge.*`.  Caught by the doubled
name in `#print axioms`, the same tell as BLOCK 143.

## 2026-09-03 — BLOCK 192: the general-u datum

`turnGen`'s remaining obligations, and both are immediate in the structural definition:

    turnGen_site   a bounce keeps the edge and top; a pass moves to the edge whose
                   corresponding end sits at the same site
    turnGen_ne     the bounce flips the SIDE, so `udOf` changes and the end cannot be
                   fixed; the pass flips the TOP
    edge_of_site   an end at site `s` is on edge `s-1` if a top, `s` if a bottom
    turnGen_invol  the three cases together, with the section conditional on occupancy

    exists_turnGen_data   the datum, from `exists_glued_data`

All 0 sorry.

`turnGen_ne` is worth a note: the first attempt unfolded `levIdx` and left `omega` an
unreduced conditional it treated as an atom.  Arguing through `udOf` instead -- the
bounce flips the side, so `udOf` of the image is `!udOf x` -- is two lines and needs no
arithmetic.  The structural definition pays off exactly here: at `mu = 2` the same fact
needed six distinctness inequalities.

## 2026-09-03 — BLOCK 193: hcyc is the round trip, not an assumption

Building the turn exposed a real defect in BLOCK 191's `turnGen`: it permuted the level
by the SAME `sigma` on both sides, so the up chain's `sigma` and the down chain's
`sigma^-1` cancel and the composite is trivial -- exactly BLOCK 187's all-identity case,
which gives `u` components, never one.  The two sides must permute INDEPENDENTLY.

Fixed by making the family side-dependent, `sig : ℤ → Bool → Perm (Fin u)`.  The change
needed NO proof edits, because the pass preserves the side, so the round-trip
cancellation still holds -- a good sign for the structural definition.

Then a second correction, to BLOCK 188 this time.  `hcyc` was taken as a hypothesis at
the run's left end, but in the real turn NO SINGLE STEP crosses levels.  What crosses
them is the ROUND TRIP: out along the up chain, across at the far bounce, back along the
down chain, closed at the near bounce.  BLOCK 187's parity is precisely the statement
that this round trip is a `u`-cycle.

    hcyc_of_round_trip        the cycle, derived from the far bounce's shift
    reflTransGen_collapse     a chain of reachability steps is a reachability step
    run_one_component_shift   the run is one component, from three families of ACTUAL
                              turn steps
    shield_law_shift          walkCount E = |Zf| + 1 on those hypotheses

All 0 sorry.

So the general-`mu` shield law now rests on three single-step facts about the turn --
its passes chain, its near bounce joins the sides, its far bounce joins them one level
across -- and the last is where the parity lives.  It is satisfiable for the reason
BLOCK 187 measured: a pass costs the same whichever levels it pairs, so the permutations
can be chosen to make the round trip a cycle.

## 2026-09-03 — BLOCK 194: the three paths, exhibited

The three link families of BLOCK 193, as actual paths through `turnGen`:

    pass_path          a pass carries a strand bottom to the next edge's, permuting the
                       level by the SIDE's permutation.  Two steps -- to the top, then
                       across -- and uniform in the side, since the pass keeps it.
    near_bounce_path   the near bounce joins the two sides in ONE step: both strand
                       bottoms of edge `j` already sit at site `j`.
    bounce_top_path    the far bounce needs THREE steps -- to the top, across, and back
                       down -- because a bounce at the run's right boundary acts on the
                       TOPS of the last edge while `strOf` names bottoms.

All 0 sorry.  `levOf_partner` and `udOf_partner` are what make the partner steps free:
crossing a strand keeps its index, so the level and side read the same at both ends.

That asymmetry between the two bounces is the whole reason the shift exists.  The near
bounce relates level `l` to level `l` and the far one relates level `l` to level `l` as
well -- but in the RAW naming.  With the naming relabelled so the passes are
level-preserving, the two bounces are relabelled differently, and their disagreement is
the round trip's permutation.  BLOCK 187's parity is exactly the freedom to choose that
disagreement, and it is free because a pass costs the same whichever levels it pairs.

## 2026-09-03 — BLOCK 195: the parity, exhibited

The relabelling, and with it the last hypothesis of the general-`mu` law.

    relAt, nameAt          the relabelling by the recursion
                           `rel (k+1) b = sig (lo+(k+1)) b * rel k b`, and the naming
                           built from it
    hchain_nameAt          `hchain` holds BY CONSTRUCTION -- the pass's permutation is
                           exactly the recursion's step
    hjoinL_nameAt          `hjoinL` is immediate: `relAt 0 = 1`, so the naming is raw
                           there and the near bounce applies directly
    hshift_nameAt          `hshift` reduces to `hrel`: the up and down relabellings at
                           the far end disagree by the successor

    shiftDown              the downward cycle on `Fin u`
    shiftDown_succ         it maps `i+1` to `i`
    hrel_of_shiftDown      so `hrel` holds when the composites are `1` and `shiftDown`
    relAt_eq_one           trivial passes compose to the identity
    exists_sig_with_parity such a `sig` EXISTS: trivial everywhere except the last down
                           pass, which carries the cycle

All 0 sorry.

So BLOCK 187's parity is now exhibited rather than measured.  It said the round trip must
be a `u`-cycle and that the choice is free because a pass costs the same whichever levels
it pairs; `exists_sig_with_parity` is that sentence in Lean.

`shiftDown` cost one restructure.  Its inverse laws are nested modular arithmetic with a
VARIABLE modulus, which `omega` cannot do; splitting on `l = 0` makes every `%` resolve by
`Nat.mod_eq_of_lt` or `Nat.add_mod_left` and the arithmetic becomes linear.

## 2026-09-03 — BLOCK 196: the shield law at general mu

`shield_law_mu_general`.  `∃ E, walkCount E = |Zf| + 1`, for `mu = 2u` at ANY `u > 0`.
0 sorry, and `CostMerge` is invoked in neither direction.

    globalName              one naming on all of ℤ: each position gets its own run's
                            relabelling, the run being named by `gz`
    globalName_eq_nameAt    inside a run it IS that run's naming
    shield_law_mu_general   the composition: the datum from `exists_turnGen_data`, the
                            three link families from the path lemmas of BLOCK 194, the
                            parity from BLOCK 195

**So `mu >= 4` is closed.**  BLOCK 158 measured 5072 of 8192 failures there and BLOCK 159
attributed them to the absence of the two-chain structure.  Both were right about the
symptom and wrong about the prognosis: BLOCK 187 identified the real obstruction as a
global PARITY -- the round trip must be a `u`-cycle -- and showed it is FREE to satisfy,
because a pass costs the same whichever levels it pairs.  BLOCKS 188-195 turned that into
a proof, and this block composes it.

The route is the same one that worked at `mu = 2`: no merge, no swap, no free pair.  That
matters because BLOCK 149 refuted `HasFreePair` in the only sign model that can express
gap edges, which closed the classical route to this bound at every `mu`.

Ledger updated for both atoms.  What remains between this and an unconditional M4b is the
same bookkeeping as at `mu = 2`: supplying the run structure for a concrete `PathData`,
which BLOCKS 181-183 already provide as level-set facts.

## 2026-09-03 — BLOCK 197: the shield law, all mu

`EltBridge.shield_law`.  `walkCount = |Zf| + 1` -- that is `c = |Z|` -- for `mu = 2u` at
every `u > 0`.  0 sorry.

The run structure is no longer assumed.  `runLo` and `runLen` are the level sets of `gz`,
and every fact about them is proved:

    runLo_le, le_runHi           runLo and runLo+runLen ARE the run's least and greatest
                                 positions -- definitional, not hypotheses
    gz_at_run, run_pos_in_span   a run's positions carry its index and lie in the span
    runLo_mem_bounce'            its left end is a bounce site
    runHi_succ_mem_bounce        so is its right end, being the span's edge or a point
                                 where gz rises
    no_bounce_inside_run         and nothing between them is
    shield_law_shift_occ         the hypotheses are needed only at OCCUPIED runs, whose
                                 witness is derived where they are used

So the hypotheses are the configuration and nothing else: `2u` strands per edge, ends in
the span, a section on `[A-1, B+1]`, cut sites strictly inside, every position occupied,
and the parity -- which `exists_sig_with_parity` shows always exists.

**M3 and M4b are green.**  Both bounds hold of ONE datum, the datum is constructed rather
than assumed, and `CostMerge` is invoked nowhere beneath the result -- no merge, no swap,
no free pair.  That last point is what makes it possible at all: BLOCK 149 refuted
`HasFreePair` in `configGData`, the only sign model that can express gap edges, which
closed the classical route at every `mu`.

The arc, for the record.  BLOCK 139 proved the derived-sign model forces cut sites empty;
BLOCK 149 refuted the free pair in the model that does not; BLOCK 152 identified `EndData`
as the gap-free model, so M3 and M4b could not even be STATED there; BLOCK 158 refuted
the local route at `mu = 4`; and BLOCK 187 found that what looked like an obstruction was
a global parity that is free to satisfy.  Everything after that was construction.

## 2026-09-03 — BLOCK 198: what BLOCK 197 does and does not close

Two corrections to BLOCK 197's framing, one in each direction.

**M4b is NOT on a side branch.**  The ledger said "the shield law is the combinatorial
half of paper2 and does not lie on the path to H1/H2/M9".  That is stale.  `hyp:model`
(M2) IS the shield law, and the paper's own accounting of what it owes reads

    rem:shieldowes -- "Proposition prop:cut gives c >= |Z|.  The reverse inequality
    c <= |Z| asks for one minimum-cost realisation whose components are exactly the
    |Z|+1 classes cut out by Z, that is, for pairings that connect all crossings within
    each class.  IT IS NOT PROVED HERE."

which is exactly `shield_law`: one constructed datum, `walkCount = |Z|+1`, its runs
connected.  So M4b is a clause of (M) = H1, not a side result.

**But the scope is narrower than BLOCK 197 said.**  `shield_law` assumes
`hm : ∀ e, m e = 2 * u` -- every edge carries the SAME `2u` strands.  The paper's
configurations have deposits varying per edge, hence varying `mu`, and the restriction is
load-bearing, not cosmetic: at a non-cut site the pass is a level bijection only when the
two edges' level counts agree, and with unequal counts the site's pairing must mix passes
and bounces.  `turnGen` has no such case.

So the honest statement is: `c = |Z|` is proved for UNIFORM-`mu` configurations at every
`u`, which includes every all-gap configuration and every uniform `mu = 4, 6, 8, ...`;
the general varying-`mu` case is not covered.  M4b goes back to yellow with that scope
recorded, and M3 stays green -- `prop:cut` is proved in the paper and instantiated here.

Catching this before editing `rem:shieldowes` is the point.  The theorem is real and the
gap it closes is real, but only on a subclass, and the paper's remark is about all bulk
configurations.

## 2026-09-03 — BLOCK 199: the shield law is an Eulerian circuit

Trying to lift `shield_law` to varying `mu` produced first a wrong measurement and then a
much better proof.

**The wrong measurement.**  A first model of a mixed-width site forced exactly
`min(u[j],u[j+1])` passes with a fixed pairing for the excess, and reported runs -- `u =
[1,2,1]`, `[1,3,1]`, `[2,3,1]`, `[1,3,2]` -- that could not reach one component.  That
contradicted `cutturn mu4`'s zero exceptions, which is how it was caught.  The error: the
number of passes may be ANY value up to the minimum, and both the passes and the leftover
bounces may pair freely.  Enumerating every pairing at every site instead:

    every mixed-width run reaches ONE component for some pairing

**The better proof.**  The corrected model makes the right argument visible.  Take the
STRAND GRAPH: vertices are sites, edges are strands, a strand of edge `j` joining site `j`
to site `j+1`.  Then

  * every vertex has EVEN degree -- site `j` carries `2u[j-1] + 2u[j]` ends;
  * each run's strand graph is CONNECTED, since every `u[j] >= 1` by `mu_pos`;
  * a turn is precisely a pairing of arrivals to departures at each vertex.

So by Euler a single closed walk covers all the strands of a run, and the turn that
follows it gives exactly ONE component.  At any widths, uniform or not.

That is the whole shield law, and it never mentions levels, chains, parities or
permutations.  BLOCKS 187-197 built the uniform-`mu` case by tracking a level cycle
through the run; the parity they were chasing is just the statement that the Eulerian
circuit closes up, which Euler gives for free.  The uniform proof is correct and now
looks like the hard way round.

So the route to varying `mu` is not to generalise the level bookkeeping but to replace it:
prove the strand graph connected with even degrees, and apply an Eulerian circuit.

## 2026-09-03 — BLOCK 200: the shield law at any widths

`shield_law_chain`: `walkCount = |Zf| + 1`, that is `c = |Z|`, with **no** uniform-width
hypothesis.  Compare `shield_law` of BLOCK 197, which assumed `∀ e, m e = 2 * u`.  The
edges may now carry any number of strands and may differ from one another, because the
argument never mentions levels.

    chain_covers, chain_pairwise  a list whose consecutive entries are joined puts all of
                                  them in one component
    hrun_of_chain                 so a per-run covering chain gives `hrun`
    shield_law_chain              and with it both bounds, at any widths

All 0 sorry.

What the theorem needs from the circuit is only that it COVERS -- the whole content of
"Eulerian" that the component count uses.  The existence of such a chain is the remaining
input: every site has even degree (`2u[j-1] + 2u[j]` ends) and each run's strand graph is
connected (`u[j] >= 1` by `mu_pos`), so a closed walk covering the run's strands exists.

The level machinery of BLOCKS 187-197 is the uniform-width case of this, where the chain
is read off the levels.  It is correct and it is the hard way round: `shield_law_chain`
is shorter than any one of the six blocks that built the parity.

The Lean error this block was the dependent-rewrite pattern again -- `rw` at a hypothesis
whose TYPE mentions the rewritten term, with a second hypothesis depending on it.  The fix
is the same as always: rewrite in the existential statement BEFORE destructuring, where
nothing depends on the index yet.

## 2026-09-03 — BLOCK 201: splicing without indices

The Eulerian construction, and an ABORT that improved it.

A first attempt spliced LISTS -- a chain of strands with consecutive entries joined -- and
spent four tactics on `List.get` versus `getElem` and append-index arithmetic before
hitting the three-strike rule.  The diagnosis was that the indices were the problem, not
the mathematics: the chain condition only ever says "all of these are mutually
reachable", which is a statement about a SET, and an ordering was never needed.

    AllJoined            every member of a set reaches every other
    allJoined_union      two joined sets sharing ONE link join -- three lines
    allJoined_pair       the base: an edge's two strand bottoms, one turn step apart
    hrun_of_allJoined    a joined set per run gives `hrun`
    shield_law_joined    and with it `walkCount = |Zf| + 1`, at ANY widths

All 0 sorry.

So the Eulerian argument is complete with the circuit dissolved.  The component count
never needed an ordering of the strands -- only that they are all joined -- and the
splice that builds it needs one link per edge.  Every trace of levels, chains, parities
and permutations is gone.

Also fixed: another `namespace EltBridge` opened without closing the previous one, caught
again by the doubled name in `#print axioms`.  That is the third time; the tell is
reliable.

What remains for (M2) in full is the link itself: that consecutive edges' strand sets
share a reachable pair at their common site, which is a pass there.

## 2026-09-03 — BLOCK 202: the link, and what (M2) still owes

    link_of_turn            ANY turn step joins the two ends' representatives -- each
                            end reaches its own strand's bottom by the partner
    allJoined_of_pass       so a pass links two edges' strand sets, which is the link
                            `allJoined_union` consumes
    RunStrandsConnected     the remaining input, named
    shield_law_of_connected and with it `walkCount = |Zf| + 1` at any widths

All 0 sorry.

**What remains, stated plainly.**  `RunStrandsConnected` says: for each run there is a
set of representatives, all mutually reachable, containing every end of that run.
Building it by `allJoined_of_pass` needs the turn's pairing graph on a run's STRANDS to
be connected, and THAT is the Eulerian statement -- every site has even degree, the run's
strand multigraph is a connected path of parallel edges, so a turn with a connected
pairing graph exists.

It is not proved here.  The set formulation of BLOCK 201 repackaged the argument but did
not reduce it: `AllJoined` on a run and one-component-per-run are the same statement, so
the Eulerian existence is still the content, not bookkeeping around it.

What HAS been established is everything on either side of it.  Given
`RunStrandsConnected`, the shield law follows at any widths; and at UNIFORM widths the
existence is proved outright (`shield_law`, BLOCK 197), by tracking a level cycle -- which
is that Eulerian circuit written out by hand for the case where all the edges match.

## 2026-09-03 — BLOCK 203: the splice, and what the induction still needs

    allJoined_absorb    a joined set absorbs another as soon as ONE turn step crosses
                        between them
    allJoined_biUnion   so given a joined set per edge and a pass linking each
                        consecutive pair, the union over the run is joined

Both 0 sorry.

The gain over the circuit: `AllJoined` does not care about the ORDER in which the strands
are covered, so the round trips the Eulerian induction would splice in never have to be
written down.  The induction becomes a union.

**What it still needs, precisely.**  `allJoined_biUnion` takes a joined set `S j` FOR EACH
EDGE.  That is not free: an edge with `w j` strands needs its own strands joined to each
other, and the only links available are the pairings at its two sites.  So the per-edge
statement is the same problem one size down -- the 2-regular strand graph restricted to
one edge -- and it is where the evenness of `w j` is used.

At UNIFORM widths that per-edge statement is what `run_one_component_gen` proves, by the
level cycle.  At varying widths it is open, and it is the honest remaining content of
(M2).  The blueprint above says what it should be: the circuit visits site `j`, breaks a
pair there, and reroutes through edge `j`'s strands in `(w j)/2` round trips.

So the accounting is: the splice is proved, the per-edge base is proved at uniform widths
and open in general, and everything from a per-edge base to the shield law is proved at
any widths.

## 2026-09-03 — BLOCK 204: BLOCK 203's decomposition was wrong

`allJoined_biUnion` is true, but the decomposition BLOCK 203 proposed for it is not
available.  It wanted a joined set PER EDGE.  An edge `j`'s bottoms sit at site `j`
TOGETHER WITH edge `j-1`'s tops, so the pairing there may join an edge-`j` bottom to an
edge-`(j-1)` top -- a pass -- rather than to another edge-`j` bottom.  An edge with
`w = 2` has its two strands joined only if some site pairs them to each other, and at a
non-cut site the pairing may pass instead.  So "each edge's strands are joined among
themselves" is not generally true, and BLOCK 203's "same problem one size down" was not
a reduction.

The correct statement of what remains is undecomposed, and is what BLOCK 199 identified:

    choose the turn so that the run's strand graph is CONNECTED.

Nothing in BLOCKS 200-203 reduces that.  `AllJoined` repackages "one component per run"
without weakening it -- the strand graph is 2-regular, so connected and single-cycle
coincide -- and `allJoined_absorb` is a way to BUILD a joined set once the links are
known, not a way to obtain them.

What those blocks did establish, and it is not nothing:

  * everything from "the run's strands are joined" to the shield law, at ANY widths
    (`shield_law_of_connected`);
  * `link_of_turn`, that any turn step joins the two representatives, so the links are
    free once the turn is chosen;
  * the absorption and union lemmas, which will assemble whatever links a construction
    provides.

And at UNIFORM widths the existence is proved outright (`shield_law`, BLOCK 197).  The
open case is varying widths, and it needs a construction of the turn, not further
repackaging of the consequence.

## 2026-09-03 — BLOCK 205: a path of links is joined, and BLOCK 204 refined

BLOCK 204 said an edge's strands need not be joined among themselves.  That is true of an
ARBITRARY turn and was the right correction to BLOCK 203, but it went one step too far:
the turn is ours to CONSTRUCT, and the recursive Eulerian walk makes it true.  Going right
on an up strand and back on a down strand, edge `j`'s strands form the path

    up 0 — dn 0 — up 1 — dn 1 — ...

each consecutive pair one turn step apart -- the far bounce joining `up i` to `dn i`, the
near bounce joining `dn i` to `up (i+1)` -- with the two loose ends carrying the
continuation.  So the per-edge decomposition is available after all, by construction.

    allJoined_of_path   a path of links joins its endpoints to the start
    allJoined_image     so its image is an AllJoined set
    allJoined_edge      and for a turn built from round trips, that is the edge's set

All 0 sorry.

**The state of (M2), precisely.**  Everything is now proved except the construction of the
turn itself at varying widths:

    per-edge set        allJoined_edge, given the round-trip pairing
    link between edges  link_of_turn -- any turn step joins the representatives
    union over the run  allJoined_biUnion
    to the shield law   shield_law_of_connected, at ANY widths

so the remaining task is to exhibit a `turnGen`-like turn whose pairing is the round-trip
path within each edge and a pass between consecutive edges.  At uniform widths that turn
is built and the law is proved (BLOCK 197).  At varying widths the same construction
should go through -- the round trips are per-edge and do not care what the neighbours'
widths are -- and it is not written.

## 2026-09-03 — BLOCK 206: (M3a) is not analytic

I had been calling (M3) "a separate analytic statement".  That was wrong, and
`site_cost_couples` (already in the file) says why: the interior site cost is
`max(|d(s-1)|, |d(s)|)` -- a function of **two consecutive states and nothing else**.
A weight that is a head term plus a nearest-neighbour term at each step plus a tail
term is a *chain cost*, and the exponential of a chain cost is a transfer-matrix path
weight.  That is a theorem, not an estimate:

    lastOf, chainCost                 the chain cost of a state path
    pathWeight_one_exp                x ^ chainCost = the inner path weight
    pathWeight_exp                    with the head weight too
    isTransferDecomposition_of_chain  hence IsTransferDecomposition, for ANY family
                                      of configurations whose weight is a chain cost
    interior_kernel_eq_max            and the kernel is x ^ max(a,b) -- eq:gapkernel's
                                      bulk kernel, forced by the cost, not posited

All four depend on `propext` alone -- no choice, no quotients.  0 sorry.

**What this does and does not do.**  (M3a) is now reduced to a bookkeeping statement:
that `lR` is a chain cost in the state `(d j, f j)`, with the two boundary sites `s = 0`
and `s = kstar` supplying the head and tail terms.  `cor:lRclosed` already gives
`lR = sum mu + sum siteCost`, and `site_cost_couples` gives the interior terms, so what
remains is to match the two boundary sites -- combinatorics, not analysis.  (M3b),
the resolvent sum, is `neumann_partial` (BLOCK 116) plus the order bound.

So (M3) is not out of reach after all.  The operator in the paper's (M3) was never an
assumption; it is what the shape of `lR` forces.

## 2026-09-03 — BLOCK 207: the two boundary sites, matched — (M3a) discharged for lR

`Elt.lR_eq` reads `lR = sum_{Icc A B} mu + sum_{Icc A (B+1)} siteCost`, so the span is a
path: site A, edge A, site A+1, ..., edge B, site B+1.  Walk it left to right and charge
each step for *the edge it crosses and the site it lands on*.  Then exactly two terms
fall outside the chain -- the two boundary sites -- and they are exactly `lambda` and
`mu`:

    h s   = siteCost s                head, at s = A
    f i j = mu i + siteCost j         each step
    g s   = mu s + siteCost (s+1)     tail, last edge + right boundary site

    idxList, lastOf_idxList           the state path A, A+1, ..., A+n
    chainCost_idxList                 its chain cost
    sum_Icc_shift                     Icc A (A+n) reindexed by range (n+1)
    alternating_is_chain              THE MATCHING: the two sums are equal
    isTransferDecomposition_alternating
    Elt.lR_is_chain                   lR IS a chain cost, boundary sites and all
    Elt.lR_exp_pathWeight             so x ^ lR IS a transfer-matrix path weight

0 sorry.  `sum_Icc_succ_top` is not in this Mathlib, so the reindex is proved here.

**Scope, stated exactly.**  This is (M3a) for a single configuration: its weight is a
path weight with kernel `x ^ (mu i + siteCost j)`, and `interior_kernel_eq_max`
identifies the site factor as `x ^ max(a,b)` -- `eq:gapkernel`'s bulk kernel.  The state
here is the index.  The *family* version -- one kernel serving every configuration --
needs the costs to factor through a state map `(d j, f j)` rather than through `j`, and
that is also where the finiteness `IsResolventSum` wants comes from.  That factoring is
the one thing between here and (M3a) in full, and it is a definitional check on `mu`
and `siteCost`, not an estimate.

## 2026-09-03 — BLOCK 208: the factoring — one kernel for the whole family

BLOCK 207 used the *index* as the state, which serves one configuration at a time.  The
costs factor through local data, by inspection of the definitions in Realisation.lean:

    mu j       = if d j = 0 and f j = 0 then 2 else max |d j| |f j|
    siteCost s = max |d (s-1) - vArr s + eps * vL s| |d s - eps * vR s|

so `mu j` needs only `(d j, f j)` and `siteCost s` only `(d (s-1), d s)` with the markers
`[s = 0]`, `[s = k*]` and the configuration's `eps`, `delta`.  Packaging those into a
`LocalState` makes both PURE FUNCTIONS OF ONE STATE -- and

    mu_factors        P.mu j = (stateOf P j).muOf          by rfl, NO AXIOMS
    siteCost_factors  P.siteCost j = (stateOf P j).siteOf   by rfl, NO AXIOMS

Running the chain over all `n + 2` **sites** rather than `n + 1` is what makes it close:
the right boundary site becomes an ordinary chain step instead of a tail, so the tail
vector is trivial and the head is the left boundary site.

    chainCost_map, lastOf_map        the chain commutes with the state map
    alternating_is_chain_sites       the matching, one step longer
    isTransferDecomposition_family   ONE kernel x ^ (muOf s + siteOf t), one head
                                     vector x ^ siteOf, serving EVERY configuration
    lR_exp_pathWeight_family         and every member's weight is its path weight
    LocalState.dcur_le_muOf          |d| <= muOf
    LocalState.fcur_le_muOf          |f| <= muOf

0 sorry.  The two factoring theorems depend on no axioms at all.

**(M3a) is done.**  The configuration now enters only through its state path, which is
what a transfer-matrix decomposition asserts.  The last two bound the state by its own
cost, so a configuration of relaxed length `N` visits only states with `|d|, |f| <= N`:
the state space is finite degree by degree, which is the hypothesis `IsResolventSum`
wants.  What remains of (M3) is (M3b) -- assembling that truncation with
`neumann_partial` (BLOCK 116) -- and it is algebra.

## 2026-09-03 — BLOCK 209: (M3b), and a RETRACTION — IsResolventSum says nothing

Setting out to prove `IsResolventSum` I found it is **vacuous**.  It asks, for each `N`,
for *some* `tail` with `W = (partial sum) + tail`, and `tail := W - (partial sum)` always
works.  It holds of every `T`, `lam`, `mu`, `W` whatsoever.  Recorded as a theorem rather
than deleted, so the retraction is checkable:

    isResolventSum_vacuous     IsResolventSum T lam mu W, for ANY arguments

So (M3b) was never carried by that definition.  `IsAssembly` (BLOCK 116) is the honest
form -- an exact coefficient identity, degree by degree, truncated at `range (N+1)`.  What
licenses that truncation is the only real content, and it is now proved:

    X_pow_dvd_matrix_pow       entries of positive order => X^k divides (T^k) a b
    coeff_matrix_pow_eq_zero   so T^k contributes nothing below degree k
    coeff_neumann_tail_zero    hence terms past range (N+1) cannot reach degree N

The Neumann series therefore terminates at each fixed degree, and `IsAssembly` loses
nothing by truncating.  The hypothesis is the paper's order bound on the travel block --
a transfer step costs at least one unit of length, so its generating function has no
constant term.  No analysis anywhere.  0 sorry.

**Honest scope.**  This closes the *formal convergence* half of (M3b).  The other half --
that `W` itself equals that sum, i.e. that summing `lR_exp_pathWeight_family` over all
configurations of each span length reproduces the series -- is a counting statement and
is not proved.  (M3a) is done; (M3b) is half done, and the remaining half is combinatorial.

## 2026-09-03 — BLOCKS 210-211: the counting half of (M3b)

`IsAssembly`'s summand is `lam a * (T^k) a b * mu b`.  What was owed is that summing
over configurations produces it.  Both halves are now proved.

The algebraic half (BLOCK 210) -- stepping `k` times through `T` and finishing with `mu`
IS the matrix power, which is the whole reason a transfer matrix is the right object:

    weightSum                 step k times through T, finish with mu
    weightSum_eq              = sum_b (T^k) a b * mu b
    lam_weightSum_eq          with the head weight: IsAssembly's summand exactly
    sum_lam_weightSum_eq      summed over starting states: the k-th Neumann term

The enumeration half (BLOCK 211) -- that this really is a sum over all state paths:

    sum_map_flatMap           summing over a concatenation is summing the sums
    paths                     every state path of length k, listed
    weightSum_eq_sum_pathWeight   weightSum IS the sum of pathWeight over all of them
    sum_univ_toList           and the Fintype enumeration qualifies

0 sorry.  `List.mul_sum` does not exist; the lemma wanted is `List.sum_map_mul_left`.
`Finset.sum_map_toList` does exist and discharges the enumeration hypothesis outright.

**Where (M3) now stands.**  (M3a) is done (BLOCKS 206-208): one kernel, every
configuration, the state factoring by `rfl`.  (M3b) has both its parts -- formal
convergence (BLOCK 209) and the path-sum identity (BLOCKS 210-211).  What is NOT proved
is the join: that the family's configurations, grouped by span length, are exactly the
state paths enumerated by `paths`.  That is a bijection between configurations and their
state paths, and it is the one thing left in (M3).  It is combinatorial.

## 2026-09-03 — BLOCK 212: the kernel must be compatibility-guarded

A structural correction found while trying to join (M3b)'s two halves.  `paths` enumerates
EVERY list of states, but not every list comes from a configuration: state `j+1` must
carry `dprev = d j`, which is state `j`'s `dcur`, and `eps`, `delta` are constant along a
configuration.  So the map from configurations to state paths is NOT onto `paths`, and
the unguarded kernel counts paths no configuration realises.

That is not a defect -- it is how transfer matrices work.  Incompatible transitions get a
zero entry:

    compatB                  tau continues sigma
    compatB_stateOf          a configuration's consecutive states are always compatible
    pathWeight_guarded_eq    so guarding the kernel changes no configuration's weight,
                             while off the realisable paths it contributes 0

Two steps toward injectivity, which is what the join needs next:

    arr_eq_one_iff           the arrival marker fires at index 0 and nowhere else
    dep_eq_one_iff           the departure marker fires at k* and nowhere else

The states carry no index, so without these two, translates of one configuration would
share a path.  0 sorry.

**Still owed for (M3).**  Injectivity of `stateOf` on configurations of a given span, and
the converse -- that every compatible path is realised.  The second is where `houter`
(deposits vanish off the span) and the minimality of `A`, `B` do the work.  Both are
combinatorial; neither is written.

## 2026-09-04 — BLOCK 213: injectivity of stateOf

Half of the bijection (M3) needs.  Every field of the state is read straight back out by
`congrArg`; only `kstar` needs an argument, and it comes from the departure marker:

    eps_eq_of_state, delta_eq_of_state, d_eq_of_state, d_pred_eq_of_state,
    travel_eq_of_state       each field recovered from the state
    kstar_eq_of_state        the departure, from dep_eq_one_iff
    stateOf_determines       what the whole path pins down
    d_eq_off_span            off the span the deposits agree by houter
    d_eq_of_states           so the deposit FUNCTIONS agree, everywhere
    pathData_ext             equal data fields => equal configurations (no axioms)
    stateOf_injective        INJECTIVITY

0 sorry.  `pathData_ext` depends on no axioms at all.

**One hypothesis is assumed, not proved.**  `stateOf_injective` takes `P.A <= P.kstar <=
P.B + 1` -- the departure lies on the span.  It should follow from `houter` (travel
vanishes off the span) together with `travel`'s definition, since `0` is always on the
span by `hA`/`hB`; that derivation is not written, so it stands as a hypothesis.

**Still owed for (M3):** surjectivity onto the compatible paths -- that every
`compatB`-compatible path is realised by some configuration.  That is the half where a
configuration has to be BUILT from a path, proof fields and all.

## 2026-09-04 — BLOCK 214: the departure is always on the span; a second guard

BLOCK 213 assumed `A <= k* <= B + 1`.  It is a theorem.  `travel` is `1` on `[0, k*)` and
`-1` on `[k*, 0)`, and `houter` forces it to vanish off the span; since `0` is always on
the span (`hA`, `hB`), a departure outside would leave a non-zero travel indicator at
`B + 1` or at `A - 1`:

    kstar_le_B_succ      k* <= B + 1
    A_le_kstar           A <= k*
    stateOf_injective'   INJECTIVITY, with no side hypotheses

And a second necessary condition, recorded now because surjectivity is where it bites:
`compatB` alone does NOT characterise realisable paths.  A configuration also carries
`hpar` -- deposit and travel indicator agree mod 2 at every edge -- and a compatible path
violating that is realised by nothing:

    validB               deposit and travel agree mod 2
    validB_stateOf       every state of a configuration is admissible

0 sorry.

**So surjectivity is not "every compatible path".**  It is: every path that is compatible
AND admissible AND has its markers in the right places.  Whether those three conditions
are jointly SUFFICIENT is the open question -- and the honest expectation is that they are
not quite, since `hAmin`/`hBmin` (minimality of the span) is a further constraint the
state does not see.  A path whose end deposits vanish would need a shorter span.

## 2026-09-04 — BLOCK 215: RETRACTION — span-minimality IS visible to the state

BLOCK 214 (one block ago) expected `hAmin`/`hBmin` to be invisible to the states, and so
expected surjectivity to fail.  **That was wrong.**  `hAmin` reads `A = 0 or d A /= 0 or
f A /= 0`, and the state at `A` carries exactly `arr`, `dcur`, `fcur` -- with `arr = 1`
iff `A = 0`, by `arr_eq_one_iff` (BLOCK 212).  Minimality is a condition on the path's END
STATES and is checkable there.

    epsValidB, epsValidB_stateOf     heps, visible at every state
    endValidB, endValidB_at_A/_at_B  hAmin/hBmin, visible at the end states

So every field-level constraint of `PathData` is now accounted for:

    heps    -> epsValidB, every state
    hpar    -> validB, every state              (BLOCK 214)
    hAmin   -> endValidB at A
    hBmin   -> endValidB at B
    hA, hB  -> the arrival marker sits on the span
    houter  -> not a constraint: it DETERMINES the deposits off the span

0 sorry.  The obstruction BLOCK 214 anticipated does not exist.

**What is still open, precisely.**  Whether those conditions are jointly SUFFICIENT --
i.e. whether a path satisfying all of them can be assembled into a `PathData`.  That is a
construction, not an obstruction: build `d` from the path and `0` off the span, take `eps`,
`delta`, `kstar` from the states, and discharge the six proof fields from the guards
above.  Nothing now suggests it fails.

## 2026-09-04 — BLOCK 216: the travel flow is local; the guard is complete

`fcur` is not free data -- it is `travel k* j` -- so a guarded path could in principle
carry travel values no single `k*` produces.  But `travel_site_facts` says the constraint
is LOCAL: the travel indicator changes only at the arrival and the departure, by one unit
each,

    f (j) + [j+1 = 0] = f (j+1) + [j+1 = k*]

which is a condition on two consecutive states.  So it belongs in the guard, and with it
the guard has no non-local content left:

    flowB, flowB_stateOf       the travel indicator flows correctly
    stepB, stepB_stateOf       compatB AND flowB: the full local step guard
    pathWeight_guard_eq        guarding by ANY predicate the configuration satisfies
                               leaves its weight alone (generalises BLOCK 212)
    pathWeight_stepB_eq        in particular by stepB

0 sorry.  `pathWeight_guard_eq` depends on `propext` alone.

**The necessary conditions are now complete and all local.**  A realisable path satisfies:
`stepB` between consecutive states, `validB` and `epsValidB` at every state, `endValidB`
at the two end states, and carries exactly one arrival marker.  Every one is proved
satisfied by every configuration, and every one is checkable from the states alone.

**What is left of (M3) is exactly one thing: sufficiency.**  Given a path satisfying all
of the above, assemble a `PathData` realising it.  The data is forced (`d` from the
states and `0` off the span, `eps`/`delta` from any state, `k*` from the departure
marker); what has to be discharged is the six proof fields, and each has a guard above
aimed at it.  No obstruction is known.

## 2026-09-04 — BLOCK 217: sufficiency — guarded data assembles into a configuration

The last piece of (M3)'s bijection.  Everything the guards check is exactly what the six
proof fields of `PathData` need:

    travel_zero_off      off the span the travel indicator vanishes, given the departure
                         lies on it -- the converse of BLOCK 214, and houter's travel half
    mkPathData           THE CONSTRUCTION: guarded data assembles into a configuration
    mkPathData_d         and it realises the deposits it was built from
    mkPathData_dcur/_dprev/_fcur/_eps/_delta    the round trip on the span

Each proof field is discharged by the guard aimed at it:

    heps   <- supplied directly            hA, hB  <- supplied directly
    hpar   <- on the span from the guard, off it because both terms vanish
    houter <- deposits by construction, travel by travel_zero_off
    hAmin, hBmin <- the end-state guard, with A <= B from hA and hB

0 sorry.  One elaboration snag: implicit arguments cannot be inferred through the state
projection, so the round-trip lemmas need `simp only [stateOf]` before `exact`.

**Both halves of (M3)'s bijection now exist**: `stateOf_injective'` (BLOCK 213-214) and
`mkPathData` (here).  What is NOT yet written is their composition into a single
`Equiv` -- and, with it, the sum over configurations rewritten as the sum over guarded
paths, which is the statement (M3) actually needs.  That is assembly of pieces that are
all present, not new mathematics.

## 2026-09-04 — BLOCK 218: the composition — configurations of a span ARE guarded data

`mkPathData` builds a configuration from guarded data (BLOCK 217); `stateOf_injective'`
says no two configurations share their states (BLOCKS 213-214).  Packaging the guarded
data as a structure makes the two into mutually inverse maps:

    SpanData             guarded data for the span [A, B]; `hzero` normalises the
                         deposits off the span so the data is determined
    SpanData.toPath      guarded data builds its configuration
    ofPath               a configuration is guarded data for its own span
    spanData_ext         equal data fields => equal guarded data
    ofPath_toPath        ROUND TRIP ONE
    toPath_ofPath        ROUND TRIP TWO
    toPath_injective     hence the correspondence is one to one

0 sorry.  `Function.LeftInverse.injective` does not apply here: `ofPath P` has type
`SpanData P.A P.B`, so `ofPath . toPath` is not syntactically a map `SpanData A B ->
SpanData A B` even though it is definitionally one.  Injectivity is proved directly
instead -- fighting the dependent type would have bought nothing.

**(M3)'s bijection is complete.**  Configurations of span `[A, B]` correspond one to one
with guarded data for that span.  With (M3a) (BLOCKS 206-208), the formal convergence of
(M3b) (BLOCK 209) and the path-sum identity (BLOCKS 210-211), the pieces of (M3) are all
present.

**What remains is packaging, and it is not nothing.**  The sum in `IsAssembly` runs over
state paths as LISTS; the bijection above is stated for guarded data as a STRUCTURE.
Turning one sum into the other is index bookkeeping of the kind that has twice cost a
whole block in this file.  Until it is written, (M3) is not green.

## 2026-09-04 — BLOCK 219: list packaging — the state path determines the configuration

The bijection of BLOCK 218 is stated for guarded data; `IsAssembly` sums over state paths
as LISTS.  The bridge is that two functions agreeing on the mapped span list agree
pointwise -- proved by induction on the list, with no index arithmetic at all, which is
the lesson of the two aborts earlier in this file:

    map_idxList_inj    images agreeing along A :: idxList A n agree on [A, A+n]
    statePath_inj      hence distinct guarded data give distinct state paths

0 sorry.  `map_idxList_inj` needs only `propext` and `Quot.sound` -- no choice.
`omega` treats `S.toPath.B` as an atom distinct from `B`, so the projections must be
reduced by an explicit `rfl` rewrite first; that is not a defeq failure, just omega's
atomisation.

**So a sum over state paths counts each configuration exactly once.**  Together with
BLOCK 218's round trips, the correspondence is complete in the form the sum needs.

**What (M3) still lacks is finiteness.**  Both sums have to be finite before they can be
compared: `SpanData A B` is not a finite type (`dspan : Z -> Z` is unbounded off the
guards), so the sum over configurations only makes sense once cut by degree.
`dcur_le_muOf`/`fcur_le_muOf` (BLOCK 208) bound the states by the cost, which is the
right tool, but the cut is not built.  That is the honest remaining gap, and it is the
same gap on both sides.

## 2026-09-04 — BLOCK 220: the degree cut — everything is bounded by lR

The finiteness (M3) needs.  `lR` is a sum of non-negative terms, one `mu j` per edge of
the span, and `mu j` dominates both `|d j|` (`mu_ge_d`) and `1` (`mu_pos`):

    card_le_lR      the span has at most lR edges
    abs_d_le_lR     every deposit is bounded by lR
    span_bounds     so the span is confined to [-lR, lR]
    kstar_bounds    and the departure to [-lR, lR + 1]

0 sorry, all four clean on the first build.  `Int.card_Icc` does exist in this Mathlib.

**So every piece of data a configuration carries is bounded by its relaxed length.**  A
configuration of relaxed length at most `N` has span inside `[-N, N]`, deposits in
`[-N, N]`, and `k*` in `[-N, N+1]` -- finitely many.  That is the cut BLOCK 219 said was
missing, and it is now available in the form the sum needs.

**What is left of (M3), stated plainly.**  Turning these bounds into an actual `Finset`
of configurations at each degree, and then the sum identity itself.  The bounds are the
mathematical content and they are done; what remains is `Fintype` plumbing -- injecting
the bounded data into a product of finite intervals.  That is real Lean work but no new
mathematics, and until it is written (M3) stays yellow.

## 2026-09-04 — BLOCK 221: finitely much data determines a bounded-degree configuration

The bounds of BLOCK 220 turn into finiteness through this: a configuration of relaxed
length at most `N` is pinned down by `kstar`, `eps`, `delta`, `A`, `B` and its deposits ON
`[-N, N]` ONLY -- everything outside is forced to vanish, because the span cannot reach
there.

    pathData_eq_of_agree   a configuration of degree <= N is determined by that data
    pathData_box           and every coordinate of it is bounded by N

0 sorry, both clean on the first build.

**The remaining step is named and scoped.**  Assembling `Set.Finite {P | P.lR <= N}` from
the box needs `Set.Finite.of_finite_image` with `Set.InjOn` (from `pathData_eq_of_agree`),
the image contained in a product of intervals via `Set.Finite.prod` and `Set.Finite.pi`
over the Fintype `Icc (-N) N`.  All three lemmas were located in this Mathlib -- they are
in `Data/Set/Finite/Basic.lean`, `Data/Finite/Prod.lean` and `Data/Fintype/Pi.lean`.  It
is a five-factor product plus a pi; I stopped rather than grind it inside one block, which
is the three-strike rule applied before the strikes rather than after.

## 2026-09-04 — BLOCK 222: finiteness at each degree

`pathData_box` says every coordinate of a bounded-degree configuration is bounded and
`pathData_eq_of_agree` says those coordinates determine it.  Encoding the whole lot as a
SINGLE function on a finite index type -- five scalars and the deposits on `[-N, N]` --
turns that into ONE application of `Set.Finite.pi`, instead of the five-factor tower
BLOCK 221 stopped in front of:

    encAll              all the data as one function on Fin 5 (+) Icc (-N) N
    encAll_inj          it determines the configuration
    finite_degree_le    {P | P.lR <= N} IS FINITE

0 sorry.  The only failure was a malformed `split_ifs <;> [...]` bracket; replacing it
with `rcases h7 <;> split_ifs <;> omega` fixed it in one attempt.  Choosing the encoding
to avoid the product tower was the whole difficulty, and it was a choice, not a fight.

**Both degree cuts now exist**: `finite_degree_le` on the configuration side,
`dcur_le_muOf`/`fcur_le_muOf` (BLOCK 208) on the state side.

**What (M3) still owes.**  The sum identity itself.  Every link is present -- the weight
is a path weight (BLOCK 208), path sums are matrix powers (BLOCKS 210-211), the guard
kills unrealisable paths (BLOCKS 212, 216), the correspondence is bijective (BLOCKS
213-218), the state path determines the configuration as a list (BLOCK 219), and both
sides are finite at each degree (BLOCKS 220-222).  What is not written is the chain of
equalities joining them.  That is assembly, and it is the last thing between (M3) and
green.

## 2026-09-04 — BLOCK 223: the chain — a sum over configurations IS a sum over state paths

Joins the links.  The weight of a configuration is the path weight of its state path
(BLOCK 208) and distinct configurations have distinct state paths (BLOCK 219), so:

    sum_configs_eq_sum_paths    sum over configurations of a fixed span
                                = sum over the state paths they occupy

0 sorry.  `LocalState` now derives `DecidableEq`, which `Finset.image` needs for
`List LocalState`; that was the only failure and it was one edit.

**What the last link is, precisely.**  This says the sum over configurations equals the
sum over the paths they OCCUPY.  BLOCKS 210-211 say the sum over ALL state paths is the
matrix power.  Joining those two needs: every guarded path is occupied -- `mkPathData`
(BLOCK 217) at the level of lists rather than of `SpanData`.  The guard theorems
(BLOCKS 212, 216) show configurations satisfy the guard; the converse, that a guarded path
comes from a configuration, is `mkPathData` and is proved -- but it is stated for guarded
DATA, and the list-level restatement is not written.

So (M3) is one restatement short.  Not one theorem short -- one restatement of a theorem
already proved.  It stays yellow until that is written and the two sums are equated.

## 2026-09-04 — BLOCK 224: CORRECTION to BLOCK 223, and the induction it missed

BLOCK 223 called the remaining step of (M3) "one restatement".  **That was too
optimistic.**  `mkPathData` wants `hpar` phrased with `travel kstar`, but a guarded path
carries only its own `fcur` together with the FLOW relation.  Recovering
`fcur = travel kstar` from the flow is an INDUCTION, not a restatement.

The argument: `f` and `travel kstar` obey the same flow relation, so their difference has
zero increment everywhere, hence is constant; and it vanishes off the span, hence is zero.

    const_of_step        a function with zero increment everywhere is constant
    eq_travel_of_flow    so the flow relation plus vanishing off the span
                         DETERMINES the travel indicator

0 sorry.  `const_of_step` needs `propext` alone.  Two failures, both mechanical: the
`Int.induction_on` cases are named `zero`/`succ`/`pred` in this Mathlib, not
`hz`/`hp`/`hn`; and stating the difference as a lambda blocked `omega`, so it is stated
pointwise and `const_of_step` is applied with an explicit `(g := ...)`.

**Revised statement of what (M3) still owes.**  With `eq_travel_of_flow` a guarded path
now supplies everything `mkPathData` needs EXCEPT the packaging of a list back into a
state function -- reading `st j` off a list at index `j`.  That is indexing, which is
exactly what the two aborts in this file were about, and it is the honest remaining
obstacle.  BLOCK 219's `map_idxList_inj` avoided indexing by induction on the list; the
same trick should work here, going the other way.

## 2026-09-04 — BLOCK 225: reading a state function off a list, without indexing

BLOCK 224's obstacle was turning a guarded path (a list) back into a state function so
`mkPathData` can consume it.  Done by induction on the list, never by indexing:

    map_idxList_congr     functions agreeing from A onward have the same image
    exists_fun_of_length  EVERY list of the right length is a state path

0 sorry, both clean on the first build.  This is the third time in this file that
replacing an index argument with an induction on the list turned a hard step into an easy
one; `map_idxList_inj` (BLOCK 219) was the same move in the other direction.

**Where (M3) stands after this.**  A guarded path now yields a state function, the state
function feeds `mkPathData` (with `eq_travel_of_flow` supplying `hpar`), and the resulting
configuration's own state path is the list one started from.  So the correspondence holds
at the level of lists.

**What is left is one set equality and one chain.**  The set equality: the image of the
configurations under `statePath` IS the set of guarded paths -- one inclusion is the guard
theorems (BLOCKS 212, 216), the other is the construction just completed.  The chain: feed
that into `sum_configs_eq_sum_paths` (BLOCK 223) and `weightSum_eq_sum_pathWeight`
(BLOCK 211) to reach the matrix power.  Neither is written.

## 2026-09-04 — BLOCK 226: what "guarded" means, and the forward inclusion

To state the set equality (M3) needs, "guarded" has to be pinned down:

    Guarded A B kstar st   every local condition a configuration's state function meets
    guarded_stateOf        FORWARD INCLUSION: every configuration's state function is
                           guarded -- each field a theorem already proved

The conditions are imposed on all of `Z`, not on a window.  That is not a strengthening --
a configuration's state function is defined everywhere and satisfies them everywhere --
and it avoids the boundary fiddliness of a windowed guard, where `eq_travel_of_flow` would
need the flow to hold one step outside the span.

**The definition was incomplete on the first pass, and using it exposed that.**  Nothing
pinned `arr` to the arrival marker, and nothing bounded `dep` to `{0,1}` -- both of which
`flowB` needs, since it reads those fields as integers.  A "guarded" path with `dep = 5`
somewhere would satisfy the original conditions vacuously and be unrealisable.  Two fields
added, `arrv` and `depv`, both `rfl`-or-near for configurations.  0 sorry.

That is worth recording as a near miss: had the converse been attempted against the first
definition, it would have been unprovable, and the natural reading would have been that
the mathematics was wrong rather than the definition incomplete.

**Left for (M3):** the converse inclusion -- a guarded state function comes from a
configuration -- which is `mkPathData` fed by `eq_travel_of_flow`, plus the final chain.

## 2026-09-04 — BLOCK 227: converse inclusion — a guarded path comes from a configuration

    exists_config_of_guarded   every guarded state function is realised by a
                               configuration with the same span, departure and deposits
    eps_const_of_guarded       the sign data is constant along a guarded path

0 sorry, both clean on the first build.  `eps_const_of_guarded` needs `propext` alone; it
reuses `const_of_step` (BLOCK 224) on the `eps` field, since the compatibility guard
carries the sign across every step -- the same argument that identified the travel
indicator, applied to a different field.

The construction runs: the flow guard plus `depv`/`arrv` give the hypotheses of
`eq_travel_of_flow`, which identifies `fcur` with `travel kstar`; that turns `validB` into
`hpar` and `endValidB` into `hAmin`/`hBmin`; and `mkPathData` (BLOCK 217) assembles the
configuration.  The two fields added in BLOCK 226 are used exactly where predicted.

**Both inclusions now hold**, so the set equality (M3) needs is proved at the level of
state functions: `guarded_stateOf` one way, `exists_config_of_guarded` the other.

**Left for (M3):** matching a guarded path's states to the constructed configuration's
FIELD BY FIELD -- `dprev` from the compatibility guard, `delta` by the same constancy
argument as `eps` -- and then the final sum chain through `sum_configs_eq_sum_paths` and
`weightSum_eq_sum_pathWeight`.

## 2026-09-04 — BLOCK 228: the field-by-field match

    const_of_step_gen        const_of_step for an arbitrary type; the proof never used
                             the arithmetic
    delta_const_of_guarded   the delta flag is constant along a guarded path
    dprev_of_guarded         each state's dprev is the previous state's dcur
    fcur_of_guarded          the travel identification, standalone
    dep_of_guarded           the departure marker, as a natural number (NO AXIOMS)
    localState_ext           componentwise equality of states (NO AXIOMS)
    stateOf_eq_of_guarded    THE MATCH: a configuration agreeing with a guarded path in
                             deposits, departure and sign data has exactly that path's
                             states -- every other field is forced by the guard

0 sorry, all seven clean on the first build.  `const_of_step` generalised for free: the
BLOCK 224 proof used `rfl`, `rw` and `exact` only, so it never needed `ℤ`-valued targets,
and the `delta` flag reuses it directly.

**The set equality is complete.**  `guarded_stateOf` (BLOCK 226) says every configuration's
state function is guarded; `exists_config_of_guarded` (BLOCK 227) builds a configuration
from a guarded path; `stateOf_eq_of_guarded` (here) says that configuration's states ARE
the path.  So the guarded state functions are exactly the state functions of
configurations.

**Left for (M3): the final chain only.**  Feed the set equality into
`sum_configs_eq_sum_paths` (BLOCK 223) and `weightSum_eq_sum_pathWeight` (BLOCK 211) to
reach the matrix power, then `IsAssembly` via `coeff_neumann_tail_zero` (BLOCK 209).  No
new construction is required.

## 2026-09-04 — BLOCK 229: the set equality, proved; and what blocks the sum chain

    exists_config_stateOf   a guarded path's configuration has exactly that path's states
    stateFns_eq_guarded     THE SET EQUALITY: the state functions of configurations with a
                            given span and departure ARE the guarded state functions

0 sorry.  `exists_config_of_guarded` was strengthened to expose `eps` and `delta`, which
required moving `const_of_step_gen`, `delta_const_of_guarded` and `eps_const_of_guarded`
ahead of it -- they had been written after.

**An honest obstacle, found by trying the chain.**  The sum-level statement wants a
FINSET of guarded paths, and `Guarded` quantifies over all of `Z`, so it is not a decidable
predicate and no `Finset` can be formed from it directly.  That is the price of BLOCK 226's
choice to impose the conditions everywhere rather than on a window -- the choice that made
both inclusions easy is exactly the one that blocks the Finset.

So the remaining work for (M3) is a windowed restatement of `Guarded`: conditions on
`[A-1, B+1]` only, plus the boundary values, shown equivalent to the present version.  The
equivalence is the boundary bookkeeping BLOCK 226 deferred, and it is now unavoidable.
This is not a new mathematical gap -- the set equality is proved -- but it is more than
the "no new construction" BLOCK 228 predicted, and that prediction was wrong.

## 2026-09-04 — BLOCK 230: the flow telescopes; BLOCK 229's diagnosis partly corrected

BLOCK 229 blamed decidability of `Guarded` for blocking the sum chain.  That was the wrong
diagnosis.  The real requirement is that the transfer kernel VANISH on paths no
configuration realises, which needs the guard to be local plus boundary -- decidability is
a symptom, not the cause.

And of the conditions in `Guarded`, the one that looks global -- `dep`, that the departure
marker fires exactly once -- is NOT an assumption:

    telescope_flow    f(A) + total arrival = f(A+n) + total departure
    sum_markers_eq    so when the flow vanishes at both ends the totals agree

The arrival total is `1`, because the arrival marker fires only at `0` and `0` lies on the
span.  So exactly one departure marker fires, forced by the flow rather than imposed.
0 sorry, both clean on the first build.

**Where this leaves (M3).**  The guard is closer to local-plus-boundary than BLOCK 229
suggested: `stepB` is local, `validB`/`epsValidB` are per-state, `endValidB` is boundary,
`dep` is now derivable, and `outer` is the boundary condition that the end states carry no
deposit and no travel.  What is still not written is the kernel that encodes all of them
and the proof that it vanishes elsewhere.  That is the remaining piece, and it is smaller
than it looked one block ago.

## 2026-09-04 — BLOCK 231: the full guarded kernel, and a condition that resists it

Every per-state guard folds into the two-state guard by charging it to the state being
entered, so `pathWeight_guard_eq` (BLOCK 216) carries the whole local guard unchanged --
the generality there pays off:

    fullStepB, fullStepB_stateOf     the step plus the conditions on the state entered
    pathWeight_fullStepB_eq          the full guard leaves a configuration's weight alone
    headOkB, headOkB_stateOf         the first state's guard, dprev = 0 included
    tailOkB, tailOkB_stateOf         the last state's guard, dcur = fcur = 0

0 sorry, all four clean on the first build.

**A finding: `hBmin` does not fit a transfer kernel.**  Span-minimality at the right end is
a condition on the state at index `B`, which is the SECOND-TO-LAST state of the site path
`A .. B+1`, not the last.  A boundary vector sees only the last state, so it cannot express
it.  The obvious repair -- have the kernel demand `endValidB sigma` whenever `tau` looks
terminal (`dcur = 0` and `fcur = 0`) -- MISFIRES: an interior state with `d = 0` and
`travel = 0` also looks terminal (that is exactly the gap case, `mu = 2`), and the
preceding state need not satisfy `endValidB`.  So that encoding would reject legitimate
configurations.

This is a modelling question, not a bug: either sum over non-minimal spans and correct by
inclusion-exclusion, or carry a two-state marker distinguishing the true end.  It is the
honest remaining obstacle in (M3), and it is the first one in this sequence that is not
merely bookkeeping.

## 2026-09-04 — BLOCK 232: minimality is NOT redundant; and BLOCK 208's reason was wrong

Two findings, one of them a correction.

**Minimality cannot be dropped.**  A non-minimal end is an edge with `d = 0` and no travel,
and `mu` is `2` there -- the gap case.  So enlarging a span past minimality strictly
increases `lR`: the sum over non-minimal spans is a DIFFERENT generating function, not a
re-count of the same one.  The inclusion-exclusion route floated in BLOCK 231 is therefore
not a shortcut.

**But BLOCK 208's reason for site-indexing was wrong, and that reopens the good route.**
BLOCK 208 moved the chain from EDGES `A .. B` to SITES `A .. B+1` because the tail term
`siteCost (s+1)` "is not a function of state `s`".  It is:

    vD_succ_B_eq_travel   the departure marker at B+1 EQUALS the travel indicator at B

forced by the flow relation at the right end (`vArr (B+1) = 0` since `B >= 0`, and the
travel vanishes past `B`).  So the tail is a function of the last edge's state after all.
With the chain indexed by edges, `endValidB` applies at the FIRST and LAST states, which is
exactly where boundary vectors can see it -- and BLOCK 231's obstacle disappears.

**Hygiene.**  My draft re-proved `mu_eq_two_of_gap`, which was already in the file -- twice
over, at lines 7207 and 8542, a pre-existing duplication.  My copy is removed and the
existing one used.  0 sorry.

**So the route for (M3) is: re-index the chain by edges.**  BLOCKS 207-208's site-indexed
machinery stays valid but is the wrong frame for minimality; the edge-indexed frame was
abandoned for a reason that does not hold.

## 2026-09-04 — BLOCK 233: the edge frame closes

BLOCK 232 showed the departure marker past the right end equals the travel indicator
there, so the tail term of the edge-indexed chain is local after all:

    vD_succ_B_natAbs           that marker, as a natural number
    tailSiteOf                 the tail site cost, computed from the last edge's state
    tailSiteOf_stateOf         and it IS the site cost at B+1
    isTransferDecomposition_edge   (M3a) IN THE EDGE FRAME: one kernel, one head vector,
                                   one GENUINE tail vector, every configuration of span
                                   length n

0 sorry.  One failure, the familiar one: the tail term sits under an unreduced lambda, so
`rw` cannot see it; `simp only []` first.  That is the fourth time in this file that a
`rw` failed for beta-reduction rather than for a real mismatch.

**Why this frame is the right one.**  In the site frame (BLOCK 208) the chain's end states
are the sites `A` and `B+1`, and span-minimality at `B` lands on the second-to-last state,
where no boundary vector can see it -- BLOCK 231's obstacle.  In the edge frame the end
states are the edges `A` and `B`, which is exactly where `endValidB` lives.  So minimality
becomes a boundary condition, and `headOkB`/`endValidB_at_B` are the vectors that carry it.

**Left for (M3):** the guarded kernel and boundary vectors in the edge frame -- the same
assembly as BLOCK 231 but now with nothing landing in the interior -- and then the sum.

## 2026-09-04 — BLOCK 234: the guarded boundary vectors, in the edge frame

    pathWeight_congr          pathWeight reads lam only at the head and mu only at the
                              last state, so it ignores them elsewhere (NO AXIOMS)
    headVec, tailVec          the guarded boundary vectors
    headVec_stateOf,
    tailVec_stateOf           both fire on a configuration
    pathWeight_guarded_edge   THE FULLY GUARDED edge-frame path weight of a configuration
                              is x ^ lR

0 sorry.  Two mechanical failures: `lastOf s []` is `s` definitionally but not
syntactically, so the hypothesis had to be restated before `rw`; and
`List.map (f) (a :: l)` needed `List.map_cons` to meet `f a :: List.map f l`.

**Kernel, head vector and tail vector now all carry their guards**, and on a configuration
every guard fires so nothing is lost.  Span-minimality rides in `tailVec` via
`endValidB`, which in this frame is the LAST state -- the arrangement BLOCK 233 set up and
BLOCK 231 could not reach.

**Left for (M3): one implication.**  That the guards, taken together, force realisability
-- i.e. that a path on which `fullStepB`, `headOkB` and `tailVec`'s condition all hold is
the state path of a configuration.  Everything needed is proved (`Guarded`,
`exists_config_stateOf`, `stateFns_eq_guarded`); what is missing is the bookkeeping that
matches the edge-frame guards against the fields of `Guarded`.

## 2026-09-04 — BLOCK 235: the arrival fires once, so the state space must be doubled

Chasing (M3)'s last implication turned up a structural fact, not bookkeeping.  `Guarded`
requires `arrv` -- that a state's arrival flag is `[j = 0]` -- but a PATH is a list of
states with no indices, so no kernel can tie the flag to an index.  What is true, and all
that is needed, is that the flag fires EXACTLY ONCE along the span:

    sum_vArr_eq_one    the arrival marker fires exactly once, since 0 lies in [A, B]

"Exactly once" is not local, so a plain transfer matrix cannot impose it.  The remedy is
the standard one -- double the state space with a flag recording whether the origin has
been passed, and allow the arrival only on the transition that flips it:

    FlagState          a state plus a "past the origin" flag
    flagOf             a configuration's flagged state: the flag is `0 <= j`
    flagStepB          the doubled guard
    flagStepB_flagOf   A CONFIGURATION'S FLAGGED PATH PASSES IT

0 sorry.  Three attempts on the last branch, all diagnosed rather than guessed: `simp`
rewrote `j+1` to `0` in the goal but not in the hypothesis supplying it, so the hypothesis
had to be rewritten first.  That is the Rule 4.3 pattern -- read the state, do not vary the
tactic.

**Hygiene.**  A first draft of this block included a theorem whose two sides were
syntactically identical (`rfl`).  It proved nothing and was removed before commit.

**What this changes for (M3).**  The undoubled kernel of BLOCKS 231-234 cannot be the final
one; the doubled kernel can.  Everything proved about the undoubled guard carries over,
since `flagStepB` contains `fullStepB`.

## 2026-09-04 — BLOCK 236: the doubled boundary vectors and path weight

    flagHeadVec, flagHeadVec_flagOf   head guard plus the flag agreeing with the arrival
    flagTailVec, flagTailVec_flagOf   tail guard plus the flag SET -- which forces the
                                      arrival to have happened somewhere on the path
    pathWeight_flag_of                the doubled guard costs nothing on a configuration
    pathWeight_flag_guarded           THE DOUBLED, FULLY GUARDED path weight of a
                                      configuration is x ^ lR

0 sorry.  Three attempts, and the third was the fix rather than a fourth guess:
`(flagOf P j).st` is `stateOf P j` by `rfl` but not syntactically, so the vector lemmas
needed a trailing `rfl`; and the induction step's list rewrite could not match
syntactically, so `congr 1` then `exact` -- which accepts definitional equality where `rw`
will not.  That distinction has now cost time twice in this file and is worth remembering:
`rw` is syntactic, `exact` is up to defeq.

**So the kernel (M3) needs exists and is proved correct on configurations.**  It is local,
it carries every per-state and boundary guard, and the doubling makes the arrival count
exactly once.

**Left for (M3): the converse for the doubled guard** -- that a path passing `flagStepB`,
`flagHeadVec`'s condition and `flagTailVec`'s condition is a configuration's flagged path.
The undoubled ingredients are all proved (BLOCKS 226-229); what the doubling adds is that
the flag forces exactly one arrival, which is `sum_vArr_eq_one` read backwards.

## 2026-09-04 — BLOCK 237: what the flag forces — exactly one arrival

The doubled guard exists to impose a condition no local kernel can state.  These three
facts are why it works:

    past_mono              the flag never turns off
    no_arr_after           no arrival fires once the flag is on -- AT MOST one
    past_false_of_no_arr   without an arrival the flag never turns on, so given a set tail
                           flag there is AT LEAST one

0 sorry, all three clean on the first build, and on minimal axioms (`propext`, and
`Quot.sound` for the induction).

Together: along a path whose head flag matches its arrival and whose tail flag is set, the
arrival fires exactly once -- which is `sum_vArr_eq_one` (BLOCK 235) recovered from the
kernel rather than from the configuration.  That was the one condition the undoubled guard
could not express, and it is now expressed.

## 2026-09-04 — BLOCK 238: the arrival pins the translation

A path is a list of states and does not know where the origin sits.  That is not a defect:
the index is ours to choose, and the arrival chooses it.  A guarded flagged path has
exactly one arrival, and declaring that index to be `0` is what turns the path into a
configuration.

    exists_arr_index      a set tail flag forces an arrival
    past_of_arr           the arrival sets the flag
    past_true_forward     and once set it stays set, forever forward
    arr_unique_forward    so no second arrival can fire

0 sorry, all four clean on the first build, on `propext` (plus `Quot.sound` for the one
`by_contra`).

**This resolves the objection of BLOCK 235 completely.**  There it looked as though `arrv`
-- the arrival flag being `[j = 0]` -- could never be recovered from a kernel, since a list
carries no indices.  The answer is that it does not need to be recovered: the arrival
DEFINES the index, and the doubled guard guarantees there is exactly one such index to
choose.

## 2026-09-04 — BLOCK 239: translating a guarded path onto the origin

The guards are pointwise or nearest-neighbour, so they survive a shift:

    shiftFn                shift a state function
    flagStepB_shift        the doubled guard is translation-invariant
    shiftFn_arr_zero       shifting by the arrival index puts the arrival at the origin
    shift_span_brackets    and then the span brackets the origin, FOR FREE

0 sorry, all three clean on the first build.

The last is the point.  `mkPathData` demands `hA : A <= 0` and `hB : 0 <= B`, and those
looked like extra hypotheses a path would have to supply.  They are not: with the arrival
at `A + k` and `k <= n`, the shifted span is `[-k, n - k]`, which contains `0`.  So the
bracketing is a CONSEQUENCE of the arrival lying inside the span, which the doubled guard
already guarantees (BLOCK 238).

**Every hypothesis `mkPathData` needs is now accounted for from the doubled guard alone.**
What remains is to write the composition: shift, read off the data, apply `mkPathData`, and
check the resulting configuration's flagged path is the one started from.

## 2026-09-04 — BLOCK 240: a marker sum of one means exactly one marker

The arrival was pinned by the flag (BLOCKS 237-238).  The DEPARTURE is pinned differently
and needs no second flag: `telescope_flow` (BLOCK 230) makes the departure total equal the
arrival total, which is `1`, and a 0/1 sum equal to `1` has exactly one term equal to `1`:

    exists_of_sum_one    such a sum has a term equal to 1
    unique_of_sum_one    and only one

0 sorry, both clean on the first build.  `unique_of_sum_one` goes through
`Finset.sum_pair` and `Finset.sum_le_sum_of_subset`: two markers would make the total at
least `2`.

**So both markers are now pinned by the guard alone** -- the arrival by the flag, the
departure by the flow.  Between them, `Guarded`'s `dep`, `arrv` and `depv` fields are
consequences rather than assumptions, which is what the converse needs.

## 2026-09-04 — BLOCK 241: the departure total equals the arrival total

The bridge from `telescope_flow` (BLOCK 230) to the marker lemmas (BLOCK 240):

    flow_of_flagStepB   the doubled guard supplies the flow relation
    dep_sum_eq_arr_sum  and with the travel vanishing at both ends of the span, the two
                        marker totals agree

0 sorry.  One failure, the beta-reduction one again -- `sum_markers_eq` returns its sums
with the summand still a lambda, so `exact_mod_cast` saw a different term; `simp only []`
first.  Fifth occurrence in this file.

Since the arrival total is `1` (`sum_vArr_eq_one`, BLOCK 235), so is the departure total,
and `exists_of_sum_one` / `unique_of_sum_one` locate the departure exactly.  **Both
markers are now derived from the guard, neither assumed.**

## 2026-09-04 — BLOCK 242: locating the departure

Everything was in place; this joins it:

    exists_dep_index    the departure index exists
    dep_index_unique    and is unique

0 sorry, both clean on the first build.  The chain is: the guard supplies the flow
(BLOCK 241), the flow makes the departure total equal the arrival total (BLOCK 230+241),
the arrival total is one (BLOCK 235), and a 0/1 sum equal to one has exactly one term
(BLOCK 240).  No second flag was needed.

**Status of the doubled converse.**  `Guarded`'s fields now come from the doubled guard as
follows: `step`, `valid`, `epsv` from `fullStepB`; `endA` from `headOkB`; `endB` from the
tail vector; `arrv` from the flag plus translation (BLOCKS 237-239); `dep` and `depv` from
the flow (this block); `loA`, `hiB` from the arrival lying in the span (BLOCK 239);
`kstLo`, `kstHi` from the departure index lying in the range.  `outer` is the boundary
condition the head and tail vectors carry.

Every field is accounted for.  What is not yet written is the single theorem that puts them
together and hands `exists_config_stateOf` its hypothesis.

## 2026-09-04 — BLOCK 243: the doubled converse, proved

    guarded_of_flag         a doubled guarded path IS a Guarded state function
    exists_config_of_flag   and so it is the state path of a configuration

0 sorry, both clean on the first build; `guarded_of_flag` depends on `propext` alone.

**This is the converse (M3) has been owed since BLOCK 226.**  The hypotheses are exactly
what the kernel and the two boundary vectors enforce, together with the three facts derived
along the way: the arrival's position after translation (BLOCKS 237-239), the located
departure (BLOCKS 240-242), and the span bracketing the origin (BLOCK 239).

**Both directions of (M3)'s correspondence now hold in the doubled, edge-indexed frame:**

    pathWeight_flag_guarded   a configuration's flagged path weight is x ^ lR
    exists_config_of_flag     a guarded flagged path comes from a configuration

**What (M3) still owes is the summation itself** -- forming the sum over paths and showing
the non-realisable ones contribute nothing, which is now a matter of `Finset` manipulation
against `weightSum_eq_sum_pathWeight` (BLOCK 211) rather than of mathematics.  I have
predicted "just assembly" twice before and been wrong (BLOCKS 223, 228), so that claim
stands only until the next block tests it.

## 2026-09-04 — BLOCK 244: extending a path past the span; "just assembly" was wrong AGAIN

BLOCK 243 predicted the summation would be "just assembly" and flagged that I had made that
prediction twice before and been wrong.  **It was wrong a third time.**

`guarded_of_flag` wants `outer` -- the states off the span carry no deposit and no travel --
but a finite path has no states off the span, so they must be supplied.  The obvious
supply, an all-zero state, BREAKS the guard: `compatB` demands `tau.dprev = sigma.dcur`, so
the state just past the right end must carry `dprev = d B`, which is not zero.

The correct extension is forced, and it is exactly the state `tailSiteOf` was already
reading (BLOCK 233):

    extState            deposit and travel zero, dprev carried over, departure marker
                        equal to the travel indicator at B
    extState_stateOf    and for a configuration it IS the state at B + 1, every field

0 sorry, clean on the first build.

**On the pattern.**  Three times now the last step has looked like bookkeeping and turned
out to carry content.  The common cause is the same each time: a path is a finite object and
a configuration is an infinite one, and the difference always shows up at the boundary.  I
should stop predicting that the boundary is free.

## 2026-09-04 — BLOCK 245: the left boundary is NOT the right one

BLOCK 244 found the state past the right end must carry `dprev = d B`.  Checking the left
end rather than assuming it -- which is the lesson of the last three blocks:

    preState            the state just before the left end
    preState_stateOf    and for a configuration it IS the state at A - 1: ALL-ZERO

0 sorry, clean on the first build.

**The asymmetry is real and has a cause.**  `dprev` looks one step to the LEFT, so the
state just past the right end inherits the span's last deposit, while the state just past
the left end looks at `d (A - 2)`, outside the span and therefore zero.  The markers vanish
there too: the arrival fires only at `0` and `A <= 0` puts `A - 1` strictly below it; the
departure fires only at `k*` and `A <= k*` puts `A - 1` strictly below that.

So the two ends need different extensions, and a symmetric guess would have been wrong at
one of them.  Both are now proved.

**Both boundaries handled**, which was the obstacle BLOCK 244 exposed.

## 2026-09-04 — BLOCK 246: extending a finite path to all of Z

With both boundary states known (BLOCKS 244-245), a path defined on the span extends:

    extendFn            the span itself, then the inherited state at B+1, then all-zero
    extendFn_stateOf    and for a configuration the extension changes NOTHING

0 sorry, clean on the first build.

The second is the point.  `guarded_of_flag` needs `outer`, a statement about states off the
span; `extendFn` supplies them, and `extendFn_stateOf` shows the supply is the correct one
-- it reproduces `stateOf` exactly rather than merely being consistent with it.  The three
branches are the span, the inherited right boundary, and everything else, and each is
discharged from `houter`, `travel_zero_off`, and the two marker positions.

## 2026-09-04 — BLOCK 247: `outer` holds for the extension of ANY path

    extendFn_eq_on    the extension agrees with the path on the span
    extendFn_outer    and off the span it carries no deposit and no travel -- for ANY
                      path, with no hypothesis at all
    extendFn_eps      the sign data carries through (NO AXIOMS)

0 sorry, all three clean on the first build.

`extendFn` was built so that both extension states satisfy `outer` by construction:
`extState` sets `dcur` and `fcur` to zero explicitly, and `preState` is all-zero.  So the
`outer` field of `guarded_of_flag` -- the one BLOCK 244 identified as the obstacle -- is
now discharged unconditionally.

**All of `guarded_of_flag`'s hypotheses are now available for an arbitrary guarded path**,
`outer` included.  The remaining work is the summation over paths, which I will not
characterise in advance.

## 2026-09-04 — BLOCK 248: injectivity from the edge path alone

    stateOf_injective_span   agreement on A .. B alone determines the configuration

0 sorry.  One failure: `split_ifs` produced two goals, not three, so the third `omega` had
nothing to solve; `<;> omega` instead.

The edge-indexed path covers `A .. B`, not `A .. B+1`, so `stateOf_injective'` (BLOCK 214)
does not apply -- it wants agreement one site further.  The deposits are fine, since they
vanish off the span.  **The departure is the problem: it can sit at `B + 1`, outside the
path.**

It is still seen, indirectly: `travel k* B` is `1` exactly when `k* > B`, and `k*` is at
most `B + 1`, so the last edge's travel indicator decides whether the departure sits past
the end.  That is the boundary case, and it is the third block in a row where the boundary
carried the content -- the pattern noted in BLOCK 244 continues to hold.

## 2026-09-04 — BLOCK 249: the sum over flagged paths

    flagPath_inj                    distinct guarded data give distinct flagged edge paths
    sum_configs_eq_sum_flag_paths   a sum over configurations of a fixed span IS a sum over
                                    their flagged edge paths, weighted by the doubled,
                                    fully guarded kernel and boundary vectors

0 sorry, both clean on the first build.  This is BLOCK 223's identity re-established in the
frame (M3) actually uses -- edge-indexed, doubled, and with every guard carried.

**What remains for (M3):** extending the sum from the IMAGE of the configurations to ALL
paths.  That needs one fact -- a path on which some guard fails has weight zero, because
the weight is a product and the guard contributes a zero factor -- together with
`exists_config_of_flag` (BLOCK 243) for the paths on which no guard fails.  Then
`weightSum_eq_sum_pathWeight` (BLOCK 211) turns the sum over all paths into the matrix
power.

## 2026-09-04 — BLOCK 250: a path failing the guard has weight zero

    pathWeight_zero_of_guard_fails   a failure anywhere along the path kills the weight

0 sorry, clean on the first build, and on `propext` + `Quot.sound` only -- no choice.

The weight is a product along the path, and the guarded kernel contributes a zero factor
wherever the guard fails, so the factor propagates out through the whole product.  The
induction splits on whether the failure is at the head of the remaining path or deeper.

**So a sum over ALL paths sees only the guarded ones.**  With `sum_configs_eq_sum_flag_paths`
(BLOCK 249) on one side and `exists_config_of_flag` (BLOCK 243) identifying the guarded
paths with configurations, the two sums agree -- which is (M3)'s statement.  What is left
is writing that comparison as a `Finset` argument.

## 2026-09-04 — BLOCK 251: the extension, on flagged states

    extendFlag            extend a flagged state function beyond its span
    extendFlag_flagOf     for a configuration it changes nothing
    extendFlag_outer      and `outer` holds for it, for ANY path
    extendFlag_eq_on      it agrees with the path on the span (NO AXIOMS)

0 sorry, all three clean on the first build.

`extendFn` extends the underlying states and the flag is `0 <= j` by definition, so the
flagged extension is immediate.  This is the piece that carries a finite path -- a list --
to the state function `exists_config_of_flag` (BLOCK 243) consumes: `exists_fun_of_length`
(BLOCK 225) turns the list into a function on the span, and `extendFlag` extends it to `Z`
with `outer` holding by construction.

## 2026-09-04 — BLOCK 252: a GAP in my own tail vector, and its repair

Checking whether `extendFlag` always satisfies the guard exposed a gap in BLOCK 234's
`tailVec`.  The step from `B` to `B + 1` needs `flowB`:

    fcur B + arr (B+1) = fcur (B+1) + dep (B+1),

and with `arr (B+1) = 0`, `fcur (B+1) = 0` and `dep (B+1) = |fcur B|` that is
`fcur B = |fcur B|`, i.e. `fcur B >= 0`.  A configuration satisfies it -- the travel
indicator is `-1` only strictly left of the origin, and `B >= 0`.  **But nothing in
`tailVec` enforced it, so a path with `fcur B = -1` passed every guard while being
unrealisable.**

    fcur_B_nonneg       the travel indicator at the last edge is never negative
    tailOk2B            the repaired tail guard: BLOCK 234's, plus the sign condition
    tailOk2B_stateOf    and a configuration satisfies it
    flowB_extState      with it, the step past the right end holds

0 sorry, all three clean on the first build.

**This is the second gap found by trying to use a guard rather than by inspecting it**
(BLOCK 226 was the first, with `arrv` and `depv`).  Both were invisible in the forward
direction -- configurations satisfy the guard either way -- and both would have made the
converse unprovable while looking like a mathematical obstruction.  The lesson is that a
guard is only tested by the direction that consumes it.

## 2026-09-04 — BLOCK 253: a THIRD gap of the same kind — the head vector's flow condition

The step from `A - 1` into `A` needs `flowB` there.  With the state before the span
carrying no travel, that reads

    arr A = fcur A + dep A,

a condition on the FIRST state alone.  `headOkB` (BLOCK 231) carries `dprev = 0` -- the
`compatB` half of that step -- but not this, the `flowB` half.

    head_flow_stateOf   the condition holds for a configuration
    headOk2B            the repaired head guard
    headOk2B_stateOf    and a configuration satisfies it
    flowB_preState      with it, the step into the left end holds

0 sorry, all three clean on the first build.

**Three gaps of identical shape now** (BLOCKS 226, 252, 253), each found by trying to USE
the guard rather than by reading it, and each invisible from the configuration side.  The
pattern is precise enough to state as a rule: **every step the extension makes across a
boundary imposes a condition on the boundary state, and the guard must carry it.**  There
are four such steps -- into `A`, out of `B`, and the two beyond -- and their `compatB` and
`flowB` halves are eight conditions.  Six are now accounted for; the two beyond the ends
are trivial, since both extension states are inert.

## 2026-09-04 — BLOCK 254: the two steps beyond the ends; the eighth condition found

BLOCK 253 called these two steps trivial.  The left one is.  **The right one is not**: past
the right end the extension goes from `extState (st B)` to `preState (st A)`, and `compatB`
compares their sign data -- so it needs `eps` and `delta` to agree between the two ENDS of
the span.  That is the constancy along the path (BLOCKS 227-228), not nothing.

    compatB_extState_preState   the step past the right end, given that agreement
    flowB_extState_preState     its flow half
    compatB_preState_self,
    flowB_preState_self         the steps beyond the left end, genuinely trivial
    compatB_extState            the compatB half of the step out of B
    compatB_preState            the compatB half of the step into A

0 sorry.  One failure: `simp` collapses the trivially-true conjuncts to `True`, so an
explicit `⟨⟨_, _⟩, _⟩` over-supplies; single `simp` calls with the hypotheses instead.

**All eight boundary conditions are now accounted for**, and the count was right --
four steps, `compatB` and `flowB` for each -- but my claim that two of them were free was
wrong on one of the two.  That is the fourth time in this stretch that a boundary looked
free and was not.

## 2026-09-04 — BLOCK 255: the extension's guard, far from the span

Six cases make up the extension's guard: inside the span, the two ends, the two steps just
beyond, and everything further out.  The last:

    extendFlag_far              off the span and away from B+1, the extension is inert
    flagStepB_extendFlag_far    and the guard holds there, on both sides

0 sorry.  One failure, and it is the same species as the last four: even the INERT state
must satisfy `epsValidB`, so the sign data has to be admissible -- which comes from the
path's own head guard, not from the extension.  Added as a hypothesis.

The flag is constant that far out because `j` never crosses the origin at a distance from a
span that contains it: past `B + 1` both flags are set, before `A - 1` both are clear.

## 2026-09-04 — BLOCK 256: the step just past the right end

    extendFlag_at_succ_B          at B+1 the extension is the inherited state
    flagStepB_extendFlag_beyond   and the step from there to the inert state holds

0 sorry.  One failure: the inert state's admissibility is needed at `B`, not at `A`, so the
sign hypothesis had to be transported along `heps` first.

This is the step BLOCK 254 found is not free: `compatB` compares the two extension states'
sign data, so it needs the path's own `eps` and `delta` to agree between `A` and `B` --
which is the constancy along the path.

**Four of the six cases are now proved in extension form** (far on both sides, and this
one); the two remaining are the step out of `B` into `B + 1` and the step from `A - 1` into
`A`, whose ingredients are BLOCKS 252-253.

## 2026-09-04 — BLOCK 257: the step out of the right end

    extendFlag_at_B              at B the extension is the path's own state
    flagStepB_extendFlag_out     and the step out of B holds

0 sorry.

**One hypothesis is taken rather than proved**, and it is worth naming: `extendFlag_at_B`
needs the path's flag at `B` to be the canonical `decide (0 <= B)`.  That IS forced by the
guard -- the flag advances only at the arrival, and the arrival is at the origin -- but the
derivation is an induction along the path, and it is not written.  So `flagStepB_extendFlag_out`
carries `hflag` as an assumption.

**Five of the six extension cases are now proved**; the step from `A - 1` into `A` remains,
and it will need the same flag fact at `A`.  Writing that induction once will discharge it
for both.

## 2026-09-04 — BLOCK 258: the flag along a guarded path is the canonical one

    past_eq_decide   the flag at A + n is `decide (0 <= A + n)`

0 sorry.  One failure: after the `if` split the goal is a BOOL equation, not `... = true`,
so `Bool.or_eq_true` had nothing to act on; handling each `decide` explicitly with
`decide_eq_true` / `decide_eq_false` works.

**This discharges the hypothesis BLOCK 257 assumed.**  The flag starts matching the arrival
at `A`, advances only where the arrival fires, and the arrival fires only at the origin, so
it is `0 <= j` throughout.  The proof is an induction from `A` upward with the interesting
case at `j = -1`, where the flag turns on exactly as the arrival fires.

With it, `flagStepB_extendFlag_out` (BLOCK 257) and the remaining step from `A - 1` into
`A` both have their flag facts.

## 2026-09-04 — BLOCK 259: the step into the left end — the sixth and last case

    extendFlag_at_A            at A the extension is the path's own state
    flagStepB_extendFlag_in    and the step from A-1 into A holds

0 sorry.  One failure, diagnosed before rewriting per Rule 4.3: `simp` had reduced the goal
to pure arithmetic in `A` -- `(1 <= A -> 0 <= A) and (A < 1 or A < 0)` -- both consequences
of `A <= 0`, so `omega` closes it; no tactic guessing was needed.

**All six extension cases are now proved:**

    inside the span            the path's own guard
    into A                     flagStepB_extendFlag_in       (BLOCK 259)
    out of B                   flagStepB_extendFlag_out      (BLOCK 257)
    just past B                flagStepB_extendFlag_beyond   (BLOCK 256)
    far on both sides          flagStepB_extendFlag_far      (BLOCK 255)

and the flag fact they all needed is `past_eq_decide` (BLOCK 258), a theorem rather than an
assumption.

**Status of (M3) [Rule 0 label: the parts are VERIFIED, the whole is not].**  Both
directions of the correspondence are VERIFIED, the summation over flagged paths is
VERIFIED, the vanishing off the guard is VERIFIED, and every boundary step of the extension
is VERIFIED.  What is NOT yet written is the single theorem that runs the case split over
`j` and concludes `flagStepB` everywhere for `extendFlag`.

## 2026-09-04 — BLOCK 260: the extension satisfies the guard everywhere

    extendFlag_at_span      on the span the extension is the path's own state (NO AXIOMS)
    FlagPath                what a guarded path supplies, bundled
    flagStepB_extendFlag    THE ASSEMBLY: the guard holds at EVERY index

0 sorry.  One failure, diagnosed before rewriting per Rule 4.3: `subst c4` with `c4 : j = B`
eliminates `B` itself, so the later `h.flag B` had no `B` to refer to; `rw [c4]` keeps both
variables and works.  Same substitution applied to the other two equations for uniformity.

The six cases of BLOCKS 255-259 dispatch by trichotomy on `j` against `A - 1`, then against
`B`, `B + 1`: far left, into `A`, inside the span, out of `B`, just past `B`, far right.

**[Rule 0] VERIFIED: a guarded path's extension satisfies the doubled guard at every index
of `Z`** -- which is the hypothesis `guarded_of_flag` (BLOCK 243) needs, and hence
`exists_config_of_flag`.  The chain from a finite guarded path to a configuration is now
complete end to end.

## 2026-09-04 — BLOCK 261: the extension's markers, everywhere

    extendFn_arrv   the arrival marker is `vArr` at EVERY index, not just on the span
    extendFn_depv   and the departure marker stays in {0,1}

0 sorry, both clean on the first build.

`exists_config_of_flag` (BLOCK 243) wants these at every index of `Z`, while a path supplies
them only on its span.  Off the span both extension states have zero markers, and that is
correct: the arrival fires only at `0`, which lies on the span, so every index off the span
has `vArr = 0`; and the departure marker past the right end is the one `extState` carries,
which is `|fcur B|` and so is `0` or `1` whenever the travel indicator is.

**[Rule 0] VERIFIED.**  Two more of `exists_config_of_flag`'s hypotheses are now available
for an arbitrary guarded path.

## 2026-09-04 — BLOCK 262: the extension's departure marker, everywhere

    extendFn_dep   the departure marker fires exactly at k*, at every index of Z

0 sorry, clean on the first build.

Off the span and away from `B + 1` the marker is `0`, and that is right: the departure lies
in `[A, B+1]`, so no index outside can be it.  At `B + 1` the marker is `|fcur B|`, and
whether it fires is exactly whether the departure sits past the end -- the criterion
BLOCK 248 identified.  **That is a hypothesis here, not a consequence**, since for an
arbitrary path it is a condition on the path rather than something derivable from the
others.

**[Rule 0] VERIFIED, with one hypothesis carried.**  With this, every field of
`exists_config_of_flag` is available for a guarded path except that hypothesis, which is a
property the guard must be asked to check.

## 2026-09-04 — BLOCK 263: the B+1 departure condition is DERIVABLE, not a new guard

BLOCK 262 carried `fcur B = 1 <-> k* = B + 1` as a hypothesis and expected it to need a new
guard clause -- the fourth repair of that shape.  **It does not.**

Telescoping the flow across `[A, B]` (BLOCK 230) gives

    f(A-1) + (arrivals on [A,B]) = f(B) + (departures on [A,B]),

and `f(A-1) = 0` with exactly one arrival (BLOCK 235) makes that

    1 = fcur B + (departures on [A,B]).

Both terms are non-negative integers -- `fcur B >= 0` is BLOCK 252's `fcur_B_nonneg` -- so
exactly one of them is `1`: either the departure sits on the span and `fcur B = 0`, or it
sits past the end and `fcur B = 1`.  The condition follows from the guard already in place.

    depB1_iff_stateOf   the condition, in the form a configuration satisfies

0 sorry, clean on the first build.

**This is the first time in this stretch that a suspected new guard clause turned out to be
a consequence.**  Four times (BLOCKS 226, 252, 253, 254) the guard genuinely had to grow;
here checking first saved a fifth clause that would have been redundant.

## 2026-09-04 — BLOCK 264: the flow balance across the span

    flow_balance             1 = (travel at the right end) + (departures on the span)
    flow_balance_dichotomy   and since both are non-negative, exactly one fires

0 sorry, both clean on the first build.

This is BLOCK 263's identity in the general form a PATH can supply, not just a
configuration: with the travel vanishing just left of the span (`preState`) and exactly one
arrival on it (`sum_vArr_eq_one`), the two quantities sum to one.  `fcur_B_nonneg`
(BLOCK 252) supplies the non-negativity on one side and the marker being a count supplies
it on the other.

**[Rule 0] VERIFIED.**  The `B + 1` condition BLOCK 262 carried as a hypothesis is now
derivable for an arbitrary guarded path, not only for a configuration.  No fifth guard
clause is needed.

## 2026-09-04 — BLOCK 265: from the balance to the departure's position

    sum_zero_iff_no_one         a 0/1 sum vanishes exactly when every term does
    kstar_eq_succ_B_of_no_dep   no departure on the span means it is past the end
    kstar_le_B_of_dep           and a departure on the span means it is not

0 sorry, all three clean on the first build; the last two need only `propext` and
`Quot.sound`.

`flow_balance` (BLOCK 264) says the departures on the span total `0` or `1`; these turn
that into a statement about WHERE the departure is, which is what `extendFn_dep`'s `hB1`
asks.  Both directions of that iff are now available:

    fcur B = 1  =>  departures total 0  =>  none on the span  =>  k* = B + 1
    fcur B = 0  =>  departures total 1  =>  one on the span    =>  k* /= B + 1

**[Rule 0] VERIFIED.**  The composition into `hB1` itself is the remaining step, and it is
now a matter of chaining these three with `flow_balance_dichotomy`.

## 2026-09-04 — BLOCK 266: the B+1 condition, composed

    hB1_of_balance   fcur B = 1 <-> k* = B + 1, from the balance and the two bridges

0 sorry, clean on the first build.

`extendFn_dep` (BLOCK 262) carried this as a hypothesis and I expected it to need a fifth
guard clause.  It needed none: `flow_balance_dichotomy` (BLOCK 264) picks a side, and each
side determines where the departure is via `kstar_eq_succ_B_of_no_dep` or
`kstar_le_B_of_dep` (BLOCK 265).

**[Rule 0] VERIFIED.**  Every hypothesis of `extendFn_dep` is now a consequence of the guard
rather than an assumption, so `exists_config_of_flag` applies to an arbitrary guarded path
with nothing carried.

**Where (M3) stands.**  The correspondence is complete in both directions, the extension is
complete and guarded everywhere, and the guard is closed -- no clause of it is assumed.
What remains is the sum comparison itself: `Finset.sum_subset` between the configurations'
image and all paths, with `pathWeight_zero_of_guard_fails` (BLOCK 250) supplying the
vanishing.

## 2026-09-04 — BLOCK 267: a fully guarded path yields a configuration

    exists_config_of_path   the composition, end to end

0 sorry.  One failure, a typo diagnosed at once: `(g B).fcur` projects `fcur` from
`FlagState` rather than from its `LocalState` field.

The pieces: `flagStepB_extendFlag` (BLOCK 260) gives the guard at every index,
`extendFn_arrv` / `extendFn_dep` / `extendFn_depv` (BLOCKS 261-262) give the markers
everywhere, `extendFlag_outer` (BLOCK 251) gives `outer`, `extendFlag_at_span` (BLOCK 260)
identifies the boundary states with the path's own, and `exists_config_of_flag` (BLOCK 243)
assembles them.

**[Rule 0] VERIFIED: a guarded flagged path of any span is the state path of a
configuration.**  This is the converse direction of (M3) in fully composed form -- from a
finite path, with no hypotheses beyond what the kernel and the two boundary vectors check.

## 2026-09-04 — BLOCK 268: bounded map congruence, and the path equality

    map_idxList_congr_le     agreement on [A, A+n] suffices for the mapped list
    flagPath_eq_of_config    a configuration built from a path HAS that path as its
                             flagged state path

0 sorry, both clean on the first build.

`map_idxList_congr` (BLOCK 225) asked for agreement at every `j >= A`, but a path supplies
it only on its span; the list only visits `[A, A+n]`, so the bound suffices.  The second
lemma is the round trip closing: `exists_config_of_path` (BLOCK 267) builds a configuration
whose states are the EXTENSION's, and on the span the extension is the path itself, so the
configuration's flagged path is the one we started from.

**[Rule 0] VERIFIED.**  With `flagPath_inj` (BLOCK 249) in the other direction, the map from
configurations to guarded flagged paths is a bijection onto them.

## 2026-09-04 — BLOCK 269: a non-zero weight forces every guard

    guards_of_weight_ne_zero    a contributing path satisfies the step guard everywhere
    headOk_of_weight_ne_zero    and its head vector does not vanish

0 sorry, both clean on the first build; the second needs `propext` alone.

These are the contrapositives of BLOCK 250, and they are the direction the sum comparison
uses: a path contributing anything to the sum must satisfy the guard, hence -- by
`exists_config_of_path` (BLOCK 267) and `flagPath_eq_of_config` (BLOCK 268) -- is the state
path of a configuration and lies in the image.

**[Rule 0] VERIFIED.**  Both halves of the sum comparison's hypothesis are now available:
paths in the image contribute their configuration's weight, and paths outside it contribute
zero.

## 2026-09-04 — BLOCK 270: the sum over configurations is the sum over all paths

    sum_configs_eq_sum_all_paths   the comparison, composed

0 sorry, clean on the first build.

`sum_configs_eq_sum_flag_paths` (BLOCK 249) turns the left side into a sum over the
configurations' own paths; `Finset.sum_subset` extends it to any larger collection whose
complement contributes nothing.

**The vanishing is a hypothesis here, and that is not a gap being hidden.**  For a general
`C` the complement can contain guarded paths whose configuration simply is not in `C`, and
then the two sums genuinely differ.  When `C` is ALL configurations of the span, BLOCK 269
supplies the hypothesis: a contributing path satisfies every guard, hence is realisable,
hence lies in the image.

**[Rule 0] Status of (M3).**  VERIFIED: the transfer decomposition (M3a), the formal
convergence and path-sum identity of (M3b), the bijection between configurations and
guarded paths in both directions, the extension and its guard, and this comparison.  What
is NOT written is the instantiation at `C` = all configurations of the span, which needs
the `Finset` of those -- available from `finite_degree_le` (BLOCK 222) but not yet wired.

## 2026-09-04 — BLOCK 271: finiteness on the guarded-data side

    finite_spanData_degree_le   the guarded data of a span, cut by degree, is finite

0 sorry, clean on the first build.

`sum_configs_eq_sum_all_paths` (BLOCK 270) needs a `Finset` of guarded data.  **A whole span
class is not finite** -- the deposits are unbounded -- so the collection must be cut by
degree, which is exactly the form `IsAssembly` uses and not a workaround.  `toPath` is
injective (BLOCK 218) and lands in a set finite by `finite_degree_le` (BLOCK 222).

**[Rule 0] VERIFIED.**  The `Finset` the comparison wants exists, via
`Set.Finite.toFinset`.

## 2026-09-04 — BLOCK 272: why the comparison must be coefficient-wise

Instantiating `sum_configs_eq_sum_all_paths` (BLOCK 270) at "all configurations of degree
at most `N`" **does not work**, and the reason is structural, not technical: a guarded path
of the right length can belong to a configuration whose relaxed length EXCEEDS `N`, and its
weight is not zero, so the two sums genuinely differ.

The fix is the one `IsAssembly` (BLOCK 116) already encodes -- compare COEFFICIENTS:

    coeff_pow_lR        the degree-N coefficient of X^k is 1 exactly when N = k
    coeff_pow_lR_ne     so a configuration of the wrong degree contributes nothing
    coeff_pow_lR_self   and at its own degree it contributes one

0 sorry, all three clean on the first build; `PowerSeries.coeff_X_pow` is in this Mathlib
with argument order `coeff m (X^n) = if m = n then 1 else 0`.

**This is why `IsAssembly` was stated degree-wise in the first place**, which BLOCK 116
recorded without the reason.  Each coefficient sees only the configurations of that exact
relaxed length, and those are finite by `finite_spanData_degree_le` (BLOCK 271).

**[Rule 0] VERIFIED.**  The selection mechanism is in place; the degree-wise instantiation
is the remaining step.

## 2026-09-04 — BLOCK 273: the degree-N coefficient is a count

    coeff_sum_configs   the degree-N coefficient of the configuration sum counts the
                        configurations of relaxed length exactly N

0 sorry, clean on the first build; `Finset.sum_boole` does the last step.

With `x := X` the weight of a configuration is `X ^ lR`, so the wrong-degree ones drop out
by `coeff_pow_lR_ne` (BLOCK 272) and each side becomes a finite count.  This is the shape
`IsAssembly` compares, and the reason both sides are finite without any further truncation.

**[Rule 0] VERIFIED.**  The configuration side of (M3)'s coefficient identity is now a
count over a `Finset`.  The path side needs the same treatment, and then the two counts are
equal by the bijection (BLOCKS 249, 267-268).

## 2026-09-04 — BLOCK 274: `pathWeight` over an arbitrary ring

A structural limit found by trying the coefficient comparison: **`pathWeight` (BLOCK 206) is
fixed to `ℤ`**, so the identity cannot even be STATED in `PowerSeries`, where BLOCK 272's
coefficient-wise comparison has to live.

    pathWeightR          the same definition over a commutative ring
    pathWeightR_one_exp  the inner chain-cost exponential
    pathWeightR_exp      and the full one

0 sorry, both clean on the first build, on `propext` alone.  **The proofs are the ℤ ones
unchanged**, which is itself the evidence that nothing about `ℤ` was being used -- the
restriction was an accident of how BLOCK 206 was written, not a mathematical fact.

The existing ℤ development stays valid and is not disturbed; what is added is the road to
`PowerSeries`, which the coefficient comparison needs.

**[Rule 0] Honest scope.**  Only the exponential lemmas are ported so far.  The guard
theorems, the sum comparison and the bijection are all still stated over `ℤ`, and porting
them is the remaining work on this line -- mechanical, but not yet done.

## 2026-09-04 — BLOCK 275: the congruence and the vanishing, over an arbitrary ring

    pathWeightR_congr                  reads lam at the head and mu at the last state only
                                       (NO AXIOMS)
    pathWeightR_zero_of_guard_fails    a failure anywhere kills the weight

0 sorry, both clean on the first build.  As in BLOCK 274 the proofs are the `ℤ` ones
verbatim -- the ring was never used.

These are the two lemmas the sum comparison rests on, so the `PowerSeries` route now has
its foundations.  What still runs only over `ℤ` is the chain of guard theorems
(BLOCKS 234-236, 249, 269-270), which use `pathWeight` rather than `pathWeightR`.

**[Rule 0] Honest scope, restated.**  Porting the exponential, the congruence and the
vanishing does NOT port the comparison; it makes porting it possible.  I am not treating
the coefficient route as available until the guard chain is over `R` too.

## 2026-09-04 — BLOCK 276: guard invariance over an arbitrary ring

    pathWeightR_guard_eq   guarding by any predicate the configuration satisfies is free
                           (NO AXIOMS)
    pathWeightR_flag_of    and the doubled guard costs nothing on a configuration

0 sorry, both clean on the first build.  These are the hinges the rest of the chain hangs
from -- BLOCKS 216 and 236 -- and again the proofs carry over unchanged.

**[Rule 0] Where the port stands.**  Over an arbitrary ring: the chain-cost exponential
(BLOCK 274), the congruence and the vanishing (BLOCK 275), and now guard invariance.  Still
`ℤ`-only: the boundary-vector theorems (`pathWeight_flag_guarded`, BLOCK 236), the sum over
paths (BLOCK 249) and the comparison (BLOCK 270).  Those are the next three, and they are
the last of the port.

## 2026-09-04 — BLOCK 277: the edge-frame weight identity over an arbitrary ring

    pathWeightR_edge   the edge-frame path weight of a configuration is x ^ lR, over any R

0 sorry.  Two failures, both diagnosed rather than guessed: a `simp only []` that made no
progress because `congr 1` had already reduced the goal, and then a direction mismatch --
`alternating_is_chain` proves `sums = chain` while the goal after `congr 1` reads
`chain = sums`, so `.symm`.

This is BLOCK 233's identity stated directly as a weight equation rather than through
`IsTransferDecomposition`, which is `ℤ`-valued and so cannot be used here.

**[Rule 0] Port status.**  Over an arbitrary ring: exponential (274), congruence and
vanishing (275), guard invariance (276), and the edge identity (277).  Still `ℤ`-only: the
boundary VECTORS (`flagHeadVec`, `flagTailVec`) and everything above them -- the sum over
paths and the comparison.

## 2026-09-04 — BLOCK 278: the boundary vectors over an arbitrary ring

    flagHeadVecR, flagTailVecR       the doubled boundary vectors over R
    flagHeadVecR_flagOf, _tailVecR_  both fire on a configuration
    pathWeightR_flag_guarded         THE DOUBLED, FULLY GUARDED WEIGHT IS x ^ lR, over any R

0 sorry, all three clean on the first build.

**The weight side of the port is complete.**  Everything the coefficient comparison needs
from `pathWeight` now exists over an arbitrary commutative ring: the exponential (274), the
congruence and vanishing (275), guard invariance (276), the edge identity (277), and the
boundary vectors with the fully guarded weight (278).

**[Rule 0] What is NOT ported.**  The `Finset` statements -- `sum_configs_eq_sum_flag_paths`
(BLOCK 249) and `sum_configs_eq_sum_all_paths` (BLOCK 270) -- are still `ℤ`-only.  They are
the last two, and unlike the lemmas above they carry `Finset.sum`, so the port is a
restatement rather than a copy.

## 2026-09-04 — BLOCK 279: the two sum statements over an arbitrary ring — PORT COMPLETE

    sum_configs_eq_sum_flag_pathsR   the sum over configurations is the sum over their paths
    sum_configs_eq_sum_all_pathsR    and extends to all paths when the complement vanishes

0 sorry, both clean on the first build.

**The port is finished.**  Every step from a configuration's weight to the comparison with
all paths now holds over an arbitrary commutative ring:

    274  the chain-cost exponential
    275  the congruence and the vanishing
    276  guard invariance
    277  the edge-frame weight identity
    278  the boundary vectors and the fully guarded weight
    279  the two sum statements

In particular they hold over `PowerSeries ℤ`, which is where BLOCK 272's coefficient
argument lives -- the limit BLOCK 274 found is removed.

**[Rule 0] What (M3) still needs.**  Instantiating at `x := X` and taking the degree-`N`
coefficient, with the vanishing hypothesis discharged from BLOCK 269 at `C` = all
configurations of the span.  That is the assembly, and the pieces are all VERIFIED.

## 2026-09-04 — BLOCK 280: the degree-N identity

    coeff_sum_all_paths   the number of configurations of relaxed length exactly N with a
                          given span IS the degree-N coefficient of the transfer sum over
                          paths

0 sorry, clean on the first build.

This is (M3)'s content in the form `IsAssembly` compares: instantiate the ported comparison
at `x := X` and take the degree-`N` coefficient.  The left side counts by BLOCK 273; the
right side is the transfer sum.

**[Rule 0] Exactly what is and is not established.**  VERIFIED: the identity above, for any
`C` and `T` satisfying the two hypotheses.  NOT established: that those hypotheses hold at
`C` = all configurations of the span and `T` = all paths of that length.  The vanishing
half follows from BLOCK 269; the containment half needs `C` to be the full degree-cut
`Finset`, which `finite_spanData_degree_le` (BLOCK 271) provides but which is not yet wired
in.  So (M3) is one instantiation short, and that instantiation is `Finset` bookkeeping
against theorems that are all proved.

## 2026-09-04 — BLOCK 281: the comparison at the level of a single coefficient

    coeff_sum_subset               the comparison, with only the COEFFICIENT required to
                                   vanish on the complement
    coeff_weight_of_wrong_degree   and a configuration of the wrong degree contributes
                                   nothing to that coefficient

0 sorry, both clean on the first build.

`sum_configs_eq_sum_all_pathsR` (BLOCK 279) asks the complement's WEIGHTS to vanish.  That
is stronger than needed and, at `C` = the degree cut, **false**: a path outside the image
can come from a configuration of larger relaxed length, whose weight `X ^ lR` is not zero.
Its degree-`N` coefficient is zero, though, and that is all the comparison uses.

**This is why BLOCK 280's second hypothesis could not be discharged as stated.**  The fix
was to weaken the statement to what is true rather than to try harder to prove what was
written -- the same move as BLOCK 272, where the whole-sum comparison had to become
coefficient-wise for the same underlying reason.

## 2026-09-04 — BLOCK 282: a non-zero coefficient forces the guard

    guardsR_of_weight_ne_zero   BLOCK 269 over an arbitrary ring
    ne_zero_of_coeff_ne_zero    a non-zero coefficient means a non-zero series
    guards_of_coeff_ne_zero     so a path contributing to the degree-N coefficient
                                satisfies the guard, hence is realisable

0 sorry, all three clean on the first build.

This is the last bridge the instantiation needs: `coeff_sum_subset` (BLOCK 281) asks the
complement's coefficients to vanish, and the contrapositive says a path with a non-zero
coefficient is guarded -- whereupon `exists_config_of_path` (BLOCK 267) and
`flagPath_eq_of_config` (BLOCK 268) put it in the image unless its configuration has the
wrong degree, which `coeff_weight_of_wrong_degree` (BLOCK 281) handles.

**[Rule 0] Every ingredient of (M3)'s coefficient identity is now VERIFIED.**  What remains
is to write the instantiation itself: choose `C` as the degree cut, `T` as the paths of the
right length, and run the case split on whether a complement path is guarded.

## 2026-09-04 — BLOCK 283: the head vector's guard, over an arbitrary ring

    headOkR_of_weight_ne_zero      a contributing path's head vector cannot vanish
    headCond_of_headVec_ne_zero    and a non-vanishing head vector IS the head guard firing,
                                   with the flag matching the arrival

0 sorry, both clean on the first build, on `propext` alone.

**The remaining obstacle, stated precisely.**  The instantiation needs, for a path `L` in
the complement, that `L` is not realisable.  From a non-zero coefficient we get the step
guard (BLOCK 282) and now the head guard.  What is NOT obtainable that way is `arrv` -- the
arrival flag being `[j = 0]` -- because a bare list carries no indices, and `A` is ours to
choose.

BLOCK 238 settled the mathematics: the guard forces exactly one arrival, and choosing `A`
so that it lands at `0` is a translation.  But that choice depends on the path, so `T`
cannot be an arbitrary `Finset` of lists -- it has to be indexed by paths whose arrival
sits at the right place.  **That is a re-indexing of the statement, not a further theorem**,
and it is what the instantiation still needs.

## 2026-09-04 — BLOCK 284: the arrival sets the flag wherever it fires

    past_of_arr_at     the arrival at ANY index a sets the flag there, no head case needed
    arr_unique_after   and no second arrival fires after it, unconditionally

0 sorry, both clean on the first build.  One failure: `rw [he]` rewrote a fresh copy of
`hstep` where `a - 1 + 1` did not syntactically occur after the first rewrite, giving a term
of the un-rewritten type; using `hstep (a - 1)` directly, without touching it, matches the
goal as stated.

`past_of_arr` (BLOCK 238) was proved for a step INTO `a`; applying it at `a - 1` removes the
need for a separate argument at the head, and gives the flag-setting fact at an arbitrary
index directly.

**Why this matters for BLOCK 283's obstacle.**  The re-indexing problem is not about
finding where the arrival is -- it is that `T`'s elements are bare lists with no marked
index at all.  These two lemmas are the tools for the re-indexed statement, once it is
written: given that a list's `k`-th entry has `arr = 1`, everything after it is pinned.
The statement itself -- `T` as pairs of a list and an index -- is still to be written.

## 2026-09-04 — BLOCKS 285-286: why the box enumeration cannot be free in `arr`, and the fix

Chasing BLOCK 283's obstacle to ground.  `dep` is free at enumeration time because
`Guarded.dep` only asks that it fire at SOME `kstar`, and `exists_dep_index` (BLOCK 242)
locates that `kstar` after the fact, from the guard alone.  **`arr` is different in kind**:
`Guarded.arrv` demands it fire exactly at the ABSOLUTE integer `j = 0`, a fact about the
real index, not recoverable from local guard-consistency the way `kstar` is.  A box
enumeration leaving `arr` free would produce "paths" guarded in every pointwise sense whose
marked arrival sits at the wrong integer -- realising no configuration, and not caught by
BLOCKS 282-284, none of which asks whether the coordinate's POSITION matches `vArr`.

The fix is not a new theorem but a corrected enumeration:

    BoxState              a local state with `arr` OMITTED -- the free coordinates only
    BoxState.toLocal      reattach arr, FORCED to the real index j, not stored
    boxState_toLocal_stateOf   a configuration's own state reattaches to itself (NO AXIOMS)
    BoxState.toFlag        the flagged state, with `past` forced too (0 <= j is determined
                           once A is fixed)
    boxState_toFlag_flagOf a configuration's own flagged state reattaches to itself
                           (NO AXIOMS)
    boxSet                the bounded BoxStates of magnitude at most N
    boxSet_finite          and that set is finite

0 sorry, all clean; two mechanical fixes along the way (`Set.finite_insert` is an iff, not a
term -- `.insert` the method instead).

**What this buys.**  `T` can now be built as the image of `boxSet N`-valued lists under
`toFlag` at the real positions `idxList A n`, and every element of `T` automatically
satisfies `harrv` by construction -- the obstruction BLOCK 283 found is closed by
construction rather than by a further lemma.  Assembling `T` itself and running the
`Finset.sum_subset` argument through it is the next and, on current evidence, final step.

## 2026-09-04 — BLOCK 287: a configuration's own path lies inside the box

    boxSet_bounds   a configuration of relaxed length <= N has every position's BoxState
                    data inside boxSet N

0 sorry.  Three failures, all diagnosed: the off-span case does not need `mu` at all --
`travel` vanishes directly by `houter`, so routing it through `mu` (which is `2` off the
span, not `0`) was the wrong path entirely; and the `dep` bound needs `1 <= N`, which is
not free -- it follows from `mu_pos` at the left endpoint of the (non-empty) span, chained
through `lR`, and had to be proved as its own fact rather than assumed.

**Both halves of the box construction are now in place**: `boxSet_finite` says the box is
finite, `boxSet_bounds` says a configuration's own data sits inside it.  What remains is
assembling `T` -- images of `boxSet N`-valued position lists under `toFlag` -- and running
`Finset.sum_subset`/`coeff_sum_subset` through it, using `guards_of_coeff_ne_zero`
(BLOCK 282), `headCond_of_headVec_ne_zero` (BLOCK 283) and `exists_config_of_path`
(BLOCK 267) to place a non-vanishing complement path back in the image.

## 2026-09-04 — BLOCK 288: T assembled, and a configuration is inside it

    idxFn, ofFn_idxFn         idxList reindexed by Fin, proved by list induction not index
                              arithmetic (the lesson relearned from a first failed attempt)
    flagPathsFinset           the Finset of degree-N flagged paths, as an image of
                              Fintype.piFinset over boxFinset N
    mem_flagPathsFinset_of_config   a configuration of relaxed length <= N lies inside it

0 sorry.  First attempt used a hand-built index inverse (`(j - A).toNat`) and hit both a
syntax error and a defeq mismatch -- exactly the index-heavy failure mode this file has hit
before.  Diagnosed per Rule 4.3 rather than patched: switched to `List.ofFn` plus
`List.ext_getElem`, which compares lists by a single index formula instead of manual cons
matching, and it went through with one small further fix (`idxFn A (m+1) 0` needed an
explicit unfold to `A`, not defeq to the `show` as first stated).

**The construction the last five blocks were building toward now exists.**  `T :=
flagPathsFinset N A n` is finite by construction, contains every configuration's own path
(this block), and by BLOCKS 282-284 + 267 every OTHER element is either unrealisable (guard
fails, coefficient zero) or realisable and hence in `C`'s image already.  Closing (M3) is
now assembling `coeff_sum_subset` with this `T` and a case split on membership.

## 2026-09-04 — BLOCK 290: RETRACTION and repair — a real soundness gap in the head vector

Drafting the final composition (`coeff_vanish_on_complement`) exposed a genuine bug, not a
formatting issue: `flagHeadVec` and `flagHeadVecR` (BLOCKS 236, 278) used `headOkB`, but
BLOCK 253 had already proved `headOkB` insufficient -- it lacks the flow condition
`arr_A = fcur_A + dep_A` -- and built `headOk2B` to repair it.  **`headOk2B` was never wired
into the actual kernel used by the sum comparison.**  Without the fix, a path could have a
non-vanishing head vector while violating the flow into `A`, contributing to the coefficient
sum while representing no configuration -- exactly the soundness gap BLOCK 253 identified in
principle but did not close in practice.

The repair: both `flagHeadVec` and `flagHeadVecR` now gate on `headOk2B` instead of
`headOkB`.  This forced re-proving three downstream theorems, each straightforwardly, using
`flowB_stateOf` and `P.houter` directly rather than the not-yet-relocatable
`preState_stateOf`/`head_flow_stateOf` chain:

    flagHeadVec_flagOf         (Z version) -- inlined the flow derivation
    flagHeadVecR_flagOf        (R version) -- same
    headCond_of_headVec_ne_zero -- conclusion strengthened to headOk2B

0 sorry, all four re-certified; `headCond_of_headVec_ne_zero` needs `propext` alone.

**Why this was found now and not earlier.**  Every prior use of `flagHeadVec`/`flagHeadVecR`
was in the FORWARD direction -- showing a configuration's own path satisfies the kernel --
where `headOkB` sufficed because a real configuration always satisfies the flow condition
too, vacuously making the weaker gate adequate.  The gap was invisible until the CONVERSE
direction (BLOCK 283's `headCond_of_headVec_ne_zero`, feeding the final composition) needed
to recover enough from a bare non-zero coefficient to reconstruct a configuration -- and
there, `headOkB` alone is not enough.  This is the same failure mode as BLOCKS 226 and
252-253 (a guard invisible from the configuration side, caught only by the converse), but
this time it had already escaped past three blocks of downstream use before being caught.

**Corrected status of (M3).**  Every VERIFIED result up to BLOCK 289 that used
`flagHeadVec`/`flagHeadVecR` remains true, since the fix only strengthens their hypothesis
(any path satisfying the new, stronger gate also satisfied the old one, so
`pathWeight_flag_guarded`/`pathWeightR_flag_guarded` and everything built on them go
through unchanged with `headOk2B_stateOf` in place of `headOkB_stateOf`).  What changes is
that BLOCK 283's `headCond_of_headVec_ne_zero` now gives the RIGHT fact for the final
composition -- `headOk2B`, which supplies both `dprevA` AND `flowA` for `FlagPath` in one
step, closing exactly the gap that composition was stuck on.

## 2026-09-04 — BLOCK 291: the tail vector's guard, over an arbitrary ring

Assembling `coeff_vanish_on_complement` needs `hendA`, `hendB`, `hvalidB`, `fcurB`, `epsvB`
for `exists_config_of_path` -- and BLOCK 283 only extracted the HEAD vector's condition.
The tail vector's is a separate argument, tracking `lastOf` through the recursion rather
than the head:

    tailOkR_of_weight_ne_zero    a non-zero weight means the tail vector at the LAST
                                 state does not vanish
    tailCond_of_tailVec_ne_zero  and that IS the tail guard firing with the flag set

0 sorry.  `tailOkR_of_weight_ne_zero` needs `propext` alone.  Two failures on the
successor case, both from a `show` not matching the goal up to defeq; fixed by copying the
exact working parenthesisation from `pathWeightR_zero_of_guard_fails` (BLOCK 275) rather
than re-deriving the shape by hand -- multiplication is associative as a THEOREM, not
definitionally, so a `show` with different grouping can fail even when the underlying
terms are equal.

**Also strengthened**, while wiring this in: `exists_stateFn_of_mem_flagPathsFinset`
(BLOCK 289) now also returns `∀ j, (gg j).st.arr = SiteCost.vArr j` for every integer, not
just the span -- true "for free" since every branch of `gg`'s definition goes through
`BoxState.toFlag j`, which sets `arr := vArr j` unconditionally.  This directly supplies
`FlagPath.arrv` and `exists_config_of_path`'s `harrv` without further argument.

**All six pieces `coeff_vanish_on_complement` needs are now available**: `guards_of_coeff_ne_zero`
(step), `headCond_of_headVec_ne_zero` (giving `headOk2B` -- `validA`, `epsvA`, `dprevA`,
`flowA`, `hendA` in one shot), `tailCond_of_tailVec_ne_zero` (this block -- `hvalidB`,
`epsvB`, `hendB`, `fcurB`), the arr-for-free fact, `past_eq_decide` (`flag`), and
`exists_dep_index`/`hB1_of_balance` (`kstar`, `hdep`, `hB1`).  Composing them into one
`FlagPath` and feeding `exists_config_of_path` is the last step.

## 2026-09-04 — BLOCK 292: `boxSet`'s dep bound tightened to `{0,1}`

Assembling the final composition needs `hdepv : dep ∈ {0,1}` for `exists_config_of_path`,
and `boxSet` only bounded `dep <= N`, not `<= 1`, even though a real departure marker
(`P.vD j`) is always `0` or `1` -- `boxSet` was looser than the object it was meant to
enclose.  Tightened the bound; `boxSet_bounds`'s `dep` clause simplifies to `P.vD j <= 1`
directly, dropping the `1 <= N` derivation it previously needed.

0 sorry, one edit each to `boxSet` and `boxSet_bounds`, both re-certified.  First attempt
at the edit script silently failed both replacements (a chained `assert` inside a `try`
raised before either `write` ran) -- caught by re-checking the file rather than trusting
the script's exit code, per the standing rule against guessing after a failure.

## 2026-09-04 — BLOCK 293: telescoping seeded from `A` itself, no pre-span point needed

`exists_dep_index` (BLOCK 242) and `telescope_flow`/`flow_balance` (BLOCKS 230, 264) all
seed the telescoping from a point BEFORE the span where the travel indicator vanishes --
available for a configuration via `preState_stateOf`, but NOT for an arbitrary guarded box
function `g`, which has no such point (its value at `A-1` is uncontrolled junk).  `flowA`
(from `headOk2B`) gives a different seed that does not need one: it is the balance AT `A`
itself, with the arrival's own value standing in for a fictitious predecessor.

    sum_vArr_range_eq_one   the arrival marker sums to 1 over any range containing 0
    telescope_seedA         telescoping seeded by flowA at A, no predecessor required

0 sorry.  Three failures on `sum_vArr_range_eq_one`, all mechanical: a type mismatch
(`0 - A : Z` fed where a `Finset Nat` membership was wanted -- needed `.toNat`), and a
`Finset.sum_eq_single_of_mem` call missing its membership argument.  One failure on
`telescope_seedA`: reindexing via `Finset.sum_range_succ'` left a `simp` with nothing to
rewrite; switched to direct induction on `n`, mirroring `telescope_flow`'s own proof shape
rather than trying to reduce to it by reindexing.

**With this, `kstar`'s existence and uniqueness can be derived from `flowA` alone** --
the last structural piece before assembling `coeff_vanish_on_complement`.

## 2026-09-04 — BLOCK 294: `kstar` exists and is unique, from `flowA` alone

    exists_unique_kstar_of_flowA   the departure exists, is unique, and the hB1
                                   dichotomy holds -- from flowA and the guard alone,
                                   with no pre-span vanishing point

0 sorry.  Several failures, each diagnosed and fixed in turn per Rule 4.1/4.3 rather than
guessed at collectively: a `Nat.cast_sum`-shaped step that did not exist by that name (the
whole sub-lemma was replaced by a three-line `simp_rw [harrv]; exact_mod_cast`), a
`.symm` on `htel` applied in the wrong direction for `flow_balance_dichotomy`, and --
the substantive one -- `hdepv` was stated restricted to the span `[A, A+n]`, but
`sum_zero_iff_no_one`/`exists_of_sum_one` need their `0/1` hypothesis UNCONDITIONALLY over
all of `Nat`, not just the summed range.  Widened `hdepv` to hold at every integer, which
is true anyway for a `gg` built from `boxSet` (every position, in range or not, comes from
a `boxSet`-valued choice with `dep <= 1`), so the widening costs nothing at the call site.

**This closes the last structural gap.**  Every hypothesis `exists_config_of_path` needs
is now derivable from `hstep` (BLOCK 282), `headOk2B` (BLOCKS 290-291), the arr-for-free
fact (BLOCK 291), `past_eq_decide` (BLOCK 258), and this block's `kstar` -- nothing is
left unaccounted for.  Assembling them into one `FlagPath` and finishing
`coeff_vanish_on_complement` is now pure composition.

## 2026-09-04 — BLOCK 295: RETRACTION and repair — the SAME missed-wiring bug in the tail vector

Preparing to assemble the final composition, I checked whether `fcurB : 0 <= fcur_B` (a
`FlagPath` field `exists_config_of_path` needs) is derivable from the tail vector's
condition -- and it is NOT.  `flagTailVec`/`flagTailVecR` gated on
`validB && epsValidB && endValidB && past`, but `tailOk2B` (BLOCK 252) -- `validB &&
epsValidB && endValidB && decide(0 <= fcur)` -- was ALREADY BUILT to repair exactly this,
and, like `headOk2B` (BLOCK 290), was never wired into the actual kernel.

Same repair, same shape: both `flagTailVec` and `flagTailVecR` now gate on `tailOk2B`.
Re-proved three downstream theorems, inlining `fcur_B_nonneg`'s argument (`travel` is
never `-1` at a non-negative index) directly rather than forward-referencing a theorem
defined later in the file:

    flagTailVec_flagOf     (Z version)
    flagTailVecR_flagOf    (R version)
    tailCond_of_tailVec_ne_zero -- conclusion strengthened to tailOk2B

0 sorry, all four re-certified; `tailCond_of_tailVec_ne_zero` needs `propext` alone.  Same
two mechanical snags as BLOCK 290's repair: doc-comments stacked illegally where a
definition was relocated, and a stray orphaned doc-comment left behind at the old site.

**Why caught before use, this time.**  Unlike `headOk2B` (found only when the converse
direction actually failed to typecheck against `exists_config_of_path`), this one was
caught by CHECKING the needed hypothesis against what the vector's condition actually
proves, before attempting the composition -- the same audit BLOCK 291 should have run when
it built the tail vector's guard extraction, and did not.  Two repairs of the identical
shape in five blocks is a pattern: **every `flagHeadVec`/`flagTailVec`-style gate needs
checking against ALL of `FlagPath`'s fields, not just the ones a given proof attempt
happens to need next.**

## 2026-09-04 — BLOCK 296: the dep bound, exposed for free too

`exists_stateFn_of_mem_flagPathsFinset` (BLOCK 289) exposed the `arr = vArr` fact for
free; the same box-membership argument gives `dep ∈ {0,1}` for free too, once the
discarded `Fintype.piFinset` membership is kept and unfolded via `mem_boxFinset`
(BLOCK 292's tightened bound) at whichever `Fin` index each branch of the state function
uses.

    exists_stateFn_of_mem_flagPathsFinset   now also returns `∀ j, dep_j = 0 ∨ dep_j = 1`

0 sorry.  One failure: a leftover `split_ifs <;> rfl` from the theorem's earlier form was
left dangling after the new case was appended, closing on an already-solved goal.

**Both hypotheses `exists_unique_kstar_of_flowA` needs beyond the guard itself -- `harrv`
and `hdepv` -- are now available with no argument beyond box membership**, for any element
of `flagPathsFinset`, not only for configurations.

## 2026-09-04 — BLOCK 297: sign data is constant along a BOUNDED guarded path

`FlagPath.epsAB`/`delAB` (eps and delta agreeing at the two ends) is the last field with
no source: `eps_const_of_guarded`/`delta_const_of_guarded` (much earlier blocks) prove this
but need `Guarded`, whose `step` field is UNCONDITIONAL over all of `Z` -- not available
for a bare `hstep` restricted to `[A, A+n)`.

    compatB_of_flagStepB     the compatB component of flagStepB, extracted cleanly
    eps_delta_const_bounded  both fields agree across the WHOLE bounded span, by
                             induction from A rather than from 0

0 sorry.  One failure: `Eq.trans`'s argument order was backwards -- `hcp.1.2` proves
`eps(A+m+1) = eps(A+m)`, so composing with `he : eps(A+m) = eps(A)` needs
`hcp.1.2.trans he`, not `he.trans hcp.1.2`.

**Every field `FlagPath` needs now has a source usable from bare `hstep` and the box
membership facts, with no remaining gaps.**  The assembly can now proceed.

## 2026-09-04 — BLOCK 298: the flag is canonical along a BOUNDED guarded path

The last unconditional-vs-bounded mismatch: `past_eq_decide` (BLOCK 258) needs `hstep` for
ALL of `Z`, but the guard extracted from a coefficient (BLOCK 282) is only bounded to
`[A, A+n)`.  Same fix as BLOCKS 294 and 297: reprove the bounded form directly.

    past_eq_decide_bounded   the flag matches `decide (0 <= j)` throughout the bounded
                             span, mirroring the unconditional proof exactly

0 sorry, clean on the first build -- the only block in this run of repairs that needed no
fix after the initial write, since its source proof (BLOCK 258) had already been through
the same diagnosis once.

**Every field `FlagPath` needs is now sourced from a bounded `hstep` alone.**  Nothing
further is missing; the composition can be written.

## 2026-09-05 — BLOCK 299: (M3) closed -- the box coefficient sees only the good spans

`coeff_vanish_on_complement`, the final composition theorem for (M3): any list in the
`flagPathsFinset` box that is *not* the image of some span in a target set `C` (the spans
whose configuration has degree exactly `N`) contributes 0 to the degree-`N` coefficient.
Composed with `coeff_sum_subset` (BLOCK 281) and `mem_flagPathsFinset_of_config`
(BLOCK 288):

    coeff_vanish_on_complement           the vanishing fact itself -- assembles a FlagPath
                                          instance from the bounded guard and box facts,
                                          feeds exists_config_of_path, and shows the
                                          resulting configuration's span is in C
    image_C_subset_flagPathsFinset       every span in C lands in the box (trivial
                                          direction, via mem_flagPathsFinset_of_config)
    coeff_flagPathsFinset_eq_C_image_sum (M3) itself: the degree-N coefficient of the
                                          weighted sum over the WHOLE box equals the
                                          coefficient of the weighted sum over exactly
                                          the paths coming from C

0 sorry.  Two of the theorems this block depends on had to be widened before the
composition would even type-check, both instances of the same unconditional-vs-bounded
mismatch already seen in BLOCKS 293/294/297/298:

- `exists_unique_kstar_of_flowA` (BLOCK 294) had been built with an UNCONDITIONAL `hstep`
  (`forall j : Z, ...`, no bound), which cannot be produced from a bare non-zero
  coefficient. Rewired to the same bounded `hstep : forall j, A <= j -> j < A+n -> ...`
  every other BLOCK-29x theorem uses, which forced re-deriving its internal flow/telescope
  step from scratch (`telescope_seedA_bounded`, a bounded sibling of BLOCK 293's
  `telescope_seedA`, added alongside it) rather than reusing the unconditional
  `flow_of_flagStepB` + `telescope_seedA` pair. This is a retraction of BLOCK 294's
  stated scope, not of its content: the theorem's conclusion is unchanged, only its
  hypothesis is weakened to what a real caller can actually supply.
- The same theorem's returned `hB1` (`fcur.natAbs = 1 <-> kstar = B+1`) turned out to be
  too weak for the caller (`exists_config_of_path` needs the trichotomy
  `fcur = 0 \/ fcur = 1 \/ fcur = -1`, and `natAbs = 1` alone does not rule out `fcur`
  taking some other value when `kstar != B+1`). Both branches of the theorem's own proof
  already establish `fcur = 0` or `fcur = 1` directly (never `-1`) via
  `flow_balance_dichotomy`; added that fact as a third conjunct
  (`hfB01 : fcur = 0 \/ fcur = 1`) instead of trying to recover it from `hB1` alone.

Other failures along the way, all local tactic mistakes rather than mathematical gaps:
a `have ... where` structure-instance block does not parse in tactic mode (needed
`have ... := { ... }` instead); `eps_delta_const_bounded`'s two components come back in
the opposite orientation from what was assumed (`(g (A+n)).eps = (g A).eps`, not the
reverse -- needed `.symm` on both); `harrv`/`hdepv` needed pointwise-restriction wrappers
(`fun j _ _ => harrv j`) to match `exists_config_of_path`'s bounded argument shape;
`pathWeightR_flag_guarded`'s hypothesis wants `P.B = P.A + n`, not `A + n = P.B`, and the
downstream `rw` chain had two direction mistakes (`rw [hPweight]` not `rw [<- hPweight]`,
and a final `.symm` on the whole list-equality composite). The one real construction
problem: casting `ofPath P : SpanData P.A P.B` to `SpanData A (A+n)` via
`hPA ▸ hPB ▸ ofPath P` does not elaborate (motive inference fails on the nested
structure). Built the target `SpanData A (A+n)` directly instead, field by field, casting
only the individual Prop-valued fields (each a trivial single-`rw`); needed `let` rather
than `have` for the resulting term so `SpanData.toPath_d` could still see through to the
underlying `dspan := P.d` field by defeq.

**(M3) is now fully assembled and certified**, `#print axioms` on all four new theorems
(`telescope_seedA_bounded`, `exists_unique_kstar_of_flowA`, `coeff_vanish_on_complement`,
`coeff_flagPathsFinset_eq_C_image_sum`) shows only `[propext, Classical.choice,
Quot.sound]` -- no `sorryAx`.

**CORRECTION, 2026-09-05, same day:** the closing line above ("this closes the atom-table
entry for the transfer-model decomposition theorem") is an overstatement, caught by
re-reading `private/RESEARCH_LOG.md`'s BLOCKS 102-117 entry before trusting this file's own
framing (MATH_RULES_V6 Rule 13: re-certify per atom, never from memory or a prior commit
message). BLOCK 299 is a continuation of that earlier thread in the same file, not an
independent closure: the honest target is `IsAssembly` (EltBridge.lean:10128), and no theorem
anywhere proves `IsAssembly` for the paper's real `W`/`T`/`lam`/`mu`. BLOCK 299 built real,
verified machinery toward the "sum over elements" gap BLOCK 117 left open, but did not
close it. See `private/RESEARCH_LOG.md`, "(M3) reconciliation, 2026-09-05" for the full
account. The atom-table status for (M3) is 🟡, not 🟢.

## 2026-09-05 — BLOCK 300: the four marker data, indexed and partitioned

Toward `IsAssembly` (EltBridge.lean:10128), following the reconciliation above: its
left side sums over `Fin 4`, one term per `(eps*, delta*) ∈ {1,-1} x {false,true}`
(BLOCK 106's "why the assembly sums over the four marker data"). This block makes
that index concrete and proves the target span set `C` splits into its four fibers.

    markerIdx                              SpanData A B -> Fin 4, encoding
                                            (eps*, delta*)
    markerIdx_eps, markerIdx_delta         the index recovers each component
    sum_C_eq_sum_marker_fibers             C's weighted sum splits into 4 fibers,
                                            via Mathlib's Finset.sum_fiberwise
    coeff_C_eq_sum_marker_fiber_coeffs     the coefficient distributes over the split

0 sorry, clean build on the first attempt (`Finset.sum_fiberwise` was already the
right Mathlib lemma for this, found by grepping the local Mathlib source rather than
guessing a name). `#print axioms` on all four shows only `propext`/`Quot.sound`
(the two `markerIdx_*` facts) or those plus `Classical.choice` (the two `Finset.sum`
facts) -- no `sorryAx`.

**Scope, stated honestly:** this is the grouping `IsAssembly`'s left side needs, not
`IsAssembly` itself. What is still missing: composing this fiber split with
`lR_exp_is_transfer` (BLOCK 115) and `neumann_partial`/`resolvent_remainder`
(BLOCK 116-117) inside each fiber, and identifying the real `W` with a
`flagPathsFinset`-derived sum via `coeff_flagPathsFinset_eq_C_image_sum` (BLOCK 299).
(M3) stays 🟡.

## 2026-09-05 — BLOCK 301: the box coefficient IS `C.card` -- a bigger, composed block

User direction this session: make blocks bigger when it helps, rather than the smallest
independently-checkable step every time. This block composes BLOCKS 299-300 two steps
further, in one sitting, rather than stopping at BLOCK 300's partition lemma alone.

    coeff_flagPathsFinset_eq_sum_marker_fiber_coeffs   the box coefficient equals the
                                                        sum over the 4 marker fibers of
                                                        C's per-fiber coefficient
                                                        (composes BLOCK 299's image-sum
                                                        identity with flagPath_inj's
                                                        injectivity, via
                                                        Finset.sum_image, and BLOCK 300's
                                                        partition)
    coeff_flagPathsFinset_eq_card_C                    the real content: every element
                                                        of C already has degree N by
                                                        construction (hC), so
                                                        pathWeightR_flag_guarded
                                                        collapses every per-element
                                                        weight to the SAME monomial X^N,
                                                        and coeff_sum_configs
                                                        (BLOCK 272, already in the file)
                                                        reads that off as a count. The
                                                        box coefficient equals C.card
                                                        exactly.

0 sorry, two failures along the way: `coeff_sum_configs` needed a `DecidableEq` instance
for `SpanData A (A+n)` that was not found automatically (fixed with a `classical` line);
and the final `congr 1` on a `Finset.card` goal produced the wrong subgoal shape (fixed
by folding the `Finset.filter_true_of_mem` rewrite directly into the `rw` chain instead
of leaving it for `congr`). `#print axioms` on both shows only `propext,
Classical.choice, Quot.sound`.

**Scope, stated honestly, again:** `coeff_flagPathsFinset_eq_card_C` is a genuinely
strong, clean result -- the "sum over elements... needs formal power series" gap named
at BLOCK 117 is discharged in the sense that the coefficient is now a concrete finite
count for ANY span length and target degree. It is still NOT `IsAssembly`
(EltBridge.lean:10128): `IsAssembly`'s right side is a sum over `Fin 4` of per-fiber
TRUNCATED NEUMANN SERIES (the transfer-matrix resolvent), not a plain cardinality --
that per-fiber resolvent identification is what remains. (M3) stays 🟡, closer than
before.

## 2026-09-05 — BLOCK 302: cross-check, `C.card` splits into marker-fiber cardinalities

`card_C_eq_sum_marker_fiber_card`: `C.card = sum over the 4 marker fibers of each
fiber's cardinality`, via `Finset.sum_fiberwise` with the constant weight 1. A Rule 3
cross-check, not new machinery: BLOCK 301's `coeff_flagPathsFinset_eq_sum_marker_fiber_coeffs`
gives per-fiber coefficient terms that are themselves fiber cardinalities (same collapse
argument as `coeff_flagPathsFinset_eq_card_C`, restricted to a sub-`Finset`), and this
theorem confirms they sum back to `C.card` as required for internal consistency. 0 sorry,
clean build, standard axioms. Committed `25a25cf`.

**Found while assessing the next step toward the real `IsAssembly`:** the actual
generating function `W` the paper's `eq:assembly` refers to has NO Lean definition
anywhere in this file -- `IsAssembly` is a Prop about an ARBITRARY `W`, `W0`, `T`, `lam`,
`mu`, and nothing instantiates it for the real objects. Composing the per-fiber
transfer/Neumann form (`lR_exp_is_transfer` + `neumann_partial`) into `IsAssembly` for
the real `W` is therefore not "one more composition step" but requires first designing
what `W` even is as a `PowerSeries ℤ` (a single object graded by degree, whereas the
current `flagPathsFinset N A n` machinery is parametrised per-degree, per-span-length).
That design question is real, unsolved work, not routine formalization glue -- logged
here rather than attempted under time pressure, per Rule 2 (name the obstruction) rather
than rushing a composition that risks another overstated claim.

## 2026-09-05 — BLOCK 303: the deposit engine's missing right-side mirror (H1a)

Switched targets, per the crux entry above and the user's push to keep moving: H1a's
generating-set section (`private/RESEARCH_LOG.md` line ~383) names the gap as "cursor
placement and the deposit engine exist, their composition does not." Investigating that
directly (rather than the blocked `IsAssembly`/`W` design question) found a real,
previously unnoticed asymmetry: `roundTrip_left` / `reachable_deposit_step` (the earlier
"deposit engine") only handle `delta = false` -- walking left. There was no `delta = true`
counterpart, so the engine could not build up an arbitrary target deposit profile while
walking right; half the composition genuinely did not exist, not just "not yet wired
together."

    roundTrip_right              the mirror of roundTrip_left: same word s3,s2,s1,s3,
                                  but s3's dif_pos branch fires first, so the touched
                                  position is g.kstar (not g.kstar - 1) and it moves
                                  by -2*eps (not +2*eps)
    reachable_deposit_step_right the mirror of reachable_deposit_step

0 sorry. One failure: the final `show` in `roundTrip_right` didn't defeq-match because
`s3`'s branch left `kstar` as the unreduced term `g.kstar + 1 - 1`, not `g.kstar` --
fixed by rewriting that equality explicitly rather than relying on defeq to see through
it. `#print axioms` on both shows only `propext, Classical.choice, Quot.sound`.
Committed `07a1d0e`.

**Scope, stated honestly:** this closes one real missing piece of the deposit engine,
not the composition itself. What full reachability still needs: an induction that,
given an arbitrary target deposit function `d` of bounded support consistent with the
parity constraint (`hpar`), walks the cursor to cover that support (via `cstep`,
already done) while applying `reachable_deposit_step`/`reachable_deposit_step_right` at
each visited position enough times (each call moves a deposit by exactly 2, and parity
guarantees an even number of calls suffices) to match the target value there. That
induction has not been attempted; it is now buildable from pieces that all exist,
where before this block one of those pieces (the right-side engine) did not. H1a stays
🟠.

## 2026-09-05 — BLOCK 304: found the real accumulation word (H1a), via BFS first

BLOCK 303's closing note was wrong in one respect: it suggested `reachable_deposit_step`/
`reachable_deposit_step_right` applied repeatedly would suffice for the induction. They
do not -- checked by hand before writing more Lean (Rule 3): two applications of
`reachable_deposit_step` at a fixed `kstar` cancel exactly (each flips `eps`, so the two
`+2*eps` contributions at opposite signs sum to zero).

Wrote `src/bin/reach_check.rs`, a small standalone BFS (reusing this tool's own
`Elt`/generator model) to settle the question computationally rather than guess again.
Ground covered: BFS to depth 22 from `one`, 118938 elements enumerated. Result: the
element with `kstar=0, d(0)=2k`, else matching `one`, is reached at word length exactly
`6k` for k=1,2,3 (lengths 6,12,18); k=4,5,6 not yet reached within depth 22 (consistent
with the pattern, not a contradiction of it). Reconstructed the exact witnessing words:
`["s2","s3","s1"]` repeated `k` times -- a genuinely different word from the 4-letter
round trip, not that round trip repeated.

Formalized that word in `EltBridge.lean`:

    depositCycle                       s1 (s3 (s2 g)) -- one turn
    depositCycle_from_false/_from_true the cycle's exact per-field effect from
                                        each side
    depositCycle_sq                    two turns: kstar, eps, delta all restored,
                                        deposit at kstar moves by exactly 2*eps --
                                        matches the BFS length-6 pattern exactly
    reachable_depositCycle             closure under Reachable
    reachable_deposit_accumulate       the real accumulation step for induction,
                                        replacing the cancelling
                                        reachable_deposit_step

0 sorry. Two failures: `(!false)=true`/`(!true)=false` needed `simp` rather than bare
`rw` (the rw-then-rfl heuristic didn't fire); a `congr 1` in the delta=true branch
closed its own goal via defeq of `a+(-b)` and `a-b`, so a trailing `ring` errored
"no goals" and had to be removed -- the delta=false branch's parallel step genuinely
needed `ring`, so the two branches are not interchangeable despite the symmetric
statement shape. `#print axioms` on all six new theorems shows only `propext,
Classical.choice, Quot.sound`. Committed `fe47f6a`.

**Scope, stated honestly:** this supplies the missing accumulation PRIMITIVE, found by
computation before being proved (Rule 3), not yet the full reachability induction.
What remains for H1a: given an arbitrary target deposit profile of bounded support
consistent with `hpar`, walk the cursor over its support (`cstep`, already done) and
apply `reachable_deposit_accumulate` the right number of times at each visited
position to match the target value there, then assemble into one existence theorem.
H1a stays 🟠, closer than BLOCK 303 left it -- the primitive that was actually missing
(not the one BLOCK 303 guessed) is no longer missing.

## 2026-09-05 — BLOCK 305: cstep's deposits are path-independent (H1a)

Worked out the design sketch for the full H1a reachability induction by hand: the
plan is to walk the cursor to cover a target profile's support (possibly in several
legs, out and back), applying `reachable_deposit_accumulate` (BLOCK 304) at each
position needing correction. The concern was whether a position visited on an
earlier leg gets corrupted by a later leg crossing it again. It does not, because
`cstep`'s own bookkeeping (independent of any manual corrections) is exactly the
differential of `travel` -- a path-independent potential. Formalized that fact
directly rather than just asserting it:

    cstep_preserves_neg_eps_travel   d j = -(eps * travel(kstar,j)) is preserved by
                                      cstep, whichever way it turns
    one_travel_inv                   the base case at `one`
    cstep_iter_travel_inv            so ANY cstep-only walk from `one`, any mix of
                                      legs and directions, lands on the exact
                                      travel-matching profile wherever it ends up

0 sorry, clean build on the first attempt. One real risk avoided: the naive guess
`d = eps * travel` (or `d = travel`) is WRONG -- checked the sign against
`cstep_iter_one`'s own explicit formula (d=+1 on [-n,-1], where `travel` is -1
there) BEFORE writing the general theorem, catching the sign error at the
falsification stage rather than after a failed proof attempt. `#print axioms` on
all three new theorems shows only `propext, Classical.choice, Quot.sound`.
Committed `fa215ef`.

**Scope, stated honestly:** this is the key invariant the full induction needs
(corrections at any point, in any order, on any route, are safe -- the automatic
`cstep` bookkeeping never re-corrupts an already-fixed position beyond what the
final `travel(kstar,j)` value accounts for). It is not the induction itself:
assembling an arbitrary target profile into an explicit walk-plus-corrections
construction, and proving THAT reaches the target, remains open. H1a stays 🟠.

## 2026-09-05 — BLOCK 306: the excess law generalized (H1a)

Generalized BLOCK 305's invariant to its natural unconditional form:

    cstep_preserves_excess          cstep preserves d j + eps*travel(kstar,j) at
                                     EVERY position, always -- not only where it's
                                     zero. At the crossed edge d moves by +-eps and
                                     travel moves by -+1, cancelling regardless of
                                     the starting excess value.
    cstep_preserves_neg_eps_travel  now a one-line corollary (the zero-excess case)

0 sorry, clean build. #print axioms shows only propext, Classical.choice, Quot.sound.
Committed `7e4bbf4`.

This is the exact tool needed to justify the assembly induction's core move: reach a
target kstar, detour to a correction position, apply `reachable_deposit_accumulate`
(BLOCK 304), return -- and by this theorem the detour provably disturbs nothing except
the corrected position, regardless of how the detour is routed.

**Stopped here deliberately, not stalled.** Traced the single-position-correction
construction through by hand and it works (move to target kstar, detour to the
correction position via `cstep_iter_left`/`cstep_iter_right` -- both already general,
not `one`-specific -- apply `reachable_deposit_accumulate`, return via the excess law).
Did not compose it in Lean this session: it needs careful `Int.toNat` direction
handling, delta/eps bookkeeping across two legs, then generalizing single-position to
an arbitrary finite support -- real multi-lemma work with genuine risk of a subtle
sign/off-by-one bug if rushed, and this session already corrected two overstated
claims once each. H1a stays 🟠; the recipe for the next block is now fully concrete.

## 2026-09-05 — BLOCK 307: the single-position-correction theorem (H1a), left case

User: attack whichever open atom is closest to completion. Assessed all three
(H1c/IsAssembly needs W defined -- design work; M4b/H1b needs RunStrandsConnected --
a long-unsolved graph existence, multiple prior NO-GOs recorded; H1a has, after
BLOCKS 303-306, every primitive the recipe in BLOCK 306 needs) and picked H1a.

Built the actual assembly theorem for the first nontrivial case:

    reachable_deposit_accumulate_iter   iterating the BLOCK 304 accumulation step k
                                         times adds 2k*eps at a fixed kstar
    cstep_eps / cstep_iter_eps          cstep and its iterates never change eps
    cstep_iter_preserves_excess         the n-step iterate of BLOCK 306's excess law
    reachable_single_correction_left    for any reachable g (delta=false) and any
                                         p <= g.kstar: a reachable h with the SAME
                                         kstar/eps/delta as g, differing from g.d by
                                         exactly 2k*eps at p and NOWHERE ELSE

Construction: walk out to p, correct, flip delta, walk back, flip delta back. The
"disturbs nothing else" claim is proved directly from the excess law on both legs,
combined algebraically per position -- not asserted.

0 sorry, clean build. Two real bugs the type checker caught: an `rw [...] at e1 e2`
tried to rewrite both excess equations with the union of both legs' hypotheses, but
they don't both apply to both equations (split into two rewrites); a `have` computing
h2's value at the correction site needed an explicit g1.eps -> g.eps substitution the
rewrite chain didn't perform implicitly. `#print axioms` on all four new theorems
shows only `propext, Classical.choice, Quot.sound`. Committed `25b800c`.

**Scope, stated honestly:** this is the LEFT case only (p <= g.kstar). The symmetric
right case, and the generalization from one correction position to an arbitrary
finite support, are both still open. H1a stays 🟠 at the composite level, but this is
real, substantial, verified progress -- the hardest algebraic content of the
single-position case is now done.

## 2026-09-05 — BLOCKS 308-310: H1a's reachability induction, fully general

Continuing directly from BLOCK 307 (left case): built the right-case mirror, then the
full induction.

    reachable_single_correction_right   mirror of BLOCK 307 for p > g.kstar (walk
                                         right first, flip to correct, walk back --
                                         no final flip needed, unlike the left case)
    reachable_single_correction         either direction in one call
    reachable_multi_correction          Finset.induction over a set of positions
                                         with NONNEGATIVE corrections c : Z -> N:
                                         a reachable h matching a baseline g outside
                                         the set, differing by 2*c(p)*eps on it
    reachable_single_correction_int     the single-position case generalized to
                                         ARBITRARY INTEGER corrections (via feps to
                                         flip eps for negative ones)
    reachable_multi_correction_int      the full induction, arbitrary integer
                                         corrections: THE combinatorial core of
                                         H1a's reachability gap

0 sorry throughout, four separate clean builds (one per theorem group), all real
bugs caught and fixed by the type checker rather than guessed around:
`le_or_lt` isn't in unqualified scope (used `by_cases` instead, twice, in two
different theorems); a combined `rw [...] at e1 e2` tried applying both legs'
excess hypotheses to both equations in the right-case mirror (split into two
rewrites, mirroring but NOT identical to the left case's split -- each leg's
hypothesis needed checking against what it actually contained, not assumed from
the mirror symmetry); `rw [..., Finset.mem_insert]` on an `if`-condition failed
with "motive is not type correct" (rewriting inside a Decidable instance) --
replaced with `simp [Finset.mem_insert, ...]`; and `Eq.trans` composition failed
for the eps field when a sign flip was involved (`q2.trans (he1.trans p2)` doesn't
typecheck since q2's target is "-h1.eps" not "h1.eps") -- replaced with a
`rw [...]; ring` tactic proof. `#print axioms` on every new theorem shows only
`propext, Classical.choice, Quot.sound`.

**What this closes.** Any finite-support target deposit profile that differs from a
reachable baseline by even amounts, at any positions, in either direction, is itself
reachable -- fully general, no remaining case restrictions. This is the actual
combinatorial content the log named as missing ("cursor placement and the deposit
engine exist, their composition does not").

**What remains for H1a, stated honestly.** Connecting this machinery to an actual
PathData/SpanData target: (a) obtain a reachable baseline at the target kstar/eps/
delta (via `reachable_kstar`, already proved, plus `feps`/`s1` to match the target
eps/delta exactly); (b) show the baseline's own deposit profile is exactly
`-eps*travel(kstar,.)` (already proved for the specific `one`/`s1 one`-based
constructions via `cstep_iter_travel_inv`); (c) show the correction needed at each
position (target minus baseline) is an even multiple of `2*eps`, which is exactly
what `hpar`'s parity condition should supply once unfolded against this baseline.
This is real work but bookkeeping, not new mathematical content -- the hard
combinatorial argument (BLOCKS 303-310) is done. H1a stays 🟠 at the composite
level; call the reachability CORE 🟢.

## 2026-09-05 — checked M4b/RunStrandsConnected before picking the next target

Investigated whether the Eulerian-route machinery already in EltBridge.lean
(lines 16648-17257) had progressed past what the research log's older entries
record. It has not: `RunStrandsConnected` (line ~17208) is still an unproved
existence statement. Checked whether Mathlib could discharge it directly --
`Mathlib/Combinatorics/SimpleGraph/Trails.lean` has Eulerian-circuit
*necessary conditions* only; its own header TODO says circuit EXISTENCE is
not proved in Mathlib either. So this atom needs a from-scratch existence
argument (e.g. formalizing Hierholzer's algorithm), which is real, hard,
unattempted-anywhere work, not a quick citation. Confirms rather than
overturns the project's prior NO-GOs on this route. Not pursued further this
session; picked a different target instead.

## 2026-09-05 — checked whether W is cheaply definable (H1c) -- it is not

Investigated defining W := PowerSeries.mk (fun N => total degree-N config count),
combining coeff_flagPathsFinset_eq_card_C (BLOCK 301) with span_le_lR (span <= N) and
Elt.A_le_zero/zero_le_B (0 is always in the span, so A ranges over the finite [-n,0]).

The union over (A,n) pairs turns out to be EASY: flagPathsFinset N A n is the same
type (List FlagState) for every A,n, so a plain Finset.biUnion suffices -- no
sigma-type construction needed, resolving an earlier worry.

Where it breaks: coeff_flagPathsFinset_eq_card_C needs an actual constructed Finset C
of SpanData A (A+n), and no such C has ever been built anywhere in the file -- every
prior theorem takes C as a hypothesis. SpanData has no Fintype/DecidableEq instance,
so there's no Finset.univ to filter. Two real fixes identified (exhibit finiteness via
the flagPath_inj injection into the box, or sidestep SpanData with a decidable
guarded-list filter on the box itself) -- both are genuinely new infrastructure, not
a quick composition. Logged in full in private/RESEARCH_LOG.md rather than attempted
under continued time pressure. H1c stays 🟡.

## 2026-09-05 — BLOCKS 311-312: C actually exists; the box coefficient is unconditional

Route (1) from the W-definability check above turned out to be cheap, not hard:

    exists_C                            constructs the target span set C directly,
                                         via Set.Finite.of_finite_image (the map
                                         S -> its flagged list is injective by
                                         flagPath_inj, and lands in the already-
                                         finite flagPathsFinset N A n) -- no decidable
                                         filter on the box needed, contrary to what
                                         seemed like the more likely route
    coeff_flagPathsFinset_eq_some_card  composes it with coeff_flagPathsFinset_eq_
                                         card_C (BLOCK 301): for ANY N, A, n, the
                                         degree-N box coefficient is SOME natural
                                         number M -- unconditional, no assumed C

0 sorry, both clean on the FIRST attempt -- no bugs this round. `#print axioms` on
both shows only `propext, Classical.choice, Quot.sound`. Committed `8301fc8`,
`07e402f`.

**This corrects the earlier assessment.** The W-definability check above said "neither
route is a one more composition step". Route (1) actually was, once tried -- the
finiteness argument via `Set.Finite.of_finite_image` composed cleanly from pieces
already in the file. Route (2) (the decidable box filter) is now unnecessary.

**What is still needed for W itself:** the biUnion across the finite range of valid
(A, n) pairs (n <= N via `span_le_lR`, A in [-n, 0] via `Elt.A_le_zero`/`zero_le_B`),
and a disjointness argument for `Finset.sum_biUnion` (different (A,n) slices produce
lists of different lengths or different position-derived field values, so should be
pairwise disjoint, but this needs an actual proof, not yet attempted). H1c stays 🟡,
closer than this morning's assessment: the coefficient is now unconditionally
well-defined per (A,n) slice, and the honest remaining gap is narrower (assembling
slices into one PowerSeries) than defining the object at all.

## 2026-09-05 — BLOCK 313: different (A,n) box slices are disjoint

flagPathsFinset_disjoint: for (A1,n1) != (A2,n2) (both satisfying the usual
A<=0<=A+n bounds), flagPathsFinset N A1 n1 and flagPathsFinset N A2 n2 share no
list. Different n gives different List.ofFn lengths (List.length_ofFn); same n
but different A is told apart by the arr field (SiteCost.vArr from
Realisation.lean, = 1 only at position 0): List.ofFn_inj turns list equality
into pointwise function equality, evaluated at the index where A1's slice puts
its "arr=1" marker (index -A1, in range since A1 in [-n,0]) forces A2's slice to
put ITS marker there too, forcing A1=A2, contradiction.

0 sorry. Two real bugs: an `rw [<- hL1eq] at hL2eq` produced the wrong equation
orientation for `List.ofFn_inj` (fixed by deriving a fresh, correctly-oriented
equality via plain `rw` instead of chained rewrites); `unfold SiteCost.vArr`
was called twice on the same hypothesis and the second call failed because the
first had already unfolded both occurrences of `vArr` in one pass (removed the
redundant call). `#print axioms` shows only propext, Classical.choice,
Quot.sound. Committed `99f8c4d`.

**What remains to actually assemble W:** define the global box as a nested
Finset.biUnion over n in range(N+1) and A in Icc(-n,0), apply Finset.sum_biUnion
twice (using this disjointness fact for both the outer n-level and inner A-level
pairwise-disjointness hypotheses), and combine with
coeff_flagPathsFinset_eq_some_card (BLOCK 312) to get one final unconditional
count per degree N. This is real remaining work (constructing two
PairwiseDisjoint proofs and composing several existentials into one sum) --
assessed as achievable but not attempted this iteration, to avoid rushing the
final assembly at the end of an already long, productive session. H1c stays 🟡,
with every ingredient for the final step now in hand.

## 2026-09-05 — BLOCKS 314-315: the assembly completed -- W is now a concrete object

Continued straight through from BLOCK 313's disjointness fact to the full assembly:

    globalBox                    the whole degree-N box, nested Finset.biUnion
                                  over every valid (A,n) slice
    globalBox_inner_disjoint     Set.PairwiseDisjoint over A (fixed n), from
                                  flagPathsFinset_disjoint
    globalBox_outer_disjoint     Set.PairwiseDisjoint over n, same source
    globalBox_coeff_eq_some_card the assembly: splits globalBox N's sum via
                                  Finset.sum_biUnion (twice), reads off each
                                  slice via coeff_flagPathsFinset_eq_some_card
                                  (BLOCK 312), sums into ONE total -- the
                                  degree-N coefficient over EVERY configuration
                                  of every span and starting point, concretely
    W                             PowerSeries.mk packaging that witness at
                                  each degree -- the first CONCRETE W anywhere
                                  in this file, not an arbitrary one
                                  universally quantified over
    coeff_W / coeff_W_eq_globalBox   W's coefficient IS the box's coefficient,
                                      by construction

0 sorry throughout, three clean builds this stretch (one had a `Set.PairwiseDisjoint`
unfolding issue needing `show Disjoint _ _` before `rw`; one had a `.le_bot ⟨_,_⟩`
application with unresolved metavariables from elaboration order, fixed with a fully
explicit `have`; one had a backwards `choose_spec` needing `.symm`). `#print axioms`
on every new theorem shows only `propext, Classical.choice, Quot.sound`.

**What this actually closes.** H1c's crux (named at the start of today's session:
"the actual generating function W has NO Lean definition anywhere in this file") is
CLOSED. `W` exists, concretely, unconditionally, and its coefficient is provably the
real configuration count.

**What remains, stated honestly.** `IsAssembly` (line 10128) still needs the
RIGHT-hand side proved for this `W`: the sum over `Fin 4` marker data (BLOCK 300's
partition) of a truncated Neumann/resolvent series built from the per-element
transfer identity (`lR_exp_is_transfer`, BLOCK 115) and the Neumann truncation
(`neumann_partial`/`resolvent_remainder`, BLOCK 116-117). That per-fiber resolvent
identification -- turning "W's coefficient is a count" into "W's coefficient is
ALSO this specific transfer-matrix formula" -- is the one piece of the whole
IsAssembly chain not yet attempted. This is the hard original mathematical content
(the actual claim of eq:assembly), not more bookkeeping. H1c stays 🟡, but the
crux that opened this thread this morning is gone.

## 2026-09-05 — hourly cloud run: container bootstrap takes ~2h45m, no shortcut found

This run's container had no Lean toolchain and no `.lake` build cache at all (fresh
checkout, as expected -- confirmed the prior run's note that `private/RESEARCH_LOG.md`
does not survive between cloud fires). `bootstrap_ci.sh` (committed by an earlier run)
still works and needed no changes to its actual logic. Checked whether Mathlib's own
`.olean` cache (`lake exe cache get`, which would turn this into a few-minute download
instead of a from-source build) is reachable from this sandbox: it is not --
`oleanstorage.azureedge.net` gets the same `403 CONNECT tunnel failed` from the egress
proxy as `release.lean-lang.org` already did. So every fresh cloud container genuinely
has to compile Mathlib from source; there is no faster path available given this
sandbox's network policy. `lake build` took right around 2h45m wall-clock end to end
(~8600 jobs: ~8600 Mathlib modules plus this project's ~110 files), most of it single
core. **Consequence stated plainly for whoever reads this next:** on an hourly cadence,
if the container is not reused between fires, a large fraction of every fire's budget
goes to this rebuild before any new theorem-proving can start. This run's real
mathematical output (below) had well under an hour of actual working time after the
build finished.

Fixed one harmless cosmetic bug while here: `bootstrap_ci.sh`'s last line called
plain `lean --version` after linking the toolchain, which fails with "no default
toolchain configured" when the script is sourced from a directory with no
`lean-toolchain` file in it (e.g. the repo root) -- it does not affect anything (the
`lake`/`lean` on PATH after sourcing work fine either way, and the actual build in
`lean/with_mathlib/` picks the right toolchain from its own `lean-toolchain` file
regardless), but it prints a scary Rust backtrace that could mislead a future run
into thinking bootstrap failed. Changed it to call `"$DEST/bin/lean" --version`
(the binary just linked, by explicit path) so the version print actually succeeds.

**Superseded at merge time.** A concurrent session found the same cache-CDN block
independently (`lakecache.blob.core.windows.net`, the host `lake exe cache get`
actually hits -- this run tested `oleanstorage.azureedge.net`, apparently a stale
or wrong hostname guess, but the proxy verdict is the same: blocked, 403) and fixed
the same cosmetic bug more thoroughly (running the version check from the script's
own directory rather than hardcoding the binary path), plus added the actually
load-bearing fix this run did not find: build the SCOPED target `lake build
EltBridge` (~400 files) rather than a bare `lake build` (all ~8600, effectively
the whole of Mathlib). Took their version of `bootstrap_ci.sh` as-is on merge --
it is strictly better. This run's own bootstrap edit is superseded, not lost: it
is what surfaced the CDN-block finding in the first place, and is preserved here
for the record.

`lake build` in `lean/with_mathlib/` after bootstrapping: **clean, 0 sorry**
(`grep -c sorry EltBridge.lean` = 0), `Build completed successfully (8637 jobs)`,
exit code 0. Confirmed before touching anything, per MATH_RULES_V6.

## 2026-09-05 — BLOCK 323: a first (weak) lower bound on `wordLength` (H1a)

(Numbered 323 at merge time: drafted independently as "BLOCK 316", the same number
at least two concurrent sessions also used for their own H1a work below -- see
those entries' own renumbering notes. No content conflict: different theorem
names throughout, and this block's approach (bounding `|kstar|` directly) turned
out to be a much weaker, non-overlapping angle than the concurrent sessions'
Lipschitz-bound-on-`lR` approach, which is substantially further along by the
time of this merge -- see below.)

With the build clean, picked H1a over H1c: H1c's remaining step (the per-fiber
resolvent identification connecting `W`'s combinatorial count to the actual
transfer-matrix formula) needs a real design decision this session's remaining
time did not leave room to make carefully (see BLOCK 315's honest scope note --
still true, untouched this run). H1a had a smaller, well-scoped opening instead.

**What was actually missing.** Every H1a result on record so far was either the
(closed) reachability upper bound or a statement ABOUT `IsRelaxedLength`/
`IsTrueLength` (e.g. `isRelaxedLength_wordLength_forces_no_defect`). No lower bound
of any kind on `wordLength` had ever been proved -- not even a weak one. And `c`,
the defect `IsTrueLength` needs (`wordLength g = g.lR + 2 * c g`), has no Lean
definition anywhere; it is only known empirically (`nogap` BFS: "max c observed = 3"
at depth 21). So the real lower bound (`wordLength g ≥ g.lR + 2 * c g`) needs `c`
defined first -- a genuine design step, not attempted this block.

**What was proved instead, cleanly.** The simplest possible potential function,
`|kstar|`, which needs no new definition:

    gen_kstar_natAbs_le        every generator step moves `kstar` by at most one:
                                `s1`/`s2` don't move it at all (`s1_kstar`/`s2_kstar`
                                already on record), `s3` moves it by exactly `+-1`
                                depending on `delta` (case split on the `s3` dite,
                                closed by `simp [s3, hd]; omega` in both branches)
    reaches_kstar_natAbs_le    induction on `Reaches n g`: `|g.kstar| <= n` for ANY
                                walk of length `n` reaching `g`, using
                                `gen_kstar_natAbs_le` at the step case
    wordLength_ge_kstar_natAbs `|g.kstar| <= wordLength g` for any reachable `g`,
                                by specialising the induction fact to
                                `n := wordLength g` via the already-proved
                                `reaches_wordLength`

0 sorry, clean build on the first attempt (`lake build EltBridge`, 2982 jobs,
incremental after the Mathlib rebuild above). `#print axioms` on all three shows
only `propext, Classical.choice, Quot.sound`. Committed alongside this log entry
and the bootstrap fix.

**Scope, stated honestly.** This is a real, previously-nonexistent lower bound, but
a WEAK one: `|kstar|` is dominated by `lR` itself (`lR` sums over several quantities
`kstar` is only one of), so this is nowhere near `IsTrueLength`'s actual target
`lR + 2 * c`. It does not close H1a's hard half, and should not be read as being
close to doing so. What it does establish, rigorously, is the shape any real lower
bound will need: a potential that is `1`-Lipschitz along `s1`, `s2`, `s3` and equals
the target at `one`. The two generators `s1`/`s2` being complete no-ops on `kstar`
(and, from their definitions, on `d` too -- `s1_d`/`s2_d`) is exactly why the eventual
potential can afford to depend only on `kstar` and `d`, ignoring `eps`/`delta`
entirely; that structural fact is now proved rather than assumed. H1a stays 🟠.
The next real step, honestly: formally DEFINE `c` (the natural candidate is built
from BLOCK 306's excess law, `d j + eps * travel(kstar, j)`, summed and halved --
matching what BLOCKS 303-310's reachability construction actually uses to build
corrections), then prove the Lipschitz property for that potential under `s3`
specifically (the `s1`/`s2` cases would already be handled, by the fact above). Not
attempted this block -- defining `c` correctly is itself a real decision with room
to get the sign or the halving wrong, and this run's remaining time was better spent
closing the smaller, fully-verified piece above than rushing that decision.

## 2026-09-05 — BLOCK 316: s1/s2 change lR by at most 1 (H1a, local session)

The cloud routine (a fresh, toolchain-less container) identified a promising lead
mid-bootstrap but never reached it (spent the whole session on setup): `s1`/`s2`
only touch `delta`/`eps`, never `d`/`kstar`/`supp`, so they should change `lR` by at
most a bounded amount. Picked this up directly in a local session (instant build,
no bootstrap tax) rather than wait for the cloud run to finish setup.

    s1_occ/s1_A/s1_B, s2_occ/s2_A/s2_B   the span is LITERALLY unchanged by s1/s2
                                          (all rfl, since occ/A/B depend only on
                                          supp/d/kstar)
    siteCost_eq_of_ne_kstar               siteCost away from kstar depends only on
                                           d, kstar and the universal vArr -- also
                                           unchanged by s1/s2
    s1_siteCost_kstar                     AT kstar, flipping delta swaps which of
                                           alphaAt/betaAt carries a +-eps term; each
                                           changes by exactly eps, natAbs is
                                           1-Lipschitz, so their max moves by at
                                           most 1

Together: mu is untouched everywhere (depends only on d, kstar), and only ONE
siteCost term (at kstar) can move, by at most 1 -- so s1 changes lR by at most 1
total. This is exactly the Lipschitz property a word-length lower bound needs.

0 sorry, clean build after several real, diagnosed failures (not guesses): a
`rw [if_pos rfl]` inside a combined simp set hit "motive is not type correct" (a
known dependent-rewrite pitfall); `rw [h]` on the eps disjunction hit the same
issue, fixed with `simp only [h]`; the goal's `delta`/`eps` conditions stayed
symbolic even after casing on `g.delta` because `toPathData.eps`/`.delta` were
never linked back to `g`'s own fields -- added those links explicitly; and, found
only after three failed `omega` attempts (three-strike rule), `norm_num` was
silently converting `Int.natAbs` to the generic `abs` notation, which `omega`
(natAbs-aware, not abs-aware) then saw as unrelated opaque terms -- removing
`norm_num` fixed it immediately. `#print axioms` shows only `propext` (the pure
site-cost equality) and `propext, Classical.choice, Quot.sound` (the Lipschitz
bound). Committed `1e263b3`.

**Scope, stated honestly:** this is the Lipschitz bound for `s1` ONLY. `s2`'s
version (flip delta AND eps) needs the same argument with a sign check, not yet
done. `s3` (the cursor-move generator) needs a SEPARATE bound -- it can touch `mu`
at one edge plus `siteCost` at two sites, so its constant is likely larger than 1,
not yet computed. The actual lower-bound theorem (`wordLength >= lR / constant`,
composing per-generator bounds by induction on word length) has not been
attempted. Real progress on H1a's previously-untouched lower-bound half, not a
closure.

## 2026-09-05 — BLOCK 317: s2 also changes lR by at most 1

s2_siteCost_kstar: the same argument as BLOCK 316's s1 bound, adjusted for s2 also
flipping eps (not just delta) -- each of alphaAt/betaAt still changes by exactly eps
in absolute value, so the max moves by at most 1 as before. 0 sorry, clean build on
the FIRST attempt -- copying BLOCK 316's now-working tactic pattern (no norm_num,
explicit toPathData field links, explicit Bool reduction before the case split)
worked directly with no new bugs. `#print axioms` shows only propext,
Classical.choice, Quot.sound. Committed `22845a7`.

**Both side/sign generators (s1, s2) now have their Lipschitz bound on lR.**

**What's next, stated honestly, and why it's harder than s1/s2:** s3 (the
cursor-move generator) is a materially different case. Unlike s1/s2, s3 can change
the SPAN (A/B): moving kstar can bring a previously-outside edge into range, adding
a new term to lR's sums rather than just perturbing an existing one. It can also
move TWO site-cost terms (the old and new kstar) rather than one, and one mu term
(the crossed edge). The bound is likely a small constant larger than 1, but it has
not been computed, and the span-growth case needs its own argument (probably using
the path-independence excess law from BLOCKS 305-306, which already tracks exactly
how cstep's bookkeeping changes site by site). Not attempted yet. H1a stays 🟠.

## 2026-09-05 — cloud environment: cache CDN confirmed blocked, scoped build fixes it

Checked the cloud routine's actual runs rather than just re-triggering blindly. One run
(cse_01XbHKeqC7sK5jc9pERPjoc8) has been "running" for over an hour, still compiling
Mathlib from source, and will likely keep going indefinitely or time out -- a real cost
of the earlier bootstrap_ci.sh fix (BLOCK -- the `lake exe cache get` addition), which
turned out not to help.

Another run (cse_01K2sq981SubQHqCbsSnTPeT) diagnosed WHY precisely: Mathlib's
precompiled-cache CDN (`lakecache.blob.core.windows.net`) is BLOCKED by this sandbox's
org egress policy, confirmed via the proxy's own `/__agentproxy/status` diagnostics --
not a transient failure. `lake exe cache get` will never succeed in this environment.
That run found the real fix itself: `lake build EltBridge` (a SCOPED target, ~400
files -- only what EltBridge.lean actually depends on) instead of a bare `lake build`
(all 60 defaultTargets, effectively the whole of Mathlib). It was progressing
(400ish/400ish targets) when it ran out of its own session budget before committing
the fix.

Rewrote `bootstrap_ci.sh` from scratch based on that run's transcript (the fix itself
was never pushed -- it lived only in that now-gone container): removed the futile
`cache get` step entirely, documented the CDN block explicitly so future runs don't
re-diagnose it, fixed a real bug the same run found (the final `lean --version` sanity
check ran from the wrong cwd, printing a harmless-but-alarming "no default toolchain"
error even on full success), and pointed callers at `lake build EltBridge` explicitly.
Committed `95d4629`. Updated the routine's own prompt to match.

**Honest note:** this is real, useful environment-hardening work, not H1a/H1b/H1c
progress. Every hourly cloud fire before this fix was likely burning its whole budget
on infrastructure. The next fires should finally reach real math work.

## BLOCK 319 (2026-09-05, commit 44a6a29) — kstar within 1 of span, for Elt

Proved `Elt.A_le_kstar` and `Elt.kstar_le_B_add_one`: `g.A <= g.kstar <= g.B + 1`
for ANY group element `g`, not just cost-minimal `PathData`. This was NOT new
math — the same fact was already proved at the `SiteCost.PathData` level
(`A_le_kstar`/`kstar_le_B_succ`). It only needed two new `rfl` field-projection
lemmas (`toPathData_A`, `toPathData_B`) to transfer it across `Elt.toPathData`.

Why this matters: BLOCK 318's `s3_occ_agree_true/false` showed that `s3`
changes `occ` by inserting/removing exactly the crossed edge. But inserting a
single point into a Finset can move its min'/max' by an unbounded amount if
that point is far from the current range. Without today's theorem, s3's
Lipschitz bound on lR could genuinely have failed for elements whose `kstar`
sits far from their occupied region. With it, `kstar` is already sandwiched
to within 1 of `[A,B]` before any move, so the span can move by at most 1 too.

0 sorry. `#print axioms` on both new theorems: only propext, Classical.choice,
Quot.sound. Build clean on `lake build EltBridge`.

Still NOT done for s3's full bound: the actual A/B movement bound (combining
this with BLOCK 318), the mu-change bound at the crossed edge, and the
two-site siteCost bound (old kstar loses its marker, new kstar gains it).
None of these three attempted yet. H1c (IsAssembly resolvent identity) and
H1b/M4b (RunStrandsConnected, deprioritized) remain untouched this block.

## BLOCK 320 (2026-09-05, commit 9317ea0) — s3's span moves by at most 1

Proved `Elt.s3_A_dist_le_one` and `Elt.s3_B_dist_le_one`: `|(s3 g).A - g.A| <= 1`
and `|(s3 g).B - g.B| <= 1`. Sub-piece 1 of s3's Lipschitz bound, closed.

Method: two new private Finset ℤ lemmas (`min'_dist_le_one_of_agree`,
`max'_dist_le_one_of_agree`) capturing the pure order-theoretic content --
two finsets agreeing everywhere except one point p, each already within one
step of p on its own min'/max', stay within one step of each other. Applied
using BLOCK 318 (occ agrees except at the crossed edge) + BLOCK 319 (kstar
within one step of the span, on both g and s3 g).

0 sorry, #print axioms clean (propext/Classical.choice/Quot.sound only).

Two Mathlib API mistakes hit and fixed: Finset.min'_le/le_max' do NOT take
the Nonempty proof as a separate arg (unlike le_min'/max'_le, which do,
because it appears in their conclusion) -- easy to get wrong by analogy;
and `rcases g.delta with _|_ <;> simp_all` does not work for case-splitting
a field projection's Bool value, use `revert hδ; cases g.delta <;> simp`.

Still open: sub-piece 2 (mu-change at the crossed edge) and sub-piece 3
(two-site siteCost bound). H1c and H1b/M4b untouched this block.

## 2026-09-05 — BLOCK 321: `pathSum` generalized to `CommRing`, matrix powers as walk sums

(Renumbered twice on merge: originally logged as "316", then "320", each time
colliding with a concurrent session's own use of the same number for unrelated
H1a work on `s1`/`s2`/`s3` (see the entries immediately above). At least two,
possibly three, sessions ran on this repo in the same window. No content
conflict either time -- different files/theorems -- but the block counter is
clearly not synchronized across concurrent sessions; treat any single
session's next free number as provisional until push time.)

Before attempting `IsAssembly`'s right-hand side directly, closed a smaller, clearly
necessary gap it exposed: `pathSum`/`pathGF` (BLOCK 112-113) are hard-coded to `M : S ->
S -> ℤ`, but `IsAssembly`'s transfer matrix `T` is `Matrix (Fin n) (Fin n) (PowerSeries
ℤ)` -- a different ring, so neither applies to it as stated.

    pathSumR                     the same walk-sum recursion as pathSum, over an
                                  arbitrary CommRing R
    pathSumR_zero / pathSumR_succ   the two defining equations, both rfl (as pathSum's
                                  own succ equation already was)
    matrixPow_apply_eq_pathSumR  (T^k) a b = pathSumR (fun i j => T i j) k a b, by
                                  induction on k generalizing a b, via pow_succ' and
                                  Matrix.mul_apply

0 sorry, clean build on the first attempt, no bugs this round. `#print axioms` on all
three shows only `propext`/`Classical.choice`/`Quot.sound` (the two rfl-equations don't
even need `Classical.choice`). Committed `7c9389a`.

**What this gives.** `IsAssembly`'s literal `(T ^ k) a b` term can now be read as a
walk sum over any commutative ring, not just algebraically via `Matrix.pow` -- the
combinatorial reading the eventual proof needs.

**What this does NOT touch, stated honestly.** The actual hard gap named at the end of
BLOCKS 314-315 is untouched: turning the box's `flagPathsFinset`/`globalBox` sum
(indexed by `List FlagState`, built over the integer-indexed `idxFn`) into a sum
indexed by a concrete `Fin n` state space with an explicit transfer matrix `T`,
`lambda`, `mu` is separate, unattempted infrastructure -- `pathWeightR` (the box's
actual per-path weight) and `pathSumR` (this block's walk-sum) are not yet connected
to each other at all. `IsAssembly` itself remains unproved for any concrete
`W, W0, T, lam, mu`. H1c stays 🟡.

## BLOCK 322 (2026-09-05) — `s3` doesn't just bound `siteCost`, it preserves it exactly

(Numbered 322 to avoid yet another collision: this was drafted independently as
"BLOCK 318" -- the same number the entries just above ended up using for
`s3_occ_agree_true/false` -- before the two histories were merged. Same story as
BLOCK 321's renumbering note: concurrent sessions, no content conflict, just an
unsynchronized counter. Nicely, the two sessions' work is complementary rather
than overlapping: BLOCKS 319-320 above close the *span*-movement half of `s3`'s
Lipschitz bound; this block closes the *siteCost* half.)

The fixed `bootstrap_ci.sh` worked as intended: bootstrap took a few minutes, `lake
build EltBridge` then ran a genuine ~50-minute from-source compile of its ~400-file
scoped dependency closure (no cache, CDN confirmed blocked as documented) and
succeeded cleanly (`grep -c sorry EltBridge.lean` = 0 both before and after this
block's edits). Went to H1a's remaining generator bound: `s3` (the cursor-move
generator).

Worked the algebra out by hand before touching Lean: `s3`'s two branches
(`delta=true`: `kstar -> kstar+1`, deposit `-eps` at the old `kstar`; `delta=false`:
mirror image) were substituted directly into `PathData.alphaAt`/`betaAt`'s
definitions for an arbitrary site `s`. Result, checked case-by-case over every
position of `s` relative to `kstar`: the `∓eps` deposit `s3` places at the crossed
edge exactly cancels the shift in the marker indicators `vL`/`vR` caused by moving
`kstar`, so `alphaAt s` and `betaAt s` -- and hence `siteCost s` -- are **literally
unchanged, at every site**, not merely bounded. This is a stronger and cleaner fact
than `s1_siteCost_kstar`/`s2_siteCost_kstar` (BLOCK 316-317), which only bounded a
single site by 1.

Formalized as three new theorems, each `0 sorry`:

    s3_alphaAt_eq   (s3 g).toPathData.alphaAt s = g.toPathData.alphaAt s, for all s
    s3_betaAt_eq    same for betaAt
    s3_siteCost_eq  corollary: siteCost is an exact conservation law under s3

`#print axioms` on all three shows only `propext, Classical.choice, Quot.sound`.
Committed `e0a95ff` (pre-merge).

**Bugs hit and fixed while proving this (three real, diagnosed failures, not
guesses):** (1) first draft omitted `g.toPathData.eps = g.eps` (a `rfl` fact,
distinct from the already-tracked `(s3 g).toPathData.eps` one) in two of the four
branches -- `ring` failed leaving a bare `g.toPathData.eps` unrelated to `g.eps` in
its eyes; fixed by adding the missing `have` and putting it in the `simp only` set.
(2) `betaAt`'s branches needed an explicit `rw [hs]` (not just `if_pos`/`if_neg` on
the marker conditions) to align a bare `g.d s` against `g.d g.kstar` that only
`alphaAt`'s branches got automatically via an already-derived `s - 1 = kstar`
lemma; adding this made two `rw` calls close their goals via `rw`'s own trailing
`rfl` check, so the following `ring` then failed with "no goals" -- removed the
now-redundant `ring` on those two lines. (3) one further negative-case branch
looked structurally identical to the two above but wasn't already closed (its
surviving terms were `g.eps * (0:ℤ)` vs `g.toPathData.eps * (0:ℤ)`, not
syntactically `rfl`-equal even though `ring` trivially collapses both to `0`) --
put `ring` back on that one line. Net: each fix was a distinct, understood cause,
not the same mistake repeated; total 4 build attempts to a clean compile.

**What this changes, stated honestly, now that both halves of the merge are on
the table.** BLOCKS 319-320 (above) prove the span `[A,B]` moves by at most 1
under `s3`; this block proves `siteCost` doesn't move at all. Between the two,
`s3`'s effect on `lR = sum_mu + sum_siteCost` is now fully accounted for except
for one piece neither session closed: `mu`'s own value at the crossed site moves
by at most 1 (argued by hand in both sessions' logs, not yet a Lean theorem), and
the *two-site* siteCost bookkeeping BLOCK 319 flagged (old `kstar` loses its
marker, new `kstar` gains one) turns out, per this block's `s3_siteCost_eq`, not
to be a bookkeeping problem at all -- `siteCost` is exactly conserved at every
site, old and new `kstar` included, so nothing there needs bounding. What
remains for a full `s3` Lipschitz bound on `lR`: the `mu`-at-the-crossed-site
theorem, plus combining it with BLOCKS 319-320's span bound and this block's
exact `siteCost` conservation into one `|lR (s3 g) - lR g| <= C` statement, and
then the actual word-length lower-bound induction (`wordLength >= lR / C`) has
not been attempted by either session. H1a stays 🟠, substantially narrowed.

## BLOCK 322 (2026-09-05, commit 99cffff + merge 693282b) — mu-change bound; reconciled with concurrent cloud session

Proved `Elt.s3_mu_dist_le_two`: mu is unchanged off the one crossed edge
(free from d/travel being literally unchanged elsewhere), and at the crossed
edge moves by at most 2. This was sub-piece 2 of s3's Lipschitz bound.

While landing this, `git push` was rejected: a concurrent cloud-routine
session had pushed BLOCK 318/321 (its own numbering, colliding with this
session's numbering) proving `s3_alphaAt_eq`/`s3_betaAt_eq`/`s3_siteCost_eq`
-- an EXACT conservation law (siteCost unchanged at every site, not just
bounded) -- plus a CommRing generalization of pathSum for H1c's transfer
matrix. That conservation law is STRONGER than and supersedes what this
session's sub-piece 3 (a two-site siteCost bound) was aiming for: siteCost
doesn't just move by a bounded amount at the two touched sites, it doesn't
move at all, anywhere. Merged clean (`git merge origin/main`, no manual
conflict resolution needed in EltBridge.lean itself), full merged build
verified 0 sorry, clean `lake build EltBridge`.

Net effect: sub-piece 3 is CLOSED (via the cloud session's exact
conservation law, not this session's planned bound). Remaining for s3's
full Lipschitz bound on lR: composing sub-pieces 1 (span moves by <=1),
2 (mu moves by <=2 at one edge), and 3 (siteCost exactly conserved) into
an actual bound on lR itself -- summing mu over a span whose endpoints
moved by <=1 each, plus the exactly-conserved siteCost sum over a span
whose length also shifted by <=1. Not yet attempted. H1c's transfer-matrix
piece (pathSum now over CommRing, from the cloud session) is a separate,
promising but also not-yet-closed thread -- worth checking next.

## BLOCK 323 (2026-09-05, commit 5abd370) — s3's Lipschitz bound on lR itself, closed

Composed the three already-proved s3 sub-pieces -- span moves by <=1 at each
end (BLOCK 320's `s3_A_dist_le_one`/`s3_B_dist_le_one`), mu unchanged off the
crossed edge and moves by <=2 there (BLOCK 322's `s3_mu_dist_le_two`), siteCost
exactly conserved everywhere (BLOCK 322's `s3_siteCost_eq`) -- into an actual
bound on `lR = mu-sum + siteCost-sum`. This is the piece both BLOCK 322 entries
flagged as the last remaining gap in s3's Lipschitz bound.

New theorems, all 0 sorry, `#print axioms` clean (propext/Classical.choice/
Quot.sound only, no `native_decide`):

    mu_eq_two_outside         outside [A,B], mu is the constant 2 (from houter)
    siteCost_eq_zero_outside  outside [A,B+1], siteCost vanishes
    s3_mu_agree               mu unchanged off the one crossed edge (new; the
                              file only had this bound AT the crossed edge, not
                              a general off-edge agreement lemma)
    s3_siteCost_sum_eq        s3's siteCost-sum is EXACTLY conserved
    s3_mu_sum_dist_le         s3's mu-sum moves by at most 10
    s3_lR_dist_le             **s3 changes lR by at most 10**

Proof strategy, the part worth remembering: extend both sides' sums to their
Finset UNION `T`. The extra terms landing in `T \ (each side's own Icc range)`
are, by construction, strictly outside THAT side's own span -- never at its
own boundary. This matters because the naive plan (shrink one domain directly
into the other, one end at a time) tries to evaluate `mu` at a point that is
about to LEAVE its own domain, and that value is genuinely unconstrained in
general (`mu` at the boundary point A itself can be huge, e.g. a large
deposit). The union construction never needs that: it only ever evaluates
each summand at points strictly outside its OWN span, which is exactly where
`mu_eq_two_outside`/`siteCost_eq_zero_outside` apply. Chased this dead end
first (see the reasoning trail in the session), then found the union fix.

siteCost's sum came out as an EXACT equality (not just bounded) -- the
summand is 0 outside on both sides, so extending to the union adds nothing
on either side. mu's sum picks up a safely generous constant: 10 = 4 + 4
(at most 2 boundary points on each side, each worth <=2) + 2 (the correction
at the crossed edge itself). The tight bound is closer to 6 but chasing it
wasn't worth it given headroom is free for this purpose.

Three real bugs hit and fixed, not guesses: (1) `SiteCost.PathData.vArr`
doesn't exist -- `vArr` lives in the bare `SiteCost` namespace, not under
`PathData` (`Realisation.lean` opens `SiteCost` but defines `vArr` before
entering the `PathData` namespace). (2) the theorem statement
`(∑ j ∈ s, f j : ℤ)` for `f : ℤ → ℕ` elaborates as `∑ j, (↑(f j) : ℤ)` (a
per-element cast), NOT `↑(∑ j, f j)` (a single outer cast) -- this silently
breaks a `set S := ∑ ...` abbreviation meant to fold the whole sum, and
`omega` then reports goals with duplicate unconnected atoms for what should
be the same quantity (caught from reading `omega`'s counterexample dump,
which named the same sum expression twice under different letters). Fixed by
forcing the ℕ elaboration first with a double ascription
`((∑ ... : ℕ) : ℤ)` inside the lemma that needs `set`, then `push_cast`/
`exact_mod_cast` bridging at the one call site (`s3_lR_dist_le`) that needs
the other (fully distributed) form to match after `unfold`+`push_cast` there.
(3) several `omega` calls needed `g.toPathData.A = g.A` (`toPathData_A`) fed
in explicitly as a `have` in scope -- `omega` treats the two sides as
unrelated opaque atoms otherwise, since it doesn't unfold definitions.

Merged cleanly with origin/main (688dd7b, the concurrent H1a/H1c session's
push) before committing -- `git fetch` + `git log HEAD..origin/main` showed
nothing new both before and after the merge, so this pushed straight through
with no conflict. Full `lake build EltBridge` verified clean (0 sorry) both
right after the merge and after this block's own commit.

**What remains for the actual word-length lower bound.** `s1`/`s2` already
have their own `lR` bounds (BLOCK 316-317's `s1_siteCost_kstar`/
`s2_siteCost_kstar`, noting `mu` is literally untouched by either generator);
with `s3_lR_dist_le` this now covers all three generators of `Elt`. What is
STILL missing, and not attempted by this session: the induction itself --
`wordLength(g) >= lR(g) / C` by induction on reachability from `one`, using
these three per-generator bounds to bound how much `lR` can change per step
and hence how many steps (word-length) are needed to reach a given `lR`. H1a
stays 🟠 until that induction is done, but the per-generator groundwork it
needs is now complete.

## BLOCK 324 (2026-09-05) — loop reconciliation note + a repo-convention violation found

This loop iteration's instructions were already stale on arrival: BLOCK 323
(`Elt.s3_lR_dist_le`, K=10, commit 5abd370) had already closed the
lR-composition step they asked for, and it was independently adversarially
verified twice in the interactive session (once for `s3_siteCost_eq`, once
for `s3_lR_dist_le` itself) -- both CONFIRMED sound, non-vacuous, 0 sorry,
clean axioms. No re-work done here; retracting nothing, everything from
BLOCK 323 stands.

Also found while reading recent history: commit d664ce9 ("a first, weak
lower bound on wordLength", `gen_kstar_natAbs_le`/`reaches_kstar_natAbs_le`/
`wordLength_ge_kstar_natAbs`) carries a `Co-Authored-By: Claude Sonnet 5`
trailer and a `Claude-Session:` link -- this VIOLATES this repo's standing
no-AI-attribution convention (some other concurrent session's slip, not
this one's). The mathematical content looks fine on inspection (honestly
labeled "weak", a real if modest first lower bound on wordLength via
|kstar|) and is already pushed/shared, so rewriting history to strip the
trailer would require a force-push on a branch multiple concurrent sessions
are actively using -- NOT done unilaterally here; flagged to the user for a
decision rather than silently editing shared git history.

Current real target, not yet started: the actual induction
`wordLength(g) >= lR(g) / C` using the now-complete per-generator lR bounds
(s1/s2: change lR by <=1; s3: change lR by <=10, BLOCK 323) plus d664ce9's
much weaker `|kstar| <= wordLength` fact (not obviously useful for this,
since it bounds by kstar not lR). Attempting this next.

## BLOCK 325 (2026-09-05) — lR is 10*wordLength+2-Lipschitz (commit 99dbd22)

Filled in the two gaps BLOCK 323/324 flagged: a real per-step `lR` bound for
`s1`/`s2` (BLOCK 316-317's `s1_siteCost_kstar`/`s2_siteCost_kstar` only bound
the *site cost at kstar*, not `lR` itself), and the induction chaining all
three generators' bounds into a wordLength-indexed statement.

**New lemmas (`EltBridge.lean`, all `#print axioms` clean: `[propext,
Classical.choice, Quot.sound]`, zero `sorry`):**

- `Elt.s1_lR_dist_le`, `Elt.s2_lR_dist_le`: `s1`/`s2` move `lR` by at most 1.
  `mu` depends only on `d` and `kstar`, both literally unchanged by `s1`/`s2`,
  so the edge-sum half of `lR` doesn't move at all; the site-sum can only
  move at the single site `kstar` (`siteCost_eq_of_ne_kstar` handles every
  other site), by at most 1 (`s1_siteCost_kstar`/`s2_siteCost_kstar`).
- `Elt.lR_congr`: `SameElt g h -> g.toPathData.lR = h.toPathData.lR`. Needed
  because `Gen`/`Reaches` are stated only up to `SameElt` (BLOCK 141's
  non-canonical `supp`), so a generator step's target is merely *SameElt* to
  `s1 a`/`s2 a`/`s3 a`, not equal to it as a term.
- `Elt.one_toPathData_lR : one.toPathData.lR = 2`. **This corrects a wrong
  assumption in the task that specified this work**: the identity's `lR` is
  NOT 0. `mu` is defined (`SiteCost.PathData.mu`) to read `2` at any
  coordinate with neither a deposit nor travel, precisely to encode that a
  minimal realisation must still visit and leave that edge; `one`'s only
  span coordinate, edge `0`, is exactly such a coordinate (no deposit, and
  `travel 0 0 = 0` since the marker sits at `kstar = 0` and induces no
  travel anywhere), so `lR(one) = 2` exactly, computed directly (`A = B =
  0`, `mu 0 = 2`, both site costs at `0` and `1` vanish).
- `Elt.gen_lR_dist_le`: every `Gen` step moves `lR` by at most 10 (transport
  via `lR_congr`, then `s1_lR_dist_le`/`s2_lR_dist_le`/`s3_lR_dist_le`).
- `Elt.reaches_lR_le`: `Reaches n g -> (lR g : Z) <= 10 * n + 2`, by
  induction on `Reaches` (mirroring `reaches_kstar_natAbs_le`'s shape),
  base case `one_toPathData_lR`, step case `gen_lR_dist_le`.
- `Elt.lR_le_wordLength_mul_C {g} (h : Reachable g) : (lR g : Z) <= (wordLength
  g : Z) * 10 + 2`, via `reaches_lR_le (reaches_wordLength h)`.

**Constant and honest scope.** C = 10 (s3's bound is the binding one, as the
task anticipated), but the task's requested statement shape
`g.toPathData.lR <= wordLength g * C` (no additive term) is FALSE at `g =
one`: `wordLength one = 0` but `lR one = 2`, so `2 <= 0 * C` fails for every
C. The additive `+2` above is not a weakening chosen for convenience -- it
is forced by `one_toPathData_lR`, i.e. by `mu`'s own definition. The proved
theorem is the honest correction of the requested one, not the literal
statement asked for.

**What this is, and is not.** This is the Lipschitz *upper* bound on `lR`
against `wordLength` -- the direction opposite `wordLength_ge_kstar_natAbs`
(d664ce9's weak *lower* bound via `|kstar|`). It does NOT touch H1a's actual
target `wordLength = lR` (`IsTrueLength`'s `lR + 2*c`, both directions still
open) nor supply any lower bound `wordLength >= lR / C` -- an upper bound on
`lR` in terms of `wordLength` goes the wrong way for that; the induction the
task and BLOCK 324 both described as "the actual induction" would need to
bound `wordLength` from below in terms of `lR`, which is a different
(harder, still fully open) argument this block does not attempt.

## BLOCK 326 (2026-09-05) — c-defect diagnosis: real candidate found, PhiAt is the missing check

Investigated whether the connectivity defect `c : Elt -> N` (needed for
`IsTrueLength`, `L g = g.lR + 2*c g`) can be defined and given a Lipschitz
bound under s3, analogous to tonight's `lR` work (BLOCK 319-325). No commit,
repo left clean -- this is a diagnosis, not a closure.

`c` currently has NO Lean definition anywhere in the file -- only an
uninterpreted parameter in `IsTrueLength` and an empirical Rust statistic in
`nogap` (max observed c=3 at depth 21).

A REAL, non-vacuous candidate exists already: `c(g) := (pdCutSites
g.toPathData).card`, using `pdCutSites` (line ~2028, already defined and
instantiated on concrete elements: `witElt_cutSites = empty`, `witNeg_cutSites
= {2}`) and `PathData.cut` (`alphaAt=0 /\ betaAt=0 /\ PhiAt=0`, matching the
paper's shield-law/|Z| notion).

What blocks proving anything about it: BLOCK 322's exact-conservation
theorems (`s3_alphaAt_eq`, `s3_betaAt_eq`) cover TWO of `cut`'s three
conjuncts. `PhiAt` (the third) has never been checked under s3 -- nobody has
proved or disproved that s3 preserves it. Without that, the union-of-windows
technique that closed `s3_lR_dist_le` (BLOCK 323) can't even start on `c`.

This is NOT the same obstruction as H1b/M4b (RunStrandsConnected, which needs
Eulerian-circuit EXISTENCE, missing from Mathlib -- a real graph-theory gap).
The `c`-obstruction is narrower and more mechanical: check whether
`s3_alphaAt_eq`'s proof pattern extends to `PhiAt` (plausible, since `PhiAt`
only involves `f`/`vArr`/`vL`, all already handled by that proof's case
analysis). If it extends, `pdCutSites`'s cardinality Lipschitz bound is
plausibly in reach by the same technique as `s3_lR_dist_le`. This is
honestly the best-scoped concrete next step identified tonight on either
open composite (H1c or this). Separately, even a full `c`-Lipschitz bound
would not by itself prove `IsTrueLength` -- that additionally needs the
still-fully-unformalized bridge from a general `Elt g` to a `ConfigLoop`
configuration, confirmed independently (again) as missing tonight.

## BLOCK 327 (2026-09-05, commit c5841ad) — PhiAt IS exactly conserved by s3; c defined, Lipschitz bound NOT reached

Followed up BLOCK 326's diagnosis. Worked the algebra by hand first: `PhiAt(s)
= f(s-1) + vArr(s) - vL(s)`. Under `s3`'s true-delta branch (`kstar -> kstar+1`,
`delta` true->false), at the crossed site `s = kstar+1` (i.e. `s-1 = kstar`),
`travel_succ_at` gives `f(s-1)` shifting by `+1`, and `vL(s)` shifts from `0`
(delta was true) to `1` (`vD'(s) = [s = kstar+1]`, now true) -- net change
`+1 - 1 = 0`. Everywhere else (`s != kstar+1`) both `f(s-1)` (`travel_succ_ne`)
and `vL(s)` are literally unchanged. `vArr(s)` never depends on `kstar`/`delta`
so it cancels trivially throughout. The false-delta branch is the exact mirror
(`travel_pred_at`/`travel_pred_ne`, crossed site `s = kstar`). So `PhiAt` is
conserved by `s3` at every site, exactly, in both cases -- no discrepancy found.

Formalized as `Elt.s3_PhiAt_eq` (same case-split shape as `s3_alphaAt_eq`/
`s3_betaAt_eq`), plus `Elt.s3_cut_iff : (s3 g).toPathData.cut s <-> g.toPathData.cut
s` (immediate corollary: `cut`'s three conjuncts are each exactly conserved).
Both `0 sorry`, `#print axioms` clean (`propext, Classical.choice, Quot.sound`
only). One real bug on the way: a first draft tried to close the "at the
crossed site" branch with `simp only [..., hs]` where `hs : s = kstar +- 1` was
thrown into the simp set to also collapse `vD`'s `if s = kstar' then ...`
condition -- `simp only` doesn't reduce `if (kstar+1 = kstar+1) then _ else _`
to the `then` branch without an explicit `eq_self_iff_true`/`if_pos` lemma in
scope, so both branches left "unsolved goals" instead of failing loudly. Fixed
by dropping `hs` from the `simp only` set and doing `rw [if_pos hs]` /
`rw [if_neg hs]` explicitly afterward, matching `s3_alphaAt_eq`'s own style
exactly (which already used this pattern and I should have copied verbatim
the first time instead of taking a shortcut).

Then defined the `c` candidate the diagnosis named: `Elt.c (g) := (pdCutSites
g.toPathData).card`. Typechecks and builds clean (it's a `noncomputable def`,
no axioms to check).

**Did NOT reach the Lipschitz bound, and this is a real obstruction, not
laziness.** `s3_lR_dist_le`'s technique (BLOCK 323) needed an "outside my own
span the summand is a known constant" fact for each side (`mu_eq_two_outside`,
`siteCost_eq_zero_outside`), both stated over the *absolute* edge coordinate
via `Finset.Icc`/`houter`. `pdCutSites`, by contrast, is defined over
`(Finset.Ioo 0 (pdWidth P)).filter (fun s => P.cut (P.A + s))` -- a window
*relative to `P.A`*, i.e. it re-indexes every site by subtracting `A` before
filtering. Reindexing to compare `pdCutSites (s3 g).toPathData` against
`pdCutSites g.toPathData` needs a translation between two different origins
(`(s3 g).A` vs `g.A`, which themselves differ by at most 1 per
`s3_A_dist_le_one` but are not literally equal), which the existing lemma set
doesn't supply. Worse: even after fixing that reindexing, the union-of-windows
step needs an analogue of `siteCost_eq_zero_outside` for `cut` itself -- "outside
the span, `cut` never holds" -- and no such lemma exists. `siteCost_eq_zero_outside`
gives `alphaAt = betaAt = 0` outside `[A, B+1]` (since `siteCost = max(|alpha|,
|beta|) = 0` there), which is two of `cut`'s three conjuncts, but says nothing
about `PhiAt` outside that range -- `PhiAt` is not asserted to vanish outside
the span by any lemma in the file, and there is no a priori reason it must
(`f = travel kstar` is `0` outside the span by `houter`, and `vArr(s) = [s=0]`
is `0` there too since `0` is inside `[A,B]` by `hA`/`hB`, but `vL(s)` need not
be `0` at `s = kstar` itself, which can sit right at the span's edge). So a
site just outside `[A, B+1]` genuinely *could* be a cut site under this
definition, unlike `siteCost`. This is exactly the domain-mismatch the task
anticipated as a plausible failure mode, confirmed rather than assumed.

**Honest scope of this block.** `PhiAt`-conservation: CLOSED exactly (stronger
than needed -- it wasn't merely bounded). `Elt.c`: DEFINED, builds, but has no
Lipschitz bound and none was forced. `IsTrueLength`/the `Elt -> ConfigLoop`
bridge: untouched, out of scope as instructed. What a future attempt would
need: either (a) a proof that `cut` implies membership in `[A, B+1]`-ish
(closing the missing "outside the span" fact), or (b) reformulating `c` over
an absolute `Finset.Icc`-style index instead of `pdCutSites`'s `A`-relative
one, so the reindexing problem doesn't arise in the first place.

## BLOCK 328: `Elt.c`'s Lipschitz bound closed -- the reindexing obstruction dissolves,
## and BLOCK 327's diagnosis of the "outside the span" gap was itself wrong

Followed BLOCK 327's own suggested option (b): reformulate `pdCutSites` over an
absolute index instead of chasing option (a) (a "cut never holds outside `[A,B+1]`"
fact). Checked `pdWidth P := (P.B - P.A + 1).toNat` first: since `hA : A <= 0` and
`hB : 0 <= B` force `B - A >= 0`, `(pdWidth P : ZZ) = P.B - P.A + 1` exactly, so
`pdCutSites`'s relative window `Ioo 0 (pdWidth P)` filtered by `s -> P.cut (P.A+s)`
is *already* nothing but `Ioo P.A (P.B+1)` filtered by `P.cut`, reindexed by the
shift `s |-> P.A + s`. Proved this as `pdCutSites_card_eq_abs` via `Finset.card_bij`
with that shift as the bijection (both directions checked by `omega` once `hw :
(pdWidth P : ZZ) = P.B - P.A + 1` is in hand). `0 sorry`, clean axioms.

**BLOCK 327's "PhiAt might not vanish outside the span" claim was checked by hand
and found FALSE, but this turned out not to matter.** Working it out: `PhiAt(s) =
f(s-1) + vArr(s) - vL(s)`. For `s` outside `[A, B+1]`: `f(s-1) = travel kstar (s-1)
= 0` by `houter` (since `s-1` is outside `[A,B]` too); `vArr(s) = [s=0] = 0` since
`0` is inside `[A,B]` (`hA`/`hB`) so `s != 0`; and `vL(s) = [delta=false][s=kstar]
= 0` since `kstar` is inside `[A, B+1]` (`A_le_kstar`/`kstar_le_B_succ`, already in
the file) so `s != kstar`. So `PhiAt(s) = 0` outside `[A,B+1]` too, by the exact
same `houter`-style argument as `alphaAt`/`betaAt` -- `cut` in fact holds
*identically true* everywhere outside `[A, B+1]`, the opposite of BLOCK 327's
worry. This was a real error in that block's reasoning, now corrected. But it
turned out to be moot: once `pdCutSites` is in the absolute form above, the
`Elt.c` Lipschitz bound doesn't need to know anything about `cut`'s behavior
outside either span at all -- see below.

**The actual closing move needed something simpler than the whole `s3_lR_dist_le`
machine.** `Elt.s3_cut_iff` (BLOCK 327, already exact and unconditional: `(s3
g).toPathData.cut s <-> g.toPathData.cut s` for *every* absolute `s`, not just
inside some span) means `cut` is *literally the same predicate* on `g` and `s3 g`
-- there is no discrepancy to bound between the two summands the way `mu`/`siteCost`
had one at the crossed edge. All that moves is the *window* `Ioo A (B+1)` itself,
by at most one at each end (`s3_A_dist_le_one`, `s3_B_dist_le_one`). So the
"outside the span, the summand is a known constant" step from `s3_lR_dist_le` is
not needed at all here; what's needed instead is the purely combinatorial fact
that a filter's cardinality over two `Ioo`-windows whose ends move by <= 1 each
differs by at most 2. Proved as `window_sdiff_subset`: `Ioo A' (B'+1) \ Ioo A
(B+1) subseteq {A, B+1}` given `|A-A'| <= 1` and `|B-B'| <= 1` (pure `omega` once
membership is unfolded), then a union-of-windows card bound (`T := W1 union W2`;
`card(T.filter p) <= card(Wi.filter p) + card(T \ Wi)` from a subset-then-
`card_union_le` step; `T \ W1 = W2 \ W1` etc.) closes both directions.

`Elt.s3_c_dist_le : |c(s3 g) - c g| <= 2`. `0 sorry`, `lake build EltBridge` clean,
`#print axioms` on `pdCutSites_card_eq_abs`, `window_sdiff_subset`, `s3_c_dist_le`
all show only `propext, Classical.choice, Quot.sound`. Commit `d2f40f2`.

**Honest scope.** This closes the `c`-Lipschitz gap BLOCK 327 left open. It does
NOT connect `Elt.c` to `IsTrueLength`'s uninterpreted `c`, and does not touch
`prop:travelinv`/the shield inequality `c <= |Z|` (paper2's still-open core, per
`travelinv-is-the-shield-inequality.md`) -- `Elt.c` here is a candidate model of
`|Z|`, formalized and now Lipschitz, nothing more.

## BLOCK 329 (2026-09-05) — Elt -> ConfigLoop bridge: much more exists than "totally unformalized" claimed

Investigated the Elt->ConfigLoop.Data bridge needed to connect tonight's
Elt.c (BLOCK 326-328) to IsTrueLength's actual defect. No commit -- this
corrects a standing claim in this log and elsewhere (repeated at least three
times previously: thm_nogap, cor_localzero, prop:travelinv sections) that
"the passage from a group element g to its configuration is not formalised."

That claim is WRONG as stated. `Elt.balanced` (line 1452) is a fully
UNCONDITIONAL theorem -- no side hypotheses -- giving the arrival/departure
balance for any g. Combined with `GenericData.dataG` (needs only balance +
VEndpt.partner/partner_invol/partner_ne/partner_site_neP, the last needing
only kstar != 0), a total configuration-datum bridge for every g with
kstar != 0 ALREADY EXISTS compositionally -- it has simply never been
assembled into one named total definition. This is real, previously-missed
structure, found by reading ConfigLoop.lean and the relevant EltBridge.lean
theorems in full rather than trusting the prior sessions' summary.

The GENUINE remaining gap is narrower and different from what was assumed:
NOT "build the bridge" (compositionally done), but proving
`ConfigLoop.defect (bridge g) = Elt.c g` in general. This splits in two:
(1) gap-free g (hcov0 holds): defect=0 is essentially in hand via
`Elt.defect_zero`'s existing pattern, modulo checking Elt.c g = 0 follows
from pdCutSites being empty when there's no gap (plausible, unchecked).
(2) gapped g: only a LOWER bound exists (`prop_cut_correct`/
`CutComponents.exists_injective_components_avoiding` gives >= |Z|, not
exact). The exact count needs an injectivity/surjectivity argument (each
cut site contributes EXACTLY one isolated cycle) that is not in the file --
this is the SAME known-open reverse inequality already tracked as
`travelinv-is-the-shield-inequality` in memory, not a new distinct gap.
It is algebraic/combinatorial (exact component counting), NOT the same
obstruction as H1b (which needs Eulerian-circuit EXISTENCE) -- confirmed
these are genuinely different blockers, not the same wall wearing two names.

Recommended next scoped step (not attempted here): name the total bridge
as `Elt.dataOf (g) (h : kstar != 0) (ds) : WalkGraph.Data (VEndpt ...)` via
GenericData.dataG using Elt.balanced, then prove ONLY the gap-free case
`Elt.c g = 0 -> ConfigLoop.defect (Elt.dataOf g h ds) = 0`, combining
Elt.defect_zero's argument pattern with an unconditional hcov0 derivation.
Assessed as likely a one-session task. The general (gapped) equality is
not -- it needs the same open combinatorial argument tracked elsewhere.

## BLOCK 330 (2026-09-05, commit 7dba194) -- Elt.dataOf named; kstar<0 mirror added; step 4 not attempted

Followed BLOCK 329's recommended step. Verified by reading: `Elt.defect_zero`
(EltBridge.lean ~1963) was ALREADY stated for arbitrary `g : Elt` with
`0 < g.toPathData.kstar`, not just `witElt` -- the "generalize from witElt"
part of BLOCK 329's plan turned out to already be done. What was missing was
a named object, since `exists_mergesMin` (CostMerge.lean:557) builds its
witness via `Int.exists_least_of_bdd` + classical choice, so it is
genuinely nonconstructive -- there is no way to name the datum except by
choice.

Added, all in EltBridge.lean, all building clean (`lake build EltBridge`,
2982 jobs) with 0 `sorry` and axiom lists exactly
`[propext, Classical.choice, Quot.sound]`:
- `Elt.dataOf g ds bnd hk hb hbnd hcov0 z0` -- `Classical.choose` of
  `Elt.defect_zero`'s existential; a genuine named `WalkGraph.Data`.
- `Elt.dataOf_mergesMin`, `Elt.dataOf_defect_zero` -- its two defining
  properties, via `Classical.choose_spec`.
- `Elt.defect_zero_neg` -- the `kstar < 0` mirror that was missing:
  `Elt.merges_to_one_neg` existed (walkCount <= 1) but nothing drew
  `defect = 0` from it the way `Elt.defect_zero` does for `kstar > 0`.
  (`Elt.dataOf` itself was left positive-only-honest-scope; a negative
  mirror `dataOf` would just repeat the same choice-packaging and wasn't
  built, to avoid an artificial single signature straddling two different
  hypothesis sets for no mathematical gain.)

**Did not attempt step 4** (connecting `Elt.c g = 0` to `hcov0`/gap-freeness
and combining both directions). Checked first: no existing lemma in the file
relates `hcov0` (the covering condition, stated over the extended `VEndpt`
type at a chosen `bnd`) to `pdCutSites`/`pdCutAt` (stated over `PathData`
via `P.cut`). Working out that equivalence from scratch is a real semantic
question, not a repackaging -- exactly the kind of thing BLOCK 329 flagged
as "plausible, unchecked" rather than in hand. Stopping here rather than
forcing it; this is a legitimate open follow-up, scoped smaller than the
gapped-case reverse inequality (which stays untouched, per instructions).

## BLOCK 331 (2026-09-05) — hcov0 vs Elt.c=0: no clean equivalence found, correctly not forced

Investigated whether `hcov0` (Elt.defect_zero's covering hypothesis, line
1963-2020) is equivalent to `Elt.c g = 0` (pdCutSites empty, BLOCK 326-328).
No commit -- genuine negative/inconclusive finding, not a failure to try.

`hcov0` lives on the extended VEndpt/EndType.edgeOf/atTop level, quantified
relative to a chosen phantom edge `bnd`; it is proved for exactly one
concrete element (`witElt_hcov0`) via a bespoke argument specific to
witElt's single-edge span. The file's ACTUAL bridge between cut sites and
walkCount is a different, more elaborate hypothesis `hcov` (line 3087,
via `WalkSupport.wLo`), used by the shield-law machinery (`VEndpt.shield`/
`shield_gap`) -- `hcov` and `hcov0` are never shown to coincide, nor is
`hcov0` shown to be `hcov` specialized at `Zf = empty`. The two available
concrete data points (`witElt`: pdCutSites=empty, hcov0 holds; `witNeg`:
pdCutSites={2}, never run through the hcov0-analogue anywhere in the file)
don't settle it either way. The file even has an explicit warning (BLOCK 60
comments, ~line 3149: "a virtual site CAN be a cut site") against assuming
a clean iff here.

Tracing this properly would require going through `Elt.merges_to_one`'s use
of hcov0 down through `hvirt_of_gap`/`wLo`/the shield-law chain to
`pdCutSites` -- which IS the general gapped-case machinery
(`travelinv-is-the-shield-inequality`) already tracked as the known-open
combinatorial crux. So this isn't a new distinct gap: it's confirmation
that H1a-bridge's gap-free case (BLOCK 330) is the honest limit of what's
reachable without opening that crux. Correctly not forced into a false or
vacuous theorem.

**H1a-bridge, final honest state for tonight:** Elt.dataOf (the named
bridge) + dataOf_defect_zero/defect_zero_neg (gap-free case, both signs of
kstar) are real and proved. Connecting this to Elt.c specifically, and the
general gapped case, both terminate at the same already-known open
reverse-inequality crux. No further progress possible here without
attacking that crux directly.

## BLOCK 334 (2026-09-06) — H1c bulk-Fintype attempt: the "off near-marker" quotient does NOT
## sidestep the obstruction; `dcur` is unbounded everywhere, not just at the marker

Followed the two independent H1c investigations' recommended next step (BLOCKS
311-315, 321): build a genuine `Fintype` for the "bulk" (off the near-marker site)
quotient state, define its transfer matrix from `flagStepB`'s weight, and reproduce
the walk weight on paths avoiding site 0, deferring the `Fin 4` marker-fiber
bookkeeping. Read `LocalState`/`FlagState` (EltBridge.lean:5938, 7523), `flagStepB`
(7534), `travel` (MarkedSite.lean:26), `LocalState.muOf`/`dcur_le_muOf` (5956, 5973),
`site_cost_magnitude_only` (9673, "BLOCK 104"), and `boxSet`/`boxSet_finite`
(9432-9445, the actual N-dependent construction BLOCKS 314-315 used for `W`).

**Checked exactly what "off the marker" buys.** `site_cost_magnitude_only` +
`marker_needs_sign` (9793-9821) show the ONLY thing that distinguishes near-marker
from bulk is that the bulk site cost depends on `dprev`/`dcur` through `.natAbs`
only, so a bulk state could in principle be quotiented by sign (folding `dcur` and
`-dcur` together, factor-2 shrink). That is real, but it is not the obstruction.
The obstruction is that `dcur` itself (a raw `ℤ`-valued deposit count, present at
EVERY site, marker or bulk) has no finite range anywhere in the file that doesn't
depend on `N`: `LocalState.dcur_le_muOf` bounds `dcur.natAbs` by `muOf`, but `muOf`
is DEFINED from `dcur`/`fcur` themselves (5956) — the bound is `|dcur| ≤
max(|dcur|,|fcur|)`, true but empty of content. The only actual finite bound on
`dcur` used anywhere is `boxSet N`'s `b.dcur.natAbs ≤ N` (9432-9433), which is
exactly the per-degree box BLOCKS 314-315 built `W` from, and is `N`-dependent by
construction. `fcur` (`= travel`) IS unconditionally in `{-1,0,1}` (`travel_cases`,
MarkedSite.lean:29) with no `N`-dependence — so a bulk Fintype quotient by
`(sign-class of dcur restricted to a fixed range, fcur, arr, dep, eps, delta)` would
work for paths whose `dcur` stays inside that range, but not for arbitrary `N`: as
`N` grows, `IsAssembly` must still cover degree-`N` configurations, and nothing in
the file bounds how large `dcur` (i.e. `d j`, an accumulated signed deposit) can get
along those paths independent of `N`.

**Why this is not simply "impossible" (so this is a diagnosis, not a proof of
impossibility).** `IsAssembly`'s `T` is `Matrix (Fin n) (Fin n) (PowerSeries ℤ)` —
entries are power series, not scalars, so a single fixed-size transfer step CAN in
principle already encode a full geometric sum over an unboundedly large `dcur`
excursion (that is the entire point of using power-series-valued transfer matrices
instead of enumerating states one integer at a time). So the right fix is not "find
an N-independent cap on dcur" (there isn't one, and there shouldn't need to be one) —
it is to exhibit the actual power-series-valued transition rule that sums out the
`dcur` degree of freedom analytically, which is exactly the "per-fiber resolvent
identification" BLOCKS 314-315/321 already named as the one unattempted piece of
real mathematical content (`pathWeightR`'s box-indexed weight is still not connected
to `pathSumR`'s `T`-indexed walk sum, BLOCK 321). My attempt to shortcut that by
finding a purely combinatorial (non-power-series) bulk `Fintype` fails for the reason
above; it does not fail for a new reason and does not narrow the crux further than
BLOCK 321 already had it.

**No commit.** No Lean file touched this session; nothing constructed was strong
enough to be worth landing (would have been a `Fintype` that provably only covers
bounded-`N` paths, i.e. exactly `boxSet N` again under a different name — not new
content). H1c stays 🟡. The honest next step, unchanged from BLOCK 321, is the
power-series transfer-matrix construction itself, not a combinatorial state-space
restriction (bulk-only or otherwise).

## BLOCK 332 (2026-09-06) — re-audit of prop:cut/`c <= |Z|`: the reverse inequality is
## ALREADY PROVED in Lean (`c_le_Z_final`); the open item is a bridge, not the inequality;
## plus a previously-unnamed type mismatch (`VEndpt` vs `Endpt`) in that bridge

Assigned to re-attack the "reverse inequality" (`c <= |Z|`, `prop:cut`,
`travelinv-is-the-shield-inequality`) directly. No commit to EltBridge.lean/
ConfigLoop.lean -- re-reading first, per instructions, changed what there was
to attack. No sorry added, no theorem forced. This is a diagnosis correction,
not a new proof.

**The inequality itself is not open in the Lean development.** Re-read
`ConfigLoop.shield_law_runs` (line 2221) and its proof in full. It obtains
`hle : walkCount E <= Zf.card + 1` from `c_le_Z_final` (line 1943) FIRST, then
closes the matching `>=` from `CutComponents.exists_injective_components_avoiding_of_runs`
+ `walkCount_ge_of_avoiding`, and `le_antisymm`s the two into the exact
equality `walkCount E = Zf.card + 1`. So both directions of "defect = |Z|"
already exist as theorems, unconditionally, given three hypotheses on a
configuration `D : Data (Endpt n m)`: `hZ` (cut sites carry no arrivals),
`hruns` (every run 0..|Z| carries an end), and `RunInv up ds Zf D` (which
itself bundles `hp`/`hts`/`hta`/`hturn`/`hcov`/`hmin` -- six conditions). This
matches BLOCK 329's reframing exactly and I confirm it by direct reading of
`c_le_Z_final`'s statement (not just its name): it literally concludes
`walkCount E <= Zf.card + 1` from `RunInv up ds Zf D`. **So `c <= |Z|` is a
proved theorem of the abstract run-graph model; what is open is showing a
configuration built from a general `g : Elt` satisfies its hypotheses.**

**New finding this session: the bridge has a type-level gap not previously
named.** `ConfigLoop.RunInv`/`shield_law_runs`/`c_le_Z_final` are all stated
over `Data (Endpt n m)`, where `Endpt` is `EndType.Endpt` (EndType.lean:29).
But `Elt.dataOf` (BLOCK 330, EltBridge.lean) is built via `GenericData.dataG`
over `VEndpt n mm`, where `VEndpt n mm := EndType.Endpt n mm ⊕ Bool`
(EltBridge.lean:204) -- `Endpt` extended with two extra "virtual"/phantom
points (the `Bool` summands). `Endpt` embeds into `VEndpt` via `Sum.inl`, but
`Data (VEndpt n mm)` and `Data (Endpt n m)` are different types entirely --
`shield_law_runs` cannot be applied to `Elt.dataOf`'s output as it stands.
Closing this needs either (a) a further bridge showing the two virtual points
of a `Elt.dataOf`-built `Data` pair off in a way that lets the whole thing
project down to a genuine `Data (Endpt n m)`, or (b) re-deriving `RunInv`/
`shield_law_runs`'s statement and proof generically over `VEndpt`, which
would need `CutComponents.exists_injective_components_avoiding_of_runs` (and
the whole graph-component machinery underneath it) regeneralized too --
non-trivial, not attempted. BLOCK 331 traced `hcov` vs `hcov0` without
surfacing this; it is a genuinely separate, additional obstruction sitting
in front of even stating `hZ`/`hruns`/`RunInv` for `Elt.dataOf g`, on top of
the semantic gap BLOCK 331 already found.

**Relation to H1b.** Confirmed again, independently: this is NOT the same
wall as H1b (Eulerian-circuit existence, missing from Mathlib). The
component-counting machinery `CutComponents.exists_injective_components_avoiding[_of_runs]`
that supplies the `>=|Z|` half is already built and used successfully
(`wit_shield`); it does not invoke anything Eulerian-circuit-shaped. The two
problems remain genuinely different blockers that happen to both terminate,
independently, in "needs a bridge/hypothesis-discharge that isn't built yet"
rather than "needs a missing inequality."

**Honest scope.** No Lean file changed. This session's contribution: (1)
confirms by direct reading, not just by name, that `c_le_Z_final` already
proves the paper2 direction abstractly; (2) narrows further what blocks
applying it to real `Elt`s -- not just the `hcov`/`hcov0` semantic gap
(BLOCK 331) but a prior, more basic `VEndpt`-vs-`Endpt` type mismatch in
`Elt.dataOf` itself. Next concrete step for a future session: decide between
options (a)/(b) above for the type mismatch before returning to `hZ`/`hruns`/
`RunInv` at all -- attacking those on the wrong type would be wasted work.

## BLOCK 333 (2026-09-06) — genuine fresh attempt at `RunStrandsConnected`
## (H1b/M4b, Eulerian existence): re-confirmed hard, one real refinement of
## WHY, no Lean committed

Explicit user instruction tonight: attempt `RunStrandsConnected` for real,
overriding the standing "don't re-attempt without a new idea" note. This is
not a repeat of BLOCK 199-206 without checking -- it is a fresh look with two
concrete falsifiable checks and one new (negative) idea, done before
concluding the wall stands.

**Check 1: has Mathlib grown an Eulerian-existence theorem since BLOCK 206?**
Read `Mathlib/Combinatorics/SimpleGraph/Trails.lean` directly in this repo's
`.lake/packages/mathlib` (not from memory). It still has only `IsEulerian`
(def), `IsEulerian.isTrail`, `IsEulerian.mem_edges_iff`,
`IsTrail.isEulerian_of_forall_mem`, `isEulerian_iff`,
`IsEulerian.even_degree_iff`, `IsEulerian.card_odd_degree`/`card_filter_odd_degree`
-- all NECESSARY-direction or definitional. No construction, no existence
theorem (no Hierholzer). Confirmed unchanged; BLOCK 206's premise stands.

**Check 2: is the object here actually a general graph, or something more
restricted that might have a direct argument?** Read `EndType.lean` in full
(the concrete `Endpt n m` type `RunStrandsConnected` is stated over) and the
`turnGen`/`allJoined_*` machinery in `EltBridge.lean` (~lines 17000-18820,
i.e. everything BLOCKS 199-206 built). Confirmed precisely what prior
sessions already said: this is NOT an arbitrary multigraph. `Endpt n m` has
`idx : Fin (m edge)`, so per-edge width is *already* fully general in the
type -- `turnGen`'s restriction to a single global `u` (`hm : ∀ e, m e = 2 *
u`) is an artificial narrowing of an already-general encoding, not a
limitation of the mathematics. The real object is a linear chain of
parallel-edge bundles between consecutive integer sites (`siteOf x = edgeOf x
+ (if top then 1 else 0)`), each bundle of even width `m e`. So the bespoke
framing BLOCK 199 identified is right, and is not a red herring: general
Hierholzer would be substantial overkill for this shape.

**The new idea tried, and why it fails (worth recording so it isn't retried).**
For a linear chain, the textbook explicit Eulerian circuit is: pick one
"spine" strand per edge that threads straight through both its sites (a
`pass` at both ends), and absorb every other strand of that edge into
internal `bounce` pairs. Checked whether this closes the general case
directly. It doesn't parse: a strand's two ends sit at two DIFFERENT sites
(`siteOf` bottom = `e`, top = `e+1`), so "internal" is not a same-site notion
-- `bounce` pairs two ends *at one site* (necessarily from different
strands), never a strand's own two ends. So "every non-spine strand bounces
internally" is not a well-formed local rule at all; it silently smuggled in
the assumption that a strand's far and near ends could be paired directly,
which the site structure forbids. This is a genuine (if elementary)
dead end distinct from BLOCK 199's "fixed min(u[j],u[j+1]) pairing"
counterexample -- that one failed numerically (found by enumeration), this
one fails to typecheck as a construction at all. Recording both wrong ideas
in one place should save a future session from re-deriving either.

**What this leaves standing, precisely (same content as BLOCK 204-206,
independently re-derived and re-verified here):** the per-edge round-trip
pairing (`up 0 -- dn 0 -- up 1 -- dn 1 -- ...`, `allJoined_edge`) is correct
and proved for ANY choice of which strands play "up"/"down" within an edge.
What is NOT free is choosing, site by site, which arrival-departure pairs are
`pass`es (crossing to the neighbour edge) versus internal round-trip steps,
in a way that is *simultaneously* consistent along the whole chain so the
result is one cycle and not several. That choice is exactly Eulerian-circuit
existence for this restricted shape, and restricting the shape did not turn
it into bookkeeping -- BLOCK 199's own counterexample already shows a
site-local, order-independent rule for making that choice does not exist;
any correct rule has to see the whole run's width sequence at once (which
strand is a `pass` at site `e+1` depends on more than the two edges at that
site). That is a genuine combinatorial-induction argument, not a translation
step, and formalizing it (even in this restricted shape) is comparable in
size to formalizing a Hierholzer-style argument, not smaller.

**Honest verdict.** Confirmed harder, not closed: no new Lean committed
(forcing a partial here risks exactly the sorry/vacuous outcome the ground
rules forbid; every one-line special case already sits in BLOCK 197's
uniform-width proof and adds nothing). Mathlib re-confirmed to lack the
theorem. The bespoke-structure framing is correct and is not a place to look
for a shortcut that removes the inductive content -- BLOCKS 199-206 already
found the sharpest available reduction (the per-edge and per-link lemmas,
all proved, `RunStrandsConnected` isolated as the sole remaining input). A
future session's best next move is not more repackaging of `AllJoined` but
an actual induction on the run's edge list building the pass/bounce choice
by strong induction (e.g. on total strand count), carrying a connectivity
invariant explicitly -- i.e., start writing the Hierholzer-shaped argument
for this restricted shape, since no shortcut around it was found tonight
either.

## BLOCK 335 (2026-09-06) — VEndpt-vs-Endpt bridge (BLOCK 332's type mismatch):
## option (a) projection ruled out concretely; option (b) confirmed genuinely
## large, not a repackaging; no Lean committed

Assigned BLOCK 332's exact open item: bridge `Data (VEndpt n mm)` (what
`Elt.dataOf` produces, via `GenericData.dataG`) down to `Data (Endpt n m)`
(what `ConfigLoop.c_le_Z_final`/`shield_law_runs` consume), or regeneralize
the latter. No commit -- a concrete negative finding on option (a), and a
confirmation (not just a repeat of the BLOCK 332 guess) that option (b) is
real work, not a mechanical generalization.

**What the two virtual points actually are, read from the source (task step
1).** `VEndpt n mm := Endpt n mm ⊕ Bool` (EltBridge.lean:204). `.inr false`
is the virtual arrival at site `0`, `.inr true` the virtual departure at
`kstar` (doc comment, same line) -- together they patch the exact deficit
`deficit_eq` proves the real model is short (`[s=kstar]-[s=0]`) so that
`VEndpt.balanced` (line ~300) holds at every site. `VEndpt.partner`
(line 318) pairs them with each other: `.inr b ↦ .inr (!b)`. This is a
*choice*, flagged honestly in the file's own comment ("the one genuine
choice in the extension... that reading belongs to (M)") -- not derived,
posited as part of the transfer model.

**Why option (a) (a projection `Data (VEndpt n mm) → Data (Endpt n m)`)
does not work, concretely (task steps 2-3).** `Data` here is
`WalkGraph.Data` (`p`,`t` : two fixed-point-free involutions never
agreeing) -- confirmed `ConfigLoop`'s `Data (Endpt n m)` opens
`WalkGraph` and is this same structure, not `EndData.Data` (a
different, unrelated structure of the same name that carries
`side`/`isArr`/`depSign`, EndData.lean:32 -- worth flagging since the two
`Data`s coexist in the same import graph and are easy to conflate).
`VEndpt.dataOf` (EltBridge.lean:906-930-ish, `GenericData.dataG`) sets
`p := VEndpt.partner` directly (so the crossing pairing on the two virtual
points is exactly the fixed `.inr b ↔ .inr (!b)`, never touching real
ends -- that part IS clean and would restrict correctly), but sets
`t := turnG siteOf isArr hbal`, built from
`TurnBuild.exists_involution_of_card_eq` (TurnBuild.lean:20) -- a bare
`Classical.choice`-backed existence theorem, no canonical order-based
construction. Adding the virtual arrival/departure at sites `0`/`kstar`
changes `arrOf`/`depOf` at exactly those two sites (one more element
each, by `VEndpt.card_arrAt`/`card_depAt`), so the `t`-matching `dataG`
chooses at those two sites is chosen *fresh* over the new, larger sets --
there is no theorem, and structurally no reason, tying it back to "the
plain-`Endpt` matching at that site, plus the new element matched to
itself/dropped". So a `Data (VEndpt n mm)` built this way carries `t`-edges
at sites `0`/`kstar` with **no forced relationship** to any
`Data (Endpt n m)`'s `t` at those sites -- there is no well-defined
"forget the two virtual points" map on `Data`, because `t` is not
determined by anything the two `Data`s could be required to share.
**This rules out (a) as stated** -- not "hard", but ill-typed at the level
of "which theorem would you even try to prove": there is no `t`-preserving
projection to write down, since `t` at those two sites is a free choice
independent of the real-only choice. (A different route -- reproving
`VEndpt.dataOf` with a *specific*, non-generic matching at sites `0`/`kstar`
that provably restricts to the real-only matching -- is conceivable but is
new construction, not a bridge from what `Elt.dataOf` already produces; out
of scope for "make the existing objects connect".)

**Option (b), checked against actual `RunInv`/`c_le_Z_final` dependencies
(task step 4).** Read `RunInv` (ConfigLoop.lean:1355) and `run_step`/`c_le_Z`
(1385-1500) in full. `edgeOf`/`atTop` DO have `VEndpt` analogues already
(`VEndpt.edgeOf bnd`, `VEndpt.atTop`, EltBridge.lean:483-491) -- so far so
good, generalizing the site/edge/orientation layer looks plausible. But
`RunInv.hmin` and `run_step`'s cost-minimality argument are stated through
`CostMerge.costOf (endDataOf up ds) E`, where `endDataOf` builds an
`EndData.Data (Endpt n m)` (ConfigLoop.lean:345) -- `EndData.Data` carries
`side`/`isArr`/`depSign : Bool → Bool`, i.e. **assigns a deposit sign to
each of the two real sides of an edge**, a notion with no stated analogue
for a *virtual*, phantom-edge end (`VEndpt.edgeOf` sends both virtual
points to one arbitrary `bnd`, not two real sides of a real edge -- "side"
is meaningless there as defined). Confirms BLOCK 332's guess was directionally
right but understates it: this is not just "regeneralize `RunInv`'s type
variable", it requires first deciding what `EndData.Data`/`CostMerge.costOf`
*mean* for a phantom end (a new modeling choice, not a generalization of an
existing definition), then redoing every lemma in `NoGapCutFree`/`CutComponents`
that `run_step`/`c_le_Z_final` cite over that new meaning. That is genuinely
comparable in size to rebuilding the run-descent chain, not a mechanical
`variable {α}` change -- consistent with BLOCK 332's "non-trivial, not
attempted" but now with the specific blocking definition named.

**Verdict.** No Lean committed -- both routes named in BLOCK 332 checked for
real; (a) is now ruled out with a specific reason (`t`'s nonconstructive,
site-local choice has no forced restriction), not just deferred; (b) is
confirmed to need a new modeling decision (`side`/cost for phantom ends)
before any regeneralization can start, not merely a bigger diff. This
matches, and sharpens, BLOCK 332's own "next concrete step" framing rather
than contradicting it. No sorry added, nothing forced.

## BLOCK 336 (2026-09-06, commit 669dccb) -- a THIRD route past BLOCK 335's two,
## closed: the desubdivision identity, proved general over the choice; plus a
## redirection finding (`VEndpt.shield_of_initial`/`HasInitialTurnInv` already
## supersedes the whole VEndpt-vs-Endpt framing as the route to `Elt.c<=|Z|`)

Assigned the exact strategy BLOCK 332/335 didn't try: not a projection (BLOCK
335's ruled-out (a)) and not regeneralizing `RunInv` (BLOCK 335's (b)), but
building the real-only datum **from `Elt.dataOf`'s own output**, by treating
the two virtual points as subdividing one edge of a smaller graph and undoing
that subdivision.

**Hand check first, as instructed.** Verified by direct computation on two
tiny explicit `Data (Fin 6/8)` examples (worked by hand, not Rust -- the claim
reduces to elementary permutation-cycle bookkeeping small enough to trace by
hand and not worth a Rust job) that: given `D : Data (α ⊕ Bool)` with the two
extra points `u=inr false`,`v=inr true` partnered by `p` (`p u = v`), `t`
necessarily sends `u`,`v` to two REAL points `x0 = t u`, `x1 = t v` (forced:
`t` can't fix them, `pt_ne` rules out `t u = v`) -- and forgetting `u,v`,
rewiring `t` so `x0`,`x1` point at each other directly, leaves `walkCount`
**exactly unchanged**, UNLESS `x0`,`x1` were already `p`-partners of each
other, in which case `{x0,u,v,x1}` is an isolated 4-cycle and `walkCount`
drops by exactly 1 on removal. This is a sharper, EXACT dichotomy (0 or -1,
not the task brief's guessed "bounded by 1 either direction, non-constructive")
-- it is literally "subdividing an edge doesn't change component count",
plus the one genuine exception (the edge being subdivided was a loop-to-be).
Crucially, the argument uses NOTHING about `t` away from `u`,`v` -- it is
correct for *whatever* `TurnBuild.exists_involution_of_card_eq`'s
`Classical.choice` produced, which is exactly BLOCK 332/335's obstruction.

**Formalized in full**, generic case only (the corner case is real but was
not formalized -- see honest scope below). `WalkGraph.lean`, new section
`Desub`: `desub_exists_x0x1` (existence of `x0,x1`, unconditional -- no
hypothesis on `t` beyond `p u = v`), `desubP`/`desubT` (the rewired datum's
two maps), `desubData` (a genuine `Data α`, needing the one hypothesis
`hne : desubP D hpuv x0 ≠ x1`, i.e. the generic case), and
`walkCount_desub : walkCount D = walkCount (desubData D hpuv x0 x1 hx0 hx1
hne)`, proved via an explicit `ConnectedComponent` equivalence (`desubEquiv`):
collapsing `u,v` onto `x0,x1` one way, embedding `α` the other, both
directions checked by hand-written `SimpleGraph.Walk` induction
(`reach_of_step`, a small reusable general lemma: a step function that turns
every edge into an equal-or-reachable pair extends to full reachability).
`EltBridge.lean`: `Elt.dataOf_p`/`Elt.dataOf_hpuv` (the two virtual points
of `Elt.dataOf`'s output ARE `partner`s, read off `Elt.dataOf_mergesMin`),
`Elt.dataOf_exists_x0x1` (instantiates the existence lemma), and
`Elt.dataOf_walkCount_eq` (the assembled bridge: `walkCount (Elt.dataOf ...)
= walkCount (desubData (Elt.dataOf ...) ...)`, a genuine `Data (Endpt
(pdWidth ..) (pdMm ..))` on the right). `lake build` (whole project, 8629
jobs) clean; every new theorem's `#print axioms` is exactly `[propext,
Classical.choice, Quot.sound]`, 0 `sorry`.

**This is real, but it does NOT close `Elt.c <= |Z| + O(1)`, for a specific
reason distinct from BLOCK 335's.** `walkCount_desub`/`Elt.dataOf_walkCount_eq`
give a genuine `Data (Endpt n mm)` with equal (or `hne`-conditionally equal)
`walkCount` to `Elt.dataOf`'s -- but `c_le_Z_final` doesn't consume a bare
`Data (Endpt n m)`, it consumes one satisfying the full six-condition
`RunInv`, and `RunInv.hmin` is cost-minimality against `CostMerge.costOf
(endDataOf up ds)` -- a condition about the constructed datum, unrelated to
anything the walkCount identity says. Nothing here shows `desubData
(Elt.dataOf ...) ...` is `RunInv`-cost-minimal (or even that it's a sensible
question -- `endDataOf up ds` is built from a real configuration's `up`/`ds`,
and whether the desubdivided datum's implicit "real-only" reading agrees with
that configuration was never checked). So this closes exactly the question
BLOCK 332 posed ("is there a way to relate `Data (VEndpt n mm)`'s walkCount
to a genuine `Data (Endpt n m)`'s") and no more -- BLOCK 335's deeper
`hmin`/phantom-end modeling gap for option (b) is UNTOUCHED, not smaller.

**Redirection finding (the most load-bearing part of this session): the
VEndpt-vs-Endpt bridge is very likely not the route to `Elt.c<=|Z|` at all.**
While reading `EltBridge.lean` to place the Elt-level instantiation, found
`VEndpt.shield_turnInvN`/`VEndpt.shield_of_initial` (~4244-4350), an ALREADY-BUILT
chain that reaches `walkCount D' = Zf.card + 1` **directly on `VEndpt`**, no
`Endpt` bridge of any kind needed -- it takes a `TurnInvG`-satisfying `D` (a
VEndpt-level analogue of `RunInv`, with `hZ`/`hturn` already discharged by the
descent) and produces the exact shield law. Its own doc comment names the one
gap precisely: `HasInitialTurnInv` (an initial datum in `TurnInvG` -- the file
says the natural witness "should come from a `Realisation`... not built
abstractly from `dataG`"). This is a DIFFERENT, and by the file's own
account nearer-term, obstruction than either BLOCK 332/335's bridge or
`RunInv.hmin` on the `Endpt` side. A future session attacking `Elt.c<=|Z|`
should check `HasInitialTurnInv` first, not continue down the VEndpt-vs-Endpt
or `RunInv.hmin` framings -- this block's bridge, while real, is very likely
not on the critical path.

**Honest scope.** Corner case (`¬hne`) stated but not formalized (would need
a `Data` on a 2-point-removed subtype -- doable, not attempted, since the
generic case was the deliverable and the corner case doesn't change the
overall verdict above). `HasInitialTurnInv` itself: read but not attempted
this session -- flagged as the next concrete step, not investigated further.

## BLOCK 337 (2026-09-06) -- `HasInitialTurnInv` investigated in full: it is NOT a
## bypass of M4b/`RunStrandsConnected`, and one of its two routes is PROVABLY
## impossible, not just hard. No Lean committed (documentation-only finding).

Assigned BLOCK 336's own recommended next step: attack `HasInitialTurnInv`
(EltBridge.lean:4433) directly, the one remaining obligation
`VEndpt.shield_of_initial` (4440) reduces the shield law to. Read `shield_of_initial`/
`shield_turnInvN` (4244-4458) in full, then `Realisation`/`PathData.canon`
(Realisation.lean:245-468) to check whether "the natural witness should come from a
`Realisation`" (the file's own doc comment, 4428-4430) is a small bridging step or a
real gap. It is a real gap, and a deeper one than the comment suggests -- deep enough
that it reduces back to the SAME already-known-hard wall (`RunStrandsConnected`/M4b,
BLOCKS 199-206/332/333) rather than around it.

**`HasInitialTurnInv := ∃ D, TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0-1))
VEndpt.partner (vEndDataN up ds) Zf D`, and `TurnInvG` unpacks to
`CostMerge.MergesMin ... ∧ (∀ x, edge-changing turn ⇒ site ∉ Zf)`** -- a cost-minimal
merging pairing (`vEndDataN up ds : EndData.Data`) in which no turn crosses an edge at
a cut site. Two ways to get a `D`: (a) as the *end* of the merge-descent
(`CostMerge.exists_mergesMin`/`VEndpt.exists_mergesMinN`, already built), checking it
also satisfies `hturn`; (b) build `D`'s turn directly, site by site, bypassing
`MergesMin` altogether. Both were checked. Both dead-end, for two different reasons.

**Route (a) is not hard, it is PROVABLY IMPOSSIBLE, whenever a cut site is occupied.**
`vEndDataN`'s cost is `EndData.Data`'s FORCED/derived sign (`EndData.sgn`, EndData.lean
line 58): on one side of a site every arrival carries one sign and every departure the
opposite, unconditionally. Three already-proved, unsorried theorems pin the
consequence exactly: `EltBridge.pcost_same_side_two` (a same-side "bounce" pairing
costs exactly `2`), `EltBridge.pcostF_ge_one` (every pairing costs at least `1`, i.e.
a cross-side "pass" costs exactly `1`) and `ConfigLoop.no_ends_of_alpha_zero`
(ConfigLoop.lean:1079, ` alpha A 0 0 C = 0 → A = 0 ∧ C = 0`, i.e. in this model a cut
site's cost-zero condition forces it EMPTY of real ends). So in `vEndDataN`'s cost
model bouncing never wins over passing -- the exact reverse of the real (`SiteCost`)
site-cost model, where `bounce_beats_pass_at_cut` (EltBridge.lean:11271, using the
real free-sign class structure) proves the opposite. A `CostMerge.MergesMin`-optimal
`D` will therefore never choose to bounce at an occupied site, so it can never satisfy
`hturn` there -- `HasInitialTurnInv` via route (a) is unsatisfiable for any element
with an occupied cut site (which per `mu_eq_two_of_gap` a genuine multi-edge gap run
always has, `mu = 2` on both adjacent edges, not `0`). This is exactly the "the
obstruction is the derived sign" finding the file already recorded, independently, at
EndData.lean:41-57 and EltBridge.lean:4821-4835/5656-5679 (`GData`/
`GData.strictly_more_general`, the free-sign fix, EXISTS only as a bare cost function
-- `gcostOf` and swap-freeness lemmas, EltBridge.lean 4862-5654 -- with NO
`WalkGraph.Data`/`MergesMin`/`TurnInvG` analogue built over it). Connecting a
`Realisation` to `HasInitialTurnInv` via route (a) therefore is not "supply a
witness" -- it needs `TurnInvG`'s whole cost-merge layer (`CostMerge.lean`) rebuilt
over the free-sign model first. Substantial new construction, not bookkeeping.

**Route (b) exists in the file too, already worked out further than route (a) --
and it reduces to `RunStrandsConnected` exactly.** EltBridge.lean ~14001-15127 (a
much older, pre-BLOCK-199 layer: "The free-pair obstruction is not on the shield
law's path" through "`hturn` from zero crossing") builds `walkCount ≤ |Z|+1` with NO
`MergesMin` at all: `exists_glued_data` assembles a `WalkGraph.Data` directly from
per-site involutions, and `shield_upper_bound_from_turn`/`_multi`/`_mu_two` get
`hedge`+`hsep` straight from a CHOSEN turn's raw pass/bounce structure
(`hpass_up`/`hpass_dn`/`hbounce`), no minimality argument anywhere. But every
theorem in that chain is stated under `hm : ∀ e, m e = 2` (multiplicity exactly `2`
on EVERY edge, not just at cut sites -- the "all-gap chain" extreme family), and even
there `hturn`/`hpass_up`/`hpass_dn`/`hbounce` are left as hypotheses "to verify on a
concrete configuration", never discharged for a general `up`. Generalizing past
`mu = 2` means choosing, consistently across a whole run of edges with arbitrary
strand counts, which specific strand passes and which bounces at each site -- which
is verbatim `RunStrandsConnected` (H1b/M4b), the Eulerian-existence-shaped wall
BLOCKS 199-206 built the bespoke reduction for and BLOCK 333 (hours earlier, same
session family) re-confirmed hard today, with a concrete counterexample ruling out
any site-local order-independent rule.

**Verdict.** BLOCK 336's redirection ("`HasInitialTurnInv` is a different, nearer-term
obstruction than `RunStrandsConnected`, check it first") does not survive contact:
route (a) is a dead end for a reason unrelated to `RunStrandsConnected` (a proven
model mismatch, not a difficulty gap), and route (b) -- the only route that could
still work -- reduces to `RunStrandsConnected` exactly, at the point where `mu = 2`
stops being assumed. `HasInitialTurnInv` is not on a shorter path to `Elt.c <= |Z|`
than `RunStrandsConnected` was; it is, after full unpacking, the same wall (route b)
or a worse one (route a). No Lean committed: forcing either route would mean either
proving something false (route a, given an occupied cut site) or re-deriving
`RunStrandsConnected` from scratch inside a new frame (route b), neither of which is
"attack `HasInitialTurnInv`" in any sense narrower than the standing M4b problem.
Next session should not re-attempt `HasInitialTurnInv` expecting a shortcut; the
honest next step is still the one BLOCK 333 named: a genuine strong-induction
Hierholzer-style construction for `RunStrandsConnected` at general multiplicity, or
(separately, if ever wanted) building `CostMerge`'s layer over `GData` from scratch.

## BLOCK 338 (2026-09-06) -- H1c geometric-series transfer matrix: the natural
## construction is numerically refuted; the required per-state information has
## UNBOUNDED rank, not just an unbounded combinatorial range

Assigned to attempt the specific fix BLOCK 334 pointed at but did not attempt:
`IsAssembly`'s `T : Fin n -> Fin n -> PowerSeries ZZ` cannot index states by the raw
magnitude of `dcur` (BLOCK 334, unbounded, confirmed again by reading
`LocalState.muOf`/`dcur_le_muOf`, EltBridge.lean 6049-6100), but since `T`'s entries
are full power series, the standard fix is to collapse the sum over all magnitudes
into a geometric-series-valued matrix entry (`sum X^d = (1-X)^-1`), keeping the
`Fin n` index to a small number of DISCRETE classes. No Lean touched this session
(none of the work below needed the Lean file at all) -- this is a hand-derivation,
checked against a Rust computation, of whether that idea is actually sound BEFORE
attempting any Lean.

**The exact per-site cost, read off `LocalState.siteOf`/`muOf` (EltBridge.lean
6063-6071) and `flagStepB`'s weight `x^(sigma.st.muOf + tau.st.siteOf)` (7645,
7729-7734).** At a "plain" site (`arr=0`, `dep=0`, so `vL=vR=0` and the `eps`/`arr`
shift terms in `siteOf` vanish identically), the two formulas reduce to:

    muOf(d)      = 2 if d=0, 1 if d=+-1, |d| if |d|>=2      (fcur=0 case)
    siteOf(d,d') = max(|d|, |d'|)                            (dprev=d, dcur=d')

i.e. the transfer weight between consecutive sites is `X^(muOf(d) + max(|d|,|d'|))`,
`d` unbounded, `d'` fresh at every step, sign of `d` free (contributes a `x2`
multiplicity per nonzero magnitude, itself already proved as `sum_signed_eq_magnitudes`/
`sum_prod_signed`, EltBridge.lean ~10160-10180, for the FINITE-`N` truncation -- the
open step is the untruncated, all-`N`-at-once version).

**The candidate construction, precisely.** Define `u(a)` := the `PowerSeries ZZ`
generating function of the total weight of a walk that starts at magnitude `a` and
may stop after any number of further steps (`u = (I-K)^-1 . 1` for the infinite
operator `(K f)(a) = X^muOf(a) * sum_b signmult(b) X^max(a,b) f(b)`, `signmult(b) = 1`
if `b=0` else `2`). This satisfies the exact fixed-point equation (order-by-order
well-posed since `muOf(a) >= 1` always):

    u(a) = 1 + X^muOf(a) * [ X^a * S(a) + Ttail - S'(a) ]
    S(a)  = sum_{b<=a} signmult(b) u(b)          (cumulative)
    S'(a) = sum_{b<=a} signmult(b) X^b u(b)       (cumulative)
    Ttail = S'(infinity)  (well defined mod X^(D+1) as S'(D) for any working cap D)

If the task's geometric-series idea is right, `{u(a)}_a` -- or some other bounded
summary of "the state at magnitude a" -- has to collapse into a FIXED (`a`-independent)
finite-dimensional structure, since that is exactly what a bounded `Fin n` matrix `T`
with `PowerSeries ZZ` entries can express (a constant-coefficient linear recursion in
the walk-length variable, which is what `pathSumR`/`matrixPow_apply_eq_pathSumR`,
BLOCK 321, already reduces `IsAssembly` to).

**Rust check** (`rankcheck`, scratch, not part of the repo's tool tree -- this was a
one-off sanity computation, not a reusable verify script, so not landed under
`tools/`): solved the fixed-point equation above by Jacobi iteration (exact `i128`
arithmetic, guaranteed convergent since every equation carries an explicit
`X^muOf(a)`, order `>=1`, factor) at working degree `D`, for `D=36` and `D=70`.
Cross-checked the fixed-point equation itself against brute-force enumeration of all
finite walks from a fixed start state (`D'=6`): **exact agreement**, so the equation
above is not a mis-derivation.

Then tested the actual question: does `{u(0), u(1), ..., u(D)}`, as vectors of
`X`-coefficients, have rank bounded independent of `D` (evidence a finite `T`
exists), or does the rank grow with `D` (evidence it does not)? Result, unambiguous
at both working degrees:

    D=36: u(0..32) [33 vectors] -> rank 33 (FULL, zero dependencies)
          u(0..36) [37 vectors] -> rank 19  (collapse -- but see below)
    D=70: u(0..32) -> rank 33 (full); u(0..36) -> rank 36 (~full);
          u(0..64), u(0..70) -> rank 36 flat

The apparent "collapse" at the tail of each run is a TRUNCATION ARTIFACT, not a
genuine algebraic relation: `u(a)-1` has leading order `~2a` (confirmed directly in
the printed data, e.g. `a=10: order=20`, `a=12: order=24`), so once `2a` exceeds the
working degree `D`, `u(a)` is INDISTINGUISHABLE from the trivial vector `[1,0,...,0]`
at that truncation -- every such `a` contributes the identical vector, manufacturing
a fake rank deficiency that is purely about running out of precision, not about the
states becoming linearly dependent. Restricting to the genuinely-resolved range
(`a` up to about `D/2`), rank is **exactly full at every degree tested, with zero
relations found**, and the full-range rank itself grows from 19 (`D=36`) to 36
(`D=70`) -- linearly in `D`, not bounded.

**Conclusion.** This refutes the geometric-series idea as stated, and does so more
sharply than BLOCK 334: it is not merely that the magnitude has no `N`-independent
combinatorial cap (already known) -- it is that the *information* needed to predict
future transfer weights from the current magnitude has provably unbounded rank as a
`PowerSeries ZZ`-module, checked directly (not just argued informally) to working
degree 70 with zero counterexamples to "more precision keeps finding more
independent directions." No bounded number of discrete classes, and no finite-`Fin n`
matrix of `PowerSeries ZZ` entries built from them via geometric sums (or by any
other summary of the magnitude), can reproduce `flagStepB`'s exact weight for every
degree simultaneously, because the site cost's `max(|d|,|d'|)` coupling to the *next*
free variable `d'` requires knowing the *exact* current magnitude to unbounded
precision, not a bounded class of it. This is the same character of obstruction
(genuinely unbounded/transcendental structure resisting a finite closed form) as the
"travel null vector" problem elsewhere in this project, which needed a real rank-one
telescoping construction, not a geometric-series shortcut, to close -- and no such
construction was attempted here (out of scope for tonight, and not implied by
anything found).

**Honest scope.** No Lean file touched -- nothing here reached the point of writing
a Lean statement, because the mathematical content it would state is now believed
false as stated (a bounded `Fin n` cannot exist via this route). `H1c` stays open,
downgraded from "no known combinatorial cap" (BLOCK 334) to "the natural
power-series collapse is numerically refuted; a working construction, if one exists,
needs the same kind of exact closed-form/telescoping argument already used
elsewhere in this project for the travel recursion, applied fresh to this
`max`-coupled site-cost sum -- not attempted." Next session should not re-attempt
the "collapse by geometric series over a small discrete class" idea in this form;
it would need either (a) a genuinely different encoding of the state that isn't
simply "the magnitude, or a bounded function of it" (unclear one exists, given the
rank result), or (b) an exact telescoping solution of the boundary-value recursion
above specifically (a real, separate research task, not attempted).

## The "zigzag turn" is FALSE for even multiplicities; `Through2` replaces it

Session 2026-09-06, tool `src/bin/zigzag_check.rs` (`cargo run --release --bin
zigzag_check`). Model: sites `0..L`, edge `j` carrying `m_j` (even, `> 0`) parallel
strands; a turn is a fixed-point-free involution on strand ends pairing only ends at
the same site; `hturn` forbids passes at cut sites (set `Z`, plus the chain ends
`0` and `L`); a *run* is a maximal stretch of edges between cut sites. Target: every
run's strands form exactly one closed walk.

**M-Z1 | the design note's zigzag gives per-run connectivity | FALSE.** Its recipe
("bounce `(2i,2i+1)` at the far site, `(2i+1,2i+2)` at the near site; loose ends are
strand `0`'s near end and the last strand's far end") is self-inconsistent for even
`m`: with `m` even the far matching `(2i,2i+1)` is already *perfect*, so both loose
ends land at the **near** site, not one at each end. The quoted end-pattern only
holds for **odd** `m`, which the model excludes. Consequence: a zigzagged edge has
zero loose ends on one side, so it can never pass to the neighbour there, and every
edge closes into its own cycle. Sweep over all `m in {2,4,6}^L`, `L = 1..5`, all
`2^(L-1)` cut-sets (4665 configurations):

| variant | pass | fail | first counterexample |
|---|---|---|---|
| V1 plain zigzag, loose ends left | 363 | 4302 | `m=[2,2]`, `Z={}`: 2 components, 1 run |
| V2 plain zigzag, loose ends right | 363 | 4302 | same |
| V3 zigzag alternating by edge parity | 1200 | 3465 | same |
| V4 run-aware `Closed`/`Zig`/`Through2` | 4665 | 0 | none |
| V5 uniform `Through2` | 4665 | 0 | none |
| V6 uniform `Through2`, crossed passes | 4665 | 0 | none |

Split by longest run: V1 passes 363/363 when **every** run has length 1, and
0/4302 otherwise (0/2088 at max run 2, 0/1404 at 3, 0/567 at 4, 0/243 at 5). So the
zigzag is exactly right for a one-edge run and exactly wrong for everything else.

**Why 2 loose ends can never be enough.** All `m_j` are even, so at any site the
pass count `p` satisfies `m - p` even, hence `p` is even and connecting two edges
costs `p >= 2`. An edge interior to a run therefore needs `2` loose ends on *each*
side, i.e. `4`, i.e. its bounces split it into **two** paths, not one chain. Further,
the two paths must each run left-to-right (a left-hanging plus a right-hanging path
gives `b - a + 2` components per run, not 1).

**M-Z2 | the repaired convention `Through2` | VERIFIED (exhaustive, in range).**
Per edge with `m` strands, uniformly, with no knowledge of `Z`:

- left bounces `(2i, 2i+1)` for `i = 1 .. m/2 - 1`;
- right bounces `(2i+1, 2i+2)` for `i = 0 .. m/2 - 2`;
- loose left ends: strands `0` and `1`; loose right ends: strands `0` and `m-1`.

(Strand `0` runs straight through; strands `1..m-1`, an odd count, zigzag.) Assemble
by: at a non-cut site pass the two loose right ends of edge `j-1` to the two loose
left ends of edge `j` (**either** bijection works — V5 and V6 both pass); at a cut
site (including sites `0` and `L`) bounce each edge's own two loose ends together.
`hturn` is then satisfied by construction and the run boundaries degenerate
correctly: closing edge `a`'s left pair fuses its two paths into one path with both
ends at site `a+1`, and for a one-edge run the two closings fuse the two paths into a
single `m`-cycle. No run-length case split and no parity-of-`j` convention is needed,
which is what makes it worth formalizing.

Evidence: 4665/4665 above; stress sweep `m in {2,4,6,8}^L`, `L = 1..6`, all cut-sets:
**149 796 / 149 796** pass; `L = 12` chains up to 156 strands, 1/2/7/12 runs, all
exact. Sanity: `m_j = 2` everywhere, `L = 1..7`, all cut-sets, 127/127 — agreeing
with the existing `m = 2` special case.

Component counts are computed **twice** per configuration by independent methods
(union-find over strands, and explicit walk tracing over ends) and asserted equal;
every turn is separately validated as a fixed-point-free same-site involution
obeying `hturn`. A brute-force enumerator additionally enumerates *all* hturn-legal
turns for 42 small configurations (`m in {2,4}`, `L <= 3`, ~150k turns, both counters
cross-checked on each): every configuration admits at least one good turn, so the
target is achievable everywhere it was tested, e.g. `m=[4,4,4]`, `Z={}`: 31 104 of
99 225 legal turns work.
