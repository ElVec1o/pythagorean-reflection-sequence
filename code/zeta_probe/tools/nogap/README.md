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
