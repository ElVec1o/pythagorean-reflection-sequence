# The no-gap lemma: sharpening prop:local(i) under (T)

**Status: reduction + verified statement + identified mechanism. NOT a proof.**
Date 2026-08-22.

## What was actually open

`prop:travelinv` (=(T), one of the two hypotheses under the conditional
transcendence of `U`) *is* proved in `lifting_U.tex` -- but in two lines from
`prop:local`(i), which carries **no proof at all**: only a numerical check to
true length <= 16 (3869 pure-travel elements, 0 violations) and a mechanistic
paragraph. So the open core of (T) is one combinatorial claim.

## The reformulation

By `lem:closedlen` (route_b_funceq.tex) a **gap edge** is an edge of the active
span with `a_j = 0` AND `f_j = 0`; such an edge is forced to `m_j = 2` by
reachability. If `supp(a) \subseteq I_k` then the span *is* `I_k`, and every edge
there has `f_j = \pm 1 \ne 0`. So the hypothesis of `prop:local`(i) is exactly
"no gap edges", and the natural statement is strictly more general:

> **Conjecture (no-gap).** If `g` has no gap edge, then `c(g) = 0`.

This drops the requirement that the support lie inside `I_k`: it also covers
elements whose lamps leave `I_k` but stay contiguous with it.

## Verification (`/tmp/gaptest.py`, BFS ground truth vs `relaxed_solve`)

`c := (\ell_T - \ell_R)/2` with `\ell_T` from `lamp_lib.bfs` and `\ell_R` from
`lamp_lib.relaxed_solve`.

| depth | class | elements | c != 0 |
|---|---|---|---|
| 13 | pure-travel | 780 | 0 |
| 13 | **no-gap** | **1407** | **0** |
| 13 | has-gap | 96 | 4 |
| 17 | pure-travel | 3869 | 0 |
| 17 | **no-gap** | **7928** | **0** |
| 17 | has-gap | 1064 | 84 |

The depth-17 pure-travel count **3869 reproduces exactly** the figure quoted in
`lifting_U.tex` for the `prop:local`(i) validation, so the harness is on the same
footing as the paper's own check. The no-gap class is ~2x larger with zero
violations. Note also that gaps *permit* but do not *force* cycles (92% of
gap-bearing elements still have c=0) -- consistent with the shield law.

## The mechanism (this is the new part)

`lem:swap` charges +2 to merge an isolated cycle into the open walk, and its
proof pinpoints why: at a **gap** edge the cycle deposits net zero, so its pair
is a cost-0 bounce, and the merge forces a sign-flip bounce (`pc = 2`).

But a 2-swap between two **pass** pairs is free:
`(a -> d), (a' -> d')  |->  (a -> d'), (a' -> d)`
with `a` on L and `d,d'` on R stays two passes, cost `1+1` before and after,
while merging the two components. **So merging is free whenever both components
have a pass at a shared site.** Gap edges are precisely where no pass is
available.

## Where it stops

Reading the DP in `lamp_lib.solve` (not the prose) fixes the site model:
`u = (m+f_j)/2`, `dn = (m-f_j)/2` -- the net direction of an edge is `f_j`, not
the deposit -- and `pd - pu = (a_j - f_j)/2` fixes the signs. Sides L/R are the
lower/upper edge at a site; a pass is an L-arrival matched to an R-departure.

Take an isolated cycle `gamma` with support interval `[p,q]`. At interior sites
of `[p,q]`, `gamma` crosses and therefore has a pass, so if the open walk also
passes at any interior site of `[p,q]` the merge is free and we are done. The
residual case is a shared site at an *endpoint* of `[p,q]`, where `gamma`
bounces. There the 2-swap pass/bounce is free **iff** the open walk's up-departure
at `p` carries the same sign as `gamma`'s -- i.e. iff the strands of edge `p` are
**sign-homogeneous**. Under `m_p = |a_p|` all crossings share the sign of `a_p`,
which would close it; whether relaxed-optimal realizations can be forced into
that shape under no-gap is exactly the remaining step.

**Next:** decide the sign-homogeneity question, either by extracting optimal
states from the DP or by an exchange argument on `pu`/`pd`. If it holds, the
no-gap lemma follows, `prop:local`(i) becomes a corollary, and (T) is proved
outright -- leaving (L) as the sole hypothesis under `U`.

## Addendum: the connection to paper 2's reverse shield inequality

`prop:cut` (paper2, §5.5) calls a site **cut** when `alpha_s = beta_s = Phi_s = 0`,
with `Z` the interior cut sites, and proves `c >= |Z|`. `rem:shieldowes` records
that the reverse `c <= |Z|` is **not proved**, and is verified only on `k* = 0`
bulk configurations (1 048 544 of them, mode `shield`).

The hypothesis of `prop:local`(i) -- lamp support inside `I_k` -- forces no gap
edges and hence `Z = \emptyset`. Therefore:

> **(T)'s open core is exactly the `Z = \emptyset` case of the reverse shield
> inequality `c <= |Z|`.**

Two weak links the papers track separately are one statement. Proving `c <= |Z|`
closes both, removing (T) from `U`'s hypotheses and leaving (L) alone. The
`Z = \emptyset` case looks strictly easier than the general one: `rem:shieldowes`
asks for pairings connecting all crossings within each of `|Z|+1` classes,
whereas at `Z = \emptyset` there is a single class and the requirement collapses
to connected + even degrees => one Eulerian trail.

## Negative result: do NOT reimplement Z in Python

Three attempts to recompute `Z` from the paper's prose plus the Rust source all
failed, each differently (2 violations, then 10, then 42 -- the last including
**10 at `k* = 0`**, where paper 2's exhaustive run has 0 exceptions). A violation
at `k* = 0` is proof of a bug in the reimplementation, not in the paper.

Diagnosis on `(eps=1, delta=1, k=-1, {-1:1, 1:-2})`: the naive formula marks site 0
cut (`alpha = d_{-1}-1 = 0`, `beta = 0`, `Phi = -1+1 = 0`), but the walk starts at 0,
must reach edge `+1` to deposit `-2`, return, and end at `k=-1`, so strands cross
site 0 repeatedly. **The reachability that forces a gap edge to `m = 2` is not
captured by the local deposit data**, and that is what the naive `alpha/beta` miss.

Use `code/zeta_probe/tools/sitecost` (exact, Rust, dual-solver) for anything
involving `Z`. Extending the `c = |Z|` check to `k* != 0` is untested territory
and worth doing -- through that tool, not a reimplementation.

**What is unaffected:** the no-gap result above, which never touches `Z` --
`c = (\ell_T - \ell_R)/2` is computed from BFS ground truth against
`relaxed_solve` directly.
