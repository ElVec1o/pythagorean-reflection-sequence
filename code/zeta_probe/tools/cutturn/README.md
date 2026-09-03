# cutturn

Does a minimal-cost merging pairing avoid turning across cut sites?

This is the last obligation of the shield law as `VEndpt.shield_of_initial`
leaves it -- `HasInitialTurnInv`, i.e. a `D` with `TurnInvG`:

    CostMerge.MergesMin  /\  (edgeOf (t x) != edgeOf x  ->  siteOf x not in Zf)

a minimal-cost merging pairing in which no turn crosses a cut site.

## The family

The all-gap chain: `n` edges, every deposit zero, so `mu = 2` on every edge and
**every** interior site is a cut site, `|Z| = n-1`.  That is the extreme case
for `c <= |Z|`.

Edge `j` carries two strands, one up and one down; strand `i` has a bottom end
at site `j` and a top end at site `j+1`.  The crossing partner joins the two
ends of a strand.  A turn is an involution pairing, at each site, the arrivals
to the departures.  At an interior site there are exactly two such pairings:
both pairs inside one edge (a double bounce, cost 0), or both crossing (a
double pass, cost 2).

## Cost model

`bounce 0, pass 1` -- two of the three weights `sitecost`'s H0 certifies as
`(bounce, flip, pass) = (0, 2, 1)` with 0 exceptions.  The sign-flip weight
plays no role on the gap chain, which carries no signs.  Every omitted weight
is non-negative, so these costs are a **lower bound**, which is the safe
direction for a claim that minimality forces bounces.

## Result

    cutturn 12

    n= 2 ... n=12:  min cost 0, walks at min = |Z|+1, all-bounce=true, any-pass=false

On every chain the minimum is attained only by the bounce-only pairing, and
that pairing has exactly `|Z| + 1` walks.

## What it shows

`TurnInvG`'s second condition is **not an independent demand**.  A cut site has
site cost 0 (`siteCost_zero_of_cut`), and a pass costs at least 1, so a pairing
attaining the site cost cannot pass there (`no_pass_at_zero_cost_site`,
`no_cross_turn_at_cut` in `EltBridge.lean`).  Minimality alone forces it.

Combined with BLOCK 132 -- the cut-site pairing has no freedom, being a
fixed-point-free involution on a two-element side -- the position is: at the cut
sites everything is determined, and determined the right way.  What remains open
in `HasInitialTurnInv` is `MergesMin` itself, off the cut sites.

## Not shown

That a minimal-cost merging pairing exists in general.  The chain here is the
all-gap family only; deposits, travel and the sign structure are absent, and the
flip weight is untested because nothing flips.  M4b is not closed by this.
