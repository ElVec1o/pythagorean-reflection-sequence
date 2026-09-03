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

## Deposit-bearing chains (`cutturn dep <nmax>`)

The gap chain carries no signs, so the flip weight is never exercised.  The
`dep` mode adds deposits: edge `j` carries `a_j` in `{-2, 0, 2}`, still
`mu = 2` and one strand each way, but now the sign CLASSES differ and the full
`(bounce, flip, pass) = (0, 2, 1)` matrix is live, as
`cost_of(i,j) = 0 if i=j, 2 if i/2=j/2, else 1`.  A realisation chooses `pu_j`,
which is pinned when `a_j != 0` and free when `a_j = 0`; the minimum is taken
over realisations as well as pairings.  A cut site is `a_{s-1} = a_s = 0`.

    cutturn dep 9

     29520 (chain, deposit) configurations
     min-cost pairings that pass at a cut site : 0
     configurations with walks-at-min != |Z|+1 : 0

The second line is the cut-site condition again, now with signs.  The third is
`c = |Z|` itself -- the walk count at the minimum equals `|Z| + 1` in every
configuration, which is the shield law, not merely its cut-site half.

The cut-site half also no longer needs a minimality argument.  A cut site has
both deposits zero, hence `pd = pu` on each side, hence the arrival and
departure classes AGREE on each side; the bounce then pairs each class with
itself at cost 0 while the pass crosses halves twice at cost 1+1.  Proved as
`bounce_beats_pass_at_cut` in `EltBridge.lean`, for every sign split.

## Not shown

That a minimal-cost merging pairing exists in general.  Both families here hold
`|a_j| <= 2`, so `mu = 2` on every edge: one up strand and one down strand, and
exactly two pairings per site.  The first genuinely richer case is `|a| = 4`,
where `mu = 4` gives two strands each way, the number of pairings per site
grows, and flips can combine across a site -- none of that is tested.  Travel
edges (`f = +-1`) and the marker sites are absent too.  M4b is not closed by
this.
