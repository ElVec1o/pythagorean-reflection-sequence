// cutturn -- does a minimal-cost merging pairing avoid turning across cut sites?
//
// This is the last obligation of the shield law as `VEndpt.shield_of_initial`
// leaves it: `HasInitialTurnInv`, i.e. a `D` with `TurnInvG`, which is
//
//     CostMerge.MergesMin  /\  (edgeOf (t x) != edgeOf x  ->  siteOf x not in Zf)
//
// -- a minimal-cost merging pairing in which no turn crosses a cut site.
//
// The family tested is the all-gap chain: n edges, every deposit zero, so
// mu = 2 on every edge and EVERY interior site is a cut site.  That is the
// extreme case for `c <= |Z|`, with |Z| = n-1.
//
// Endpoints.  Edge j carries mu = 2 strands, one directed up (i=0) and one down
// (i=1); strand i has a bottom end at site j and a top end at site j+1.  The
// crossing partner p joins the two ends of a strand.  A turn t is an involution
// pairing, at each site, the arrivals to the departures there:
//
//     site s arrivals   : top of the UP strand of edge s-1, bottom of the DOWN
//                         strand of edge s
//     site s departures : top of the DOWN strand of edge s-1, bottom of the UP
//                         strand of edge s
//
// Cost model: a turn joining two ends of the SAME edge is a bounce and costs 0;
// one joining different edges is a pass and costs 1.  These are two of the three
// weights `sitecost`'s H0 certifies as (bounce, flip, pass) = (0, 2, 1); the
// sign-flip weight plays no role here because the gap chain carries no signs.
// Since every omitted weight is non-negative, the costs below are lower bounds,
// which is the safe direction for a claim that minimality FORCES bounces.
//
// All integer arithmetic.

/// endpoint id: edge j, strand i (0 = up, 1 = down), end (0 = bottom, 1 = top)
#[inline]
fn eid(j: usize, i: usize, top: usize) -> usize { j * 4 + i * 2 + top }
#[inline]
fn edge_of(x: usize) -> usize { x / 4 }
#[inline]
fn partner(x: usize) -> usize { x ^ 1 }   // flips the `top` bit, same edge+strand

struct Dsu(Vec<usize>);
impl Dsu {
    fn new(n: usize) -> Self { Dsu((0..n).collect()) }
    fn find(&mut self, a: usize) -> usize {
        if self.0[a] != a { let r = self.find(self.0[a]); self.0[a] = r; }
        self.0[a]
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb { self.0[ra] = rb; }
    }
}

fn main() {
    let nmax: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    println!("[cutturn] all-gap chains, n = 2..{nmax}; every interior site is a cut site");
    println!("[cutturn] cost: bounce 0, pass 1 (a lower bound on the full model)");
    let mut verdict = true;
    for n in 2..=nmax {
        let np = 4 * n;                       // endpoints
        let _nsite = n + 1;                    // sites 0..n
        // the choice at each site: interior sites have two pairings (bounce/pass),
        // the two boundary sites have exactly one (only one edge is present).
        let interior: Vec<usize> = (1..n).collect();
        let ncut = interior.len();            // |Z| = n-1
        let mut best_cost = usize::MAX;
        let mut best_walks_at_min = usize::MAX;
        let mut min_has_pass = false;         // does ANY min-cost pairing pass at a cut site?
        let mut min_all_bounce = false;       // is there a min-cost pairing with no such pass?
        let mut merges_min_walks = usize::MAX;
        for mask in 0u32..(1u32 << ncut) {
            let mut dsu = Dsu::new(np);
            let mut cost = 0usize;
            let mut passed_at_cut = false;
            // strands
            for j in 0..n { for i in 0..2 { dsu.union(eid(j, i, 0), partner(eid(j, i, 0))); } }
            // boundary site 0: bottom of the DOWN strand of edge 0 arrives, bottom of
            // the UP strand departs; the only pairing joins them (a bounce, cost 0).
            dsu.union(eid(0, 1, 0), eid(0, 0, 0));
            // boundary site n: same on the far edge, using the tops.
            dsu.union(eid(n - 1, 0, 1), eid(n - 1, 1, 1));
            for (b, &s) in interior.iter().enumerate() {
                let bounce = (mask >> b) & 1 == 0;
                if bounce {
                    // both pairs stay inside one edge
                    dsu.union(eid(s - 1, 0, 1), eid(s - 1, 1, 1));
                    dsu.union(eid(s, 1, 0), eid(s, 0, 0));
                } else {
                    // both pairs cross the site
                    dsu.union(eid(s - 1, 0, 1), eid(s, 0, 0));
                    dsu.union(eid(s, 1, 0), eid(s - 1, 1, 1));
                    cost += 2;                       // two passes
                    passed_at_cut = true;
                }
            }
            let mut roots = std::collections::HashSet::new();
            for x in 0..np { let r = dsu.find(x); roots.insert(r); }
            let walks = roots.len();
            if cost < best_cost {
                best_cost = cost; best_walks_at_min = walks;
                min_has_pass = passed_at_cut; min_all_bounce = !passed_at_cut;
                merges_min_walks = walks;
            } else if cost == best_cost {
                best_walks_at_min = best_walks_at_min.min(walks);
                if passed_at_cut { min_has_pass = true; } else { min_all_bounce = true; }
                merges_min_walks = merges_min_walks.min(walks);
            }
        }
        let ok = min_all_bounce && !min_has_pass && merges_min_walks == ncut + 1;
        verdict &= ok;
        println!(
            "  n={n:2}  |Z|={ncut:2}  min cost={best_cost}  walks at min={merges_min_walks}  |Z|+1={}  \
             min-cost pairing: all-bounce={min_all_bounce} any-pass={min_has_pass}  {}",
            ncut + 1, if ok { "OK" } else { "MISMATCH" }
        );
        let _ = best_walks_at_min;
    }
    println!("[cutturn] VERDICT: {}", if verdict {
        "on every all-gap chain the minimal-cost pairing is bounce-only at every \
         cut site, and attains exactly |Z|+1 walks -- TurnInvG's second condition \
         is IMPLIED by minimality here, not an extra demand"
    } else { "MISMATCH -- see rows above" });
}
