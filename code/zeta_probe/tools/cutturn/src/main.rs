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


/// the site-cost weights `sitecost` H0 certifies: bounce 0, flip 2, pass 1.
/// classes 0,1 are the left edge (+,-), classes 2,3 the right edge (+,-).
#[inline]
fn cost_of(i: usize, j: usize) -> usize {
    if i == j { 0 } else if i / 2 == j / 2 { 2 } else { 1 }
}

/// Deposit-bearing chains.  Edge `j` carries deposit `a_j` in {-2,0,2}, so
/// `mu = 2`, one up strand and one down strand, exactly as in the gap chain --
/// only the SIGN CLASSES differ, and with them the cost.  A realisation chooses
/// `pu_j` in [0,1] with `pd_j = pu_j + a_j/2` in [0,1]; that pins `pu` when
/// `a_j != 0` and leaves it free when `a_j = 0`.
///
/// A cut site is one with `a_{s-1} = a_s = 0`.
fn mode_dep(nmax: usize) {
    println!("[cutturn] deposit-bearing chains, n = 2..{nmax}, a_j in {{-2,0,2}}");
    println!("[cutturn] cost: bounce 0, flip 2, pass 1 (the full H0 weights)");
    let mut worst: Vec<String> = vec![];
    let mut tested = 0u64;
    let mut pass_at_cut_in_min = 0u64;
    let mut walks_ne = 0u64;
    for n in 2..=nmax {
        let mut a = vec![0i64; n];
        let total = 3usize.pow(n as u32);
        for code in 0..total {
            let mut c = code;
            for j in 0..n { a[j] = [0i64, 2, -2][c % 3]; c /= 3; }
            // cut sites
            let cuts: Vec<usize> = (1..n).filter(|&s| a[s - 1] == 0 && a[s] == 0).collect();
            let ncut = cuts.len();
            // realisations: pu_j free only when a_j == 0
            let free: Vec<usize> = (0..n).filter(|&j| a[j] == 0).collect();
            let mut best = usize::MAX;
            let mut best_walks = usize::MAX;
            let mut best_has_pass_at_cut = false;
            let mut best_has_clean = false;
            for pcode in 0..(1usize << free.len()) {
                let mut pu = vec![0usize; n];
                let mut pd = vec![0usize; n];
                let mut ok = true;
                for j in 0..n {
                    if a[j] == 2 { pu[j] = 0; pd[j] = 1; }
                    else if a[j] == -2 { pu[j] = 1; pd[j] = 0; }
                    else { ok = ok; }
                }
                for (b, &j) in free.iter().enumerate() {
                    let v = (pcode >> b) & 1; pu[j] = v; pd[j] = v;
                }
                if !ok { continue; }
                let acls = |x: usize| if x == 1 { 0usize } else { 1usize };   // left half
                let rcls = |x: usize| if x == 1 { 2usize } else { 3usize };   // right half
                for mask in 0usize..(1usize << (n - 1)) {
                    let mut cost = 0usize;
                    // boundary sites: forced, one edge present
                    cost += cost_of(rcls(pd[0]), rcls(pu[0]));
                    cost += cost_of(acls(pu[n - 1]), acls(pd[n - 1]));
                    let mut dsu = Dsu::new(4 * n);
                    for j in 0..n { for i in 0..2 { dsu.union(eid(j, i, 0), partner(eid(j, i, 0))); } }
                    dsu.union(eid(0, 1, 0), eid(0, 0, 0));
                    dsu.union(eid(n - 1, 0, 1), eid(n - 1, 1, 1));
                    let mut passed_at_cut = false;
                    for s in 1..n {
                        let (al, ar) = (acls(pu[s - 1]), rcls(pd[s]));
                        let (dl, dr) = (acls(pd[s - 1]), rcls(pu[s]));
                        if (mask >> (s - 1)) & 1 == 0 {
                            cost += cost_of(al, dl) + cost_of(ar, dr);
                            dsu.union(eid(s - 1, 0, 1), eid(s - 1, 1, 1));
                            dsu.union(eid(s, 1, 0), eid(s, 0, 0));
                        } else {
                            cost += cost_of(al, dr) + cost_of(ar, dl);
                            dsu.union(eid(s - 1, 0, 1), eid(s, 0, 0));
                            dsu.union(eid(s, 1, 0), eid(s - 1, 1, 1));
                            if cuts.contains(&s) { passed_at_cut = true; }
                        }
                    }
                    let mut roots = std::collections::HashSet::new();
                    for x in 0..4 * n { let r = dsu.find(x); roots.insert(r); }
                    let walks = roots.len();
                    if cost < best {
                        best = cost; best_walks = walks;
                        best_has_pass_at_cut = passed_at_cut; best_has_clean = !passed_at_cut;
                    } else if cost == best {
                        best_walks = best_walks.min(walks);
                        if passed_at_cut { best_has_pass_at_cut = true; } else { best_has_clean = true; }
                    }
                }
            }
            if best == usize::MAX { continue; }
            tested += 1;
            if best_has_pass_at_cut { pass_at_cut_in_min += 1; }
            if best_walks != ncut + 1 {
                walks_ne += 1;
                if worst.len() < 6 {
                    worst.push(format!("    a={:?}  |Z|={}  min cost={}  walks at min={}  |Z|+1={}",
                        a, ncut, best, best_walks, ncut + 1));
                }
            }
            let _ = best_has_clean;
        }
    }
    println!("  {tested} (chain, deposit) configurations");
    println!("  min-cost pairings that pass at a cut site : {pass_at_cut_in_min}");
    println!("  configurations with walks-at-min != |Z|+1 : {walks_ne}");
    for w in &worst { println!("{}", w); }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "gap".into());
    let nmax: usize = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(7);
    if mode == "dep" { mode_dep(nmax); return; }
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
