// The strand structure of a run, at general mu.
//
// A run of k edges, each carrying u = mu/2 up strands and u down strands.  A strand is
// (edge, level, up?).  The turn contributes:
//
//   pass at the site between edge j and j+1
//       (j, l, up) -- (j+1, sigma_j(l), up)        the up chain
//       (j+1, l, dn) -- (j, tau_j(l), dn)          the down chain
//   bounce at the run's two ends
//       (0, l, up) -- (0, betaL(l), dn)
//       (k-1, l, up) -- (k-1, betaR(l), dn)
//
// At u = 1 every permutation is the identity and the run is one component -- BLOCK 160's
// two-chain argument.  At u = 2 the permutations are free, and the question is which
// choices leave the run connected.

fn perms(u: usize) -> Vec<Vec<usize>> {
    let mut out = vec![];
    let mut idx: Vec<usize> = (0..u).collect();
    fn go(j: usize, idx: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if j == idx.len() { out.push(idx.clone()); return; }
        for i in j..idx.len() { idx.swap(j, i); go(j + 1, idx, out); idx.swap(j, i); }
    }
    go(0, &mut idx, &mut out);
    out
}

/// components of the strand graph, by union-find
fn components(k: usize, u: usize, sig: &[Vec<usize>], tau: &[Vec<usize>],
              bl: &[usize], br: &[usize]) -> usize {
    let n = k * u * 2;
    let id = |e: usize, l: usize, up: bool| (e * u + l) * 2 + if up { 0 } else { 1 };
    let mut p: Vec<usize> = (0..n).collect();
    fn find(p: &mut Vec<usize>, x: usize) -> usize {
        let mut x = x;
        while p[x] != x { p[x] = p[p[x]]; x = p[x]; }
        x
    }
    let mut uni = |p: &mut Vec<usize>, a: usize, b: usize| {
        let (ra, rb) = (find(p, a), find(p, b));
        if ra != rb { p[ra] = rb; }
    };
    for j in 0..k.saturating_sub(1) {
        for l in 0..u {
            uni(&mut p, id(j, l, true), id(j + 1, sig[j][l], true));
            uni(&mut p, id(j + 1, l, false), id(j, tau[j][l], false));
        }
    }
    for l in 0..u {
        uni(&mut p, id(0, l, true), id(0, bl[l], false));
        uni(&mut p, id(k - 1, l, true), id(k - 1, br[l], false));
    }
    let mut roots = std::collections::HashSet::new();
    for x in 0..n { let r = find(&mut p, x); roots.insert(r); }
    roots.len()
}

pub fn run(kmax: usize, mu: usize) {
    let u = mu / 2;
    println!("[cutturn] chain -- the strand structure of ONE run, mu = {mu} (u = {u})");
    println!("[cutturn] a run is one component exactly when the composite is a single cycle");
    let ps = perms(u);
    for k in 1..=kmax {
        let npass = k.saturating_sub(1);
        let total_choices = ps.len().pow((2 * npass + 2) as u32);
        let mut ok = 0u64;
        let mut tot = 0u64;
        let mut best = usize::MAX;
        for code in 0..total_choices {
            let mut c = code;
            let mut sig = vec![]; let mut tau = vec![];
            for _ in 0..npass { sig.push(ps[c % ps.len()].clone()); c /= ps.len(); }
            for _ in 0..npass { tau.push(ps[c % ps.len()].clone()); c /= ps.len(); }
            let bl = ps[c % ps.len()].clone(); c /= ps.len();
            let br = ps[c % ps.len()].clone();
            let comp = components(k, u, &sig, &tau, &bl, &br);
            tot += 1;
            best = best.min(comp);
            if comp == 1 { ok += 1; }
        }
        println!("  k = {k:2}: {ok:>6} of {tot:>6} choices give ONE component; fewest = {best}");
    }
    // a single u-cycle at ONE place, identity everywhere else
    println!("  --- identity passes, one u-cycle at the left bounce ---");
    for k in 1..=kmax {
        let npass = k.saturating_sub(1);
        let idp: Vec<usize> = (0..u).collect();
        let cyc: Vec<usize> = (0..u).map(|l| (l + 1) % u).collect();
        let sig = vec![idp.clone(); npass];
        let tau = vec![idp.clone(); npass];
        let comp = components(k, u, &sig, &tau, &cyc, &idp);
        println!("  k = {k:2}: {comp} component(s)");
    }
    // the identity choice, which is what a local rule would pick
    for k in 1..=kmax {
        let npass = k.saturating_sub(1);
        let idp: Vec<usize> = (0..u).collect();
        let sig = vec![idp.clone(); npass];
        let tau = vec![idp.clone(); npass];
        let comp = components(k, u, &sig, &tau, &idp, &idp);
        println!("  k = {k:2}: the all-identity choice gives {comp} components");
    }
}

/// Where can the cycle go?  A PASS costs 1 whichever levels it pairs, so a cycle there
/// is free.  A BOUNCE at a cut site costs 0 only if it pairs within classes, so a cycle
/// there is free only when some class has at least two levels.
///
/// So a run of length k >= 2 can always take its cycle in a pass.  A run of length 1 has
/// no pass, and must take it in a bounce -- which is possible only if the classes are
/// not all singletons.
pub fn run_placement(kmax: usize, mu: usize) {
    let u = mu / 2;
    println!("[cutturn] where the cycle can go, mu = {mu} (u = {u})");
    let idp: Vec<usize> = (0..u).collect();
    let cyc: Vec<usize> = (0..u).map(|l| (l + 1) % u).collect();
    println!("  identity bounces, one u-cycle in the FIRST PASS:");
    for k in 2..=kmax {
        let npass = k - 1;
        let mut sig = vec![idp.clone(); npass];
        sig[0] = cyc.clone();
        let tau = vec![idp.clone(); npass];
        let comp = components(k, u, &sig, &tau, &idp, &idp);
        println!("    k = {k:2}: {comp} component(s)");
    }
    println!("  k = 1 has no pass, so the cycle must sit in a bounce:");
    let c1 = components(1, u, &[], &[], &cyc, &idp);
    let c2 = components(1, u, &[], &[], &idp, &idp);
    println!("    k = 1: cycle in the bounce -> {c1} component(s);  identity -> {c2}");
}
