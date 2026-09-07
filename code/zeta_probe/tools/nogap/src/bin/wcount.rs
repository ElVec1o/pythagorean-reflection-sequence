// wcount -- the coefficient series of EltBridge.W, by exact enumeration.
//
// `W`'s N-th coefficient is the degree-N configuration count: the number of valid
// `SiteCost.PathData` with `lR = N`.  This enumerates them directly from the Lean
// definitions (Realisation.lean / MarkedSite.lean), so the series can be compared with
// the bulk max-kernel resolvent of BLOCK 340/345 (AssemblyContract).
//
// Exact integer arithmetic; no floating point.

#[inline]
fn travel(kstar: i64, j: i64) -> i64 {
    if 0 <= j && j < kstar { 1 } else if kstar <= j && j < 0 { -1 } else { 0 }
}

/// `mu j` of `SiteCost.PathData`.
#[inline]
fn mu(d: i64, f: i64) -> i64 { if d == 0 && f == 0 { 2 } else { d.abs().max(f.abs()) } }

/// `siteCost s = max |alphaAt s| |betaAt s|`, with the virtual events folded in.
fn site_cost(a: i64, b: i64, kstar: i64, eps: i64, delta: bool, s: i64, dl: i64, dc: i64) -> i64 {
    let _ = (a, b);
    let varr = if s == 0 { 1 } else { 0 };
    let vd = if s == kstar { 1 } else { 0 };
    let vl = if delta { 0 } else { vd };
    let vr = if delta { vd } else { 0 };
    let alpha = dl - varr + eps * vl;
    let beta = dc - eps * vr;
    alpha.abs().max(beta.abs())
}

fn main() {
    let nmax: i64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(12);
    let mut counts = vec![0u64; (nmax + 1) as usize];

    // span [A,B] with A <= 0 <= B (PathData's hA, hB). Each edge contributes mu >= 1,
    // so B - A + 1 <= nmax.
    for a in -nmax..=0 {
        for b in 0..=nmax {
            let len = b - a + 1;
            if len > nmax { continue; }
            // kstar must satisfy A <= kstar <= B+1 (A_le_kstar / kstar_le_B_succ), and
            // houter forces travel to vanish outside [A,B], i.e. the travel interval
            // between 0 and kstar must sit inside [A,B].
            for kstar in a..=(b + 1) {
                if kstar > 0 && kstar - 1 > b { continue; }
                if kstar < 0 && kstar < a { continue; }
                for &eps in &[1i64, -1] {
                    for &delta in &[false, true] {
                        // d on [A,B], with hpar: d j = travel j (mod 2), and |d j| <= nmax.
                        let mut dvec = vec![0i64; len as usize];
                        enumerate(a, b, kstar, eps, delta, 0, &mut dvec, nmax, &mut counts, 0);
                    }
                }
            }
        }
    }

    println!("# coefficient series of W (configuration count by lR)");
    for n in 0..=nmax { println!("N={n:2}  count={}", counts[n as usize]); }
    let s: Vec<String> = (0..=nmax).map(|n| counts[n as usize].to_string()).collect();
    println!("series: {}", s.join(","));
}

#[allow(clippy::too_many_arguments)]
fn enumerate(a: i64, b: i64, kstar: i64, eps: i64, delta: bool, idx: i64,
             dvec: &mut Vec<i64>, nmax: i64, counts: &mut Vec<u64>, acc: i64) {
    let len = b - a + 1;
    if acc > nmax { return; }
    if idx == len {
        // hAmin / hBmin: the span must be minimal.
        let fa = travel(kstar, a);
        let fb = travel(kstar, b);
        if !(a == 0 || dvec[0] != 0 || fa != 0) { return; }
        if !(b == 0 || dvec[(len - 1) as usize] != 0 || fb != 0) { return; }
        // `acc` already holds every edge cost and every site in [A, B]; only the last
        // site B+1 remains (it uses d[B] and d[B+1]=0).
        let dl = dvec[(len - 1) as usize];
        let t = acc + site_cost(a, b, kstar, eps, delta, b + 1, dl, 0);
        if t <= nmax { counts[t as usize] += 1; }
        return;
    }
    let j = a + idx;
    let f = travel(kstar, j);
    // hpar: d j = f (mod 2).  Prune on the running cost: this edge already contributes
    // mu(d,f) >= max(|d|,1), and site `j` becomes fully determined once d[idx] is fixed
    // (it depends only on d[idx-1] and d[idx]).
    let mut v = -nmax;
    while v <= nmax {
        if (v - f).rem_euclid(2) == 0 {
            dvec[idx as usize] = v;
            let mut add = mu(v, f);
            let s = j;                                  // site s = j uses d[j-1], d[j]
            let dl = if idx >= 1 { dvec[(idx - 1) as usize] } else { 0 };
            add += site_cost(a, b, kstar, eps, delta, s, dl, v);
            if acc + add <= nmax {
                enumerate(a, b, kstar, eps, delta, idx + 1, dvec, nmax, counts, acc + add);
            }
        }
        v += 1;
    }
    dvec[idx as usize] = 0;
}
