// sitecost -- exact verification of the local site-cost law (M1) of paper2 sec.5
// and of the gap-run cycle count (M2, the shield law).
//
// Ground truth is the crossing-pairing optimisation of paper1
// Proposition (metric formula): at a site, arrivals are paired with departures,
// a pass (opposite sides) costs 1, a bounce (same side, same sign) costs 0, and
// a sign-flip bounce (same side, opposite signs) costs 2.  Classes are
//   0 = (left,+)  1 = (left,-)  2 = (right,+)  3 = (right,-).
//
// Edge j carries a deposit a_j, a travel indicator f_j in {-1,0,+1} and a
// crossing count m_j >= max(|a_j|,|f_j|) with m_j = a_j = f_j (mod 2);
// u_j = (m_j+f_j)/2 up-crossings, dn_j = (m_j-f_j)/2 down-crossings, split by
// sign as (p^u_j, u_j-p^u_j) and (p^d_j, dn_j-p^d_j), with
//        a_j = 2 p^d_j - dn_j + u_j - 2 p^u_j,   i.e. p^d_j = p^u_j + (a_j-f_j)/2.
//
// At the site between edge L (= edge s-1) and edge R (= edge s):
//   arr = [p^u_L, u_L-p^u_L, p^d_R, dn_R-p^d_R]
//   dep = [p^d_L, dn_L-p^d_L, p^u_R, u_R-p^u_R]
// plus a virtual arrival in class (left,+) at site 0 and a virtual departure in
// class (delta*==1 ? right : left, eps*) at site k*.
//
// All arithmetic is exact integer arithmetic.  No floating point anywhere.

mod realize;

use std::collections::HashMap;
use std::env;

const INF: i64 = 1 << 40;

/// (bounce, sign-flip bounce, pass).  The model value is (0,2,1); the other
/// values are used only by the hypothesis-deletion mode.
static CW: [std::sync::atomic::AtomicI64; 3] = [
    std::sync::atomic::AtomicI64::new(0),
    std::sync::atomic::AtomicI64::new(2),
    std::sync::atomic::AtomicI64::new(1),
];

#[inline]
pub fn cost_of(i: usize, j: usize) -> i64 {
    let k = if i == j { 0 } else if i / 2 == j / 2 { 1 } else { 2 };
    CW[k].load(std::sync::atomic::Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Method A: min-cost flow, successive shortest paths with SPFA.
// ---------------------------------------------------------------------------
struct Mcmf {
    to: Vec<usize>,
    cap: Vec<i64>,
    cost: Vec<i64>,
    head: Vec<Vec<usize>>,
}

impl Mcmf {
    fn new(n: usize) -> Self {
        Mcmf { to: vec![], cap: vec![], cost: vec![], head: vec![vec![]; n] }
    }
    fn add(&mut self, u: usize, v: usize, c: i64, w: i64) {
        self.head[u].push(self.to.len());
        self.to.push(v);
        self.cap.push(c);
        self.cost.push(w);
        self.head[v].push(self.to.len());
        self.to.push(u);
        self.cap.push(0);
        self.cost.push(-w);
    }
    /// Successive shortest paths.  Distances come from a full Bellman-Ford
    /// (|V|-1 sweeps over every arc, no early exit, no predecessor array), and
    /// the augmenting path is then found by a DFS over admissible arcs guarded
    /// by a visited mark.  Reconstructing the path from a predecessor array is
    /// unsafe here: the residual graph has zero-cost arcs, so the predecessor
    /// relation can contain a zero-cost cycle.
    fn run(&mut self, s: usize, t: usize) -> (i64, i64) {
        let n = self.head.len();
        let (mut flow, mut total) = (0i64, 0i64);
        loop {
            let mut dist = vec![INF; n];
            dist[s] = 0;
            for _ in 0..n {
                let mut changed = false;
                for e in 0..self.to.len() {
                    let u = self.to[e ^ 1];
                    if self.cap[e] > 0 && dist[u] < INF && dist[u] + self.cost[e] < dist[self.to[e]] {
                        dist[self.to[e]] = dist[u] + self.cost[e];
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            if dist[t] >= INF {
                break;
            }
            // DFS along admissible arcs, collecting one s-t path
            let mut path: Vec<usize> = vec![];
            let mut seen = vec![false; n];
            fn dfs(
                u: usize,
                t: usize,
                g: &Mcmf,
                dist: &[i64],
                seen: &mut Vec<bool>,
                path: &mut Vec<usize>,
            ) -> bool {
                if u == t {
                    return true;
                }
                seen[u] = true;
                for &e in &g.head[u] {
                    let v = g.to[e];
                    if g.cap[e] > 0 && !seen[v] && dist[u] + g.cost[e] == dist[v] {
                        path.push(e);
                        if dfs(v, t, g, dist, seen, path) {
                            return true;
                        }
                        path.pop();
                    }
                }
                false
            }
            if !dfs(s, t, self, &dist, &mut seen, &mut path) {
                break;
            }
            let push = path.iter().map(|&e| self.cap[e]).min().unwrap();
            for &e in &path {
                self.cap[e] -= push;
                self.cap[e ^ 1] += push;
            }
            flow += push;
            total += push * dist[t];
        }
        (flow, total)
    }
}

fn mincost_flow(arr: &[i64; 4], dep: &[i64; 4]) -> Option<i64> {
    let na: i64 = arr.iter().sum();
    let nd: i64 = dep.iter().sum();
    if na != nd {
        return None;
    }
    if na == 0 {
        return Some(0);
    }
    let mut g = Mcmf::new(10);
    for i in 0..4 {
        g.add(8, i, arr[i], 0);
        g.add(4 + i, 9, dep[i], 0);
        for j in 0..4 {
            g.add(i, 4 + j, INF, cost_of(i, j));
        }
    }
    let (f, c) = g.run(8, 9);
    if f != na {
        return None;
    }
    Some(c)
}

// ---------------------------------------------------------------------------
// Method B: exact dynamic programming over the transportation polytope.
// Independent of Method A (no flow, no potentials): it enumerates the
// row-by-row allocation and memoises on the remaining column demands.
// ---------------------------------------------------------------------------
fn dp_rec(
    i: usize,
    arr: &[i64; 4],
    rem: [i64; 4],
    memo: &mut HashMap<(usize, [i64; 4]), i64>,
) -> i64 {
    if i == 4 {
        return if rem.iter().all(|&x| x == 0) { 0 } else { INF };
    }
    if let Some(&v) = memo.get(&(i, rem)) {
        return v;
    }
    let a = arr[i];
    let mut best = INF;
    for x0 in 0..=a.min(rem[0]) {
        for x1 in 0..=(a - x0).min(rem[1]) {
            for x2 in 0..=(a - x0 - x1).min(rem[2]) {
                let x3 = a - x0 - x1 - x2;
                if x3 < 0 || x3 > rem[3] {
                    continue;
                }
                let c = x0 * cost_of(i, 0)
                    + x1 * cost_of(i, 1)
                    + x2 * cost_of(i, 2)
                    + x3 * cost_of(i, 3);
                let sub = dp_rec(i + 1, arr, [rem[0] - x0, rem[1] - x1, rem[2] - x2, rem[3] - x3], memo);
                if sub < INF && c + sub < best {
                    best = c + sub;
                }
            }
        }
    }
    memo.insert((i, rem), best);
    best
}

fn mincost_dp(arr: &[i64; 4], dep: &[i64; 4]) -> Option<i64> {
    let na: i64 = arr.iter().sum();
    let nd: i64 = dep.iter().sum();
    if na != nd {
        return None;
    }
    let mut memo = HashMap::new();
    let v = dp_rec(0, arr, *dep, &mut memo);
    if v >= INF {
        None
    } else {
        Some(v)
    }
}

static DUAL: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// The site cost.  When DUAL is set, both exact solvers are run and any
/// disagreement aborts.
fn mincost(arr: &[i64; 4], dep: &[i64; 4]) -> Option<i64> {
    let a = mincost_flow(arr, dep);
    if DUAL.load(std::sync::atomic::Ordering::Relaxed) {
        let b = mincost_dp(arr, dep);
        if a != b {
            panic!("SOLVER DISAGREEMENT arr={:?} dep={:?} flow={:?} dp={:?}", arr, dep, a, b);
        }
    }
    a
}

// ---------------------------------------------------------------------------
// Site configuration builder.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy)]
struct Edge {
    a: i64,
    f: i64,
    m: i64,
    pu: i64,
}

impl Edge {
    fn u(&self) -> i64 {
        (self.m + self.f) / 2
    }
    fn dn(&self) -> i64 {
        (self.m - self.f) / 2
    }
    fn pd(&self) -> i64 {
        self.pu + (self.a - self.f) / 2
    }
    fn valid(&self) -> bool {
        if (self.m - self.f) % 2 != 0 || (self.m - self.a) % 2 != 0 {
            return false;
        }
        if self.m < self.a.abs() || self.m < self.f.abs() {
            return false;
        }
        let (u, dn, pd) = (self.u(), self.dn(), self.pd());
        u >= 0 && dn >= 0 && self.pu >= 0 && self.pu <= u && pd >= 0 && pd <= dn
    }
}

/// arrivals/departures at the site between edge `l` (left) and edge `r` (right).
/// `virt_arr`: the virtual arrival at the origin, class (left,+).
/// `virt_dep`: Some(class) for the virtual departure at site k*.
fn site_vectors(l: &Edge, r: &Edge, virt_arr: bool, virt_dep: Option<usize>) -> Option<([i64; 4], [i64; 4])> {
    if !l.valid() || !r.valid() {
        return None;
    }
    let mut arr = [l.pu, l.u() - l.pu, r.pd(), r.dn() - r.pd()];
    let mut dep = [l.pd(), l.dn() - l.pd(), r.pu, r.u() - r.pu];
    if virt_arr {
        arr[0] += 1;
    }
    if let Some(c) = virt_dep {
        dep[c] += 1;
    }
    if arr.iter().sum::<i64>() != dep.iter().sum::<i64>() {
        return None;
    }
    Some((arr, dep))
}

// ---------------------------------------------------------------------------
// Mode: cross-check the two exact solvers.
// ---------------------------------------------------------------------------
fn mode_xcheck(nmax: i64) {
    let mut cases = 0u64;
    let mut bad = 0u64;
    let mut badcf = 0u64;
    // exhaustive over all arr,dep with entries <= nmax and equal sums
    for a0 in 0..=nmax {
        for a1 in 0..=nmax {
            for a2 in 0..=nmax {
                for a3 in 0..=nmax {
                    let s = a0 + a1 + a2 + a3;
                    for d0 in 0..=nmax.min(s) {
                        for d1 in 0..=nmax.min(s - d0) {
                            for d2 in 0..=nmax.min(s - d0 - d1) {
                                let d3 = s - d0 - d1 - d2;
                                if d3 < 0 || d3 > nmax {
                                    continue;
                                }
                                let arr = [a0, a1, a2, a3];
                                let dep = [d0, d1, d2, d3];
                                let x = mincost_flow(&arr, &dep);
                                let y = mincost_dp(&arr, &dep);
                                cases += 1;
                                if x != y {
                                    bad += 1;
                                    if bad <= 5 {
                                        println!("  MISMATCH arr={:?} dep={:?} flow={:?} dp={:?}", arr, dep, x, y);
                                    }
                                }
                                // the closed form: max(|alpha|,|beta|,|Phi|)
                                let phi = (arr[0] + arr[1]) - (dep[0] + dep[1]);
                                let alpha = (dep[0] - dep[1]) - (arr[0] - arr[1]);
                                let beta = (arr[2] - arr[3]) - (dep[2] - dep[3]);
                                let cf = alpha.abs().max(beta.abs()).max(phi.abs());
                                if x != Some(cf) {
                                    badcf += 1;
                                    if badcf <= 5 {
                                        println!("  CLOSED-FORM MISS arr={:?} dep={:?} true={:?} formula={}", arr, dep, x, cf);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!(
        "[xcheck] entries <= {}: {} (arr,dep) pairs, {} mismatches between min-cost-flow and transportation DP",
        nmax, cases, bad
    );
    println!("[xcheck] closed form max(|alpha|,|beta|,|Phi|): {} misses", badcf);
    println!("[xcheck] VERDICT: {}", if bad == 0 && badcf == 0 { "both solvers AGREE and the closed form is exact" } else { "DISAGREE" });
}

// ---------------------------------------------------------------------------
// Mode: the interior local cost law.
// ---------------------------------------------------------------------------
fn mode_interior(amax: i64, lam: i64) {
    let mut n_cfg = 0u64;
    let mut viol_law = 0u64;    // min over m,splits != max(|aL|,|aR|)
    let mut viol_lb = 0u64;     // some (m,split,matching) strictly below max(|aL|,|aR|)
    let mut viol_split = 0u64;  // cost depends on the sign splits
    let mut viol_minimal = 0u64;// minimal m does not already attain the min
    let mut examples: Vec<String> = vec![];

    for f in [-1i64, 0, 1] {
        // deposits have the parity of f
        let mut al = -amax;
        while al <= amax {
            if (al - f).rem_euclid(2) != 0 {
                al += 1;
                continue;
            }
            let mut ar = -amax;
            while ar <= amax {
                if (ar - f).rem_euclid(2) != 0 {
                    ar += 1;
                    continue;
                }
                let target = al.abs().max(ar.abs());
                let mut global_min = INF;
                let mut minimal_m_min = INF;
                let mut ok = true;
                for il in 0..=lam {
                    let ml = al.abs().max(f.abs()) + 2 * il;
                    for ir in 0..=lam {
                        let mr = ar.abs().max(f.abs()) + 2 * ir;
                        // cost as a function of the splits, for this (ml,mr)
                        let mut per_split: Vec<i64> = vec![];
                        let el0 = Edge { a: al, f, m: ml, pu: 0 };
                        let er0 = Edge { a: ar, f, m: mr, pu: 0 };
                        for pul in 0..=el0.u() {
                            for pur in 0..=er0.u() {
                                let el = Edge { a: al, f, m: ml, pu: pul };
                                let er = Edge { a: ar, f, m: mr, pu: pur };
                                if let Some((arr, dep)) = site_vectors(&el, &er, false, None) {
                                    if let Some(c) = mincost(&arr, &dep) {
                                        n_cfg += 1;
                                        per_split.push(c);
                                        if c < global_min {
                                            global_min = c;
                                        }
                                        if il == 0 && ir == 0 && c < minimal_m_min {
                                            minimal_m_min = c;
                                        }
                                        if c < target {
                                            viol_lb += 1;
                                            ok = false;
                                            if examples.len() < 8 {
                                                examples.push(format!(
                                                    "LB aL={} aR={} f={} mL={} mR={} puL={} puR={} cost={} < {}",
                                                    al, ar, f, ml, mr, pul, pur, c, target
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if !per_split.is_empty() {
                            let c0 = per_split[0];
                            if per_split.iter().any(|&c| c != c0) {
                                viol_split += 1;
                                ok = false;
                                if examples.len() < 8 {
                                    examples.push(format!(
                                        "SPLIT aL={} aR={} f={} mL={} mR={} costs={:?}",
                                        al, ar, f, ml, mr, per_split
                                    ));
                                }
                            }
                        }
                    }
                }
                if global_min < INF {
                    if global_min != target {
                        viol_law += 1;
                        ok = false;
                        if examples.len() < 8 {
                            examples.push(format!(
                                "LAW aL={} aR={} f={} min={} target={}",
                                al, ar, f, global_min, target
                            ));
                        }
                    }
                    if minimal_m_min != global_min {
                        viol_minimal += 1;
                        if examples.len() < 8 {
                            examples.push(format!(
                                "MINIMAL-M aL={} aR={} f={} minimal_m={} global={}",
                                al, ar, f, minimal_m_min, global_min
                            ));
                        }
                    }
                }
                let _ = ok;
                ar += 1;
            }
            al += 1;
        }
    }
    println!(
        "[interior] |a| <= {}, m up to minimal+{}, all sign splits, f in {{-1,0,1}}",
        amax,
        2 * lam
    );
    println!("[interior] {} (edge-pair, m, split) configurations evaluated", n_cfg);
    println!("[interior] violations: law={} lower-bound={} split-dependence={} minimal-m={}",
             viol_law, viol_lb, viol_split, viol_minimal);
    for e in &examples {
        println!("   ex: {}", e);
    }
    println!(
        "[interior] VERDICT: {}",
        if viol_law == 0 && viol_lb == 0 && viol_split == 0 && viol_minimal == 0 {
            "Site(aL,aR) = max(|aL|,|aR|), attained at minimal m, split-independent -- 0 exceptions"
        } else {
            "EXCEPTIONS FOUND"
        }
    );
}

// ---------------------------------------------------------------------------
// Mode: the marker sites.
// ---------------------------------------------------------------------------
fn marker_min(al: i64, fl: i64, ar: i64, fr: i64, virt_arr: bool, virt_dep: Option<usize>, lam: i64) -> Option<i64> {
    let mut best = INF;
    for il in 0..=lam {
        let ml = al.abs().max(fl.abs()) + 2 * il;
        for ir in 0..=lam {
            let mr = ar.abs().max(fr.abs()) + 2 * ir;
            let el0 = Edge { a: al, f: fl, m: ml, pu: 0 };
            let er0 = Edge { a: ar, f: fr, m: mr, pu: 0 };
            for pul in 0..=el0.u().max(0) {
                for pur in 0..=er0.u().max(0) {
                    let el = Edge { a: al, f: fl, m: ml, pu: pul };
                    let er = Edge { a: ar, f: fr, m: mr, pu: pur };
                    if let Some((arr, dep)) = site_vectors(&el, &er, virt_arr, virt_dep) {
                        if let Some(c) = mincost(&arr, &dep) {
                            if c < best {
                                best = c;
                            }
                        }
                    }
                }
            }
        }
    }
    if best >= INF {
        None
    } else {
        Some(best)
    }
}

fn mode_marker(amax: i64, lam: i64) {
    // site 0 for k>0: left edge is bulk (f=0, a even), right edge is travel (f=+1, a odd)
    // site k for k>0: left edge is travel (f=+1, a odd), right edge is bulk (f=0, a even)
    // site 0 for k<0: left edge is travel (f=-1, a odd), right edge is bulk (f=0, a even)
    // site k for k<0: left edge is bulk (f=0, a even), right edge is travel (f=-1, a odd)
    let cases: Vec<(&str, i64, i64, bool, bool)> = vec![
        ("site0 k>0", 0, 1, true, false),
        ("siteK k>0", 1, 0, false, true),
        ("site0 k<0", -1, 0, true, false),
        ("siteK k<0", 0, -1, false, true),
    ];
    println!("[marker] |a| <= {}, m up to minimal+{}, all sign splits, all four (eps*,delta*)", amax, 2 * lam);
    for (name, fl, fr, v_arr, v_dep) in cases {
        let mut rows: Vec<String> = vec![];
        let mut n = 0u64;
        let mut bad_paper = 0u64;   // vs  max(|aL|-1,|aR|)  (site0 orientation)
        let mut bad_shift = 0u64;   // vs  max(|aL-1|,|aR|)  / mirror
        let mut bad_dep_eps = 0u64; // dependence on (eps*,delta*)
        // shape census: the multiset of the four (eps*,delta*) costs, normalised
        // by subtracting the minimum.  Records how the four terms of prop:shape's
        // sum are spread in q, independently of the overall power.
        let mut shapes: HashMap<Vec<i64>, u64> = HashMap::new();
        let mut al = -amax;
        while al <= amax {
            if (al - fl).rem_euclid(2) != 0 {
                al += 1;
                continue;
            }
            let mut ar = -amax;
            while ar <= amax {
                if (ar - fr).rem_euclid(2) != 0 {
                    ar += 1;
                    continue;
                }
                let mut vals: Vec<(i64, i64, i64)> = vec![];
                for eps in [1i64, -1] {
                    for delta in [0i64, 1] {
                        let vd = if v_dep {
                            Some((if delta == 1 { 2usize } else { 0usize }) + (if eps == 1 { 0 } else { 1 }))
                        } else {
                            None
                        };
                        if let Some(c) = marker_min(al, fl, ar, fr, v_arr, vd, lam) {
                            vals.push((eps, delta, c));
                        }
                    }
                }
                if vals.is_empty() {
                    ar += 1;
                    continue;
                }
                n += 1;
                let c0 = vals[0].2;
                if vals.len() == 4 {
                    let lo = vals.iter().map(|&(_, _, c)| c).min().unwrap();
                    let mut sh: Vec<i64> = vals.iter().map(|&(_, _, c)| c - lo).collect();
                    sh.sort();
                    *shapes.entry(sh).or_insert(0) += 1;
                }
                if vals.iter().any(|&(_, _, c)| c != c0) {
                    bad_dep_eps += 1;
                    if rows.len() < 6 {
                        rows.push(format!("  (eps,delta)-dependence aL={} aR={} vals={:?}", al, ar, vals));
                    }
                }
                // candidate closed forms
                // the virtual event sits on the LEFT of site 0 (arrival class (left,+))
                // and on the side named by delta* at site k.
                let paper = (al.abs() - 1).max(ar.abs());
                let shift_l = (al - 1).abs().max(ar.abs());
                let shift_r = al.abs().max((ar + 1).abs());
                let pick_paper = if v_arr { paper } else { al.abs().max(ar.abs() - 1) };
                let pick_shift = if v_arr { shift_l } else { shift_r };
                if c0 != pick_paper {
                    bad_paper += 1;
                    if rows.len() < 6 {
                        rows.push(format!("  paper-form miss aL={} aR={} true={} paper={}", al, ar, c0, pick_paper));
                    }
                }
                if c0 != pick_shift {
                    bad_shift += 1;
                    if rows.len() < 6 {
                        rows.push(format!("  shift-form miss aL={} aR={} true={} shift={}", al, ar, c0, pick_shift));
                    }
                }
                ar += 1;
            }
            al += 1;
        }
        println!(
            "[marker] {}: {} (aL,aR) cells;  max(|aL|-1,|aR|)-type misses = {};  |a-1|-type misses = {};  (eps*,delta*)-dependence = {}",
            name, n, bad_paper, bad_shift, bad_dep_eps
        );
        for r in &rows {
            println!("{}", r);
        }
        let mut sh: Vec<(Vec<i64>, u64)> = shapes.into_iter().collect();
        sh.sort_by(|x, y| y.1.cmp(&x.1));
        for (k, v) in &sh {
            println!("  shape {:?} x {}", k, v);
        }
    }
    // the exact table on the range the paper certificate used, plus negatives
    println!("[marker] site0 k>0 table, cost(aL,aR) for aL even in [-8,8], aR odd in [-5,5]:");
    print!("        aR:");
    let mut ar = -5;
    while ar <= 5 {
        print!("{:4}", ar);
        ar += 2;
    }
    println!();
    let mut al = -8;
    while al <= 8 {
        print!("  aL={:3}  ", al);
        let mut ar = -5;
        while ar <= 5 {
            let c = marker_min(al, 0, ar, 1, true, None, lam);
            match c {
                Some(v) => print!("{:4}", v),
                None => print!("   -"),
            }
            ar += 2;
        }
        println!();
        al += 2;
    }
}


// ---------------------------------------------------------------------------
// Mode: the universal law  Site = max(|alpha|,|beta|),
//   alpha = (signed departures to the left) - (signed arrivals from the left),
//   beta  = (signed arrivals from the right) - (signed departures to the right),
// both counted with the virtual events included.  For a plain interior site
// alpha = a_L and beta = a_R.
// ---------------------------------------------------------------------------
fn mode_universal(amax: i64, lam: i64) {
    // (name, fL, fR, virtual arrival?, virtual departure?)
    let sites: Vec<(&str, i64, i64, bool, bool)> = vec![
        ("interior f=0  (bulk)",        0, 0, false, false),
        ("interior f=+1 (travel)",      1, 1, false, false),
        ("interior f=-1 (travel)",     -1, -1, false, false),
        ("site 0, k>0",                 0, 1, true, false),
        ("site 0, k<0",                -1, 0, true, false),
        ("site k, k>0",                 1, 0, false, true),
        ("site k, k<0",                 0, -1, false, true),
        ("site 0 = site k, k=0",        0, 0, true, true),
    ];
    let mut grand_cells = 0u64;
    let mut grand_cfg = 0u64;
    let mut grand_bad = 0u64;
    for (name, fl, fr, v_arr, v_dep) in sites {
        let mut cells = 0u64;
        let mut cfg = 0u64;
        let mut bad = 0u64;
        let mut shown = 0;
        for eps in [1i64, -1] {
            for delta in [0i64, 1] {
                if !v_dep && (eps != 1 || delta != 0) {
                    continue; // no virtual departure: (eps,delta) is not a parameter
                }
                let vd = if v_dep {
                    Some((if delta == 1 { 2usize } else { 0usize }) + (if eps == 1 { 0 } else { 1 }))
                } else {
                    None
                };
                let mut al = -amax;
                while al <= amax {
                    if (al - fl).rem_euclid(2) != 0 { al += 1; continue; }
                    let mut ar = -amax;
                    while ar <= amax {
                        if (ar - fr).rem_euclid(2) != 0 { ar += 1; continue; }
                        // alpha, beta with the virtual events folded in
                        let mut alpha = al;
                        let mut beta = ar;
                        if v_arr { alpha -= 1; }            // arrival (left,+)
                        if let Some(c) = vd {
                            let sgn = if c % 2 == 0 { 1 } else { -1 };
                            if c < 2 { alpha += sgn; } else { beta -= sgn; }
                        }
                        let target = alpha.abs().max(beta.abs());
                        let mut seen_any = false;
                        let mut minv = INF;
                        for il in 0..=lam {
                            let ml = al.abs().max(fl.abs()) + 2 * il;
                            for ir in 0..=lam {
                                let mr = ar.abs().max(fr.abs()) + 2 * ir;
                                let el0 = Edge { a: al, f: fl, m: ml, pu: 0 };
                                let er0 = Edge { a: ar, f: fr, m: mr, pu: 0 };
                                for pul in 0..=el0.u().max(0) {
                                    for pur in 0..=er0.u().max(0) {
                                        let el = Edge { a: al, f: fl, m: ml, pu: pul };
                                        let er = Edge { a: ar, f: fr, m: mr, pu: pur };
                                        if let Some((arr, dep)) = site_vectors(&el, &er, v_arr, vd) {
                                            if let Some(c) = mincost(&arr, &dep) {
                                                cfg += 1;
                                                seen_any = true;
                                                minv = minv.min(c);
                                                // the strong claim: EVERY (m, split) already
                                                // realises exactly max(|alpha|,|beta|)
                                                if c != target {
                                                    bad += 1;
                                                    if shown < 6 {
                                                        shown += 1;
                                                        println!("   MISS {} eps={} delta={} aL={} aR={} mL={} mR={} puL={} puR={} cost={} target={}",
                                                                 name, eps, delta, al, ar, ml, mr, pul, pur, c, target);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if seen_any { cells += 1; let _ = minv; }
                        ar += 1;
                    }
                    al += 1;
                }
            }
        }
        println!("[universal] {:26} cells={:6} configurations={:9} exceptions={}", name, cells, cfg, bad);
        grand_cells += cells; grand_cfg += cfg; grand_bad += bad;
    }
    println!("[universal] TOTAL cells={} configurations={} exceptions={}", grand_cells, grand_cfg, grand_bad);
    println!("[universal] VERDICT: {}",
        if grand_bad == 0 {
            "Site = max(|alpha|,|beta|) for EVERY crossing count and EVERY sign split -- 0 exceptions"
        } else { "EXCEPTIONS FOUND" });
}


// ---------------------------------------------------------------------------
// Mode: hypothesis deletion.  Each hypothesis of the site-cost theorem is
// removed in turn and the law is re-tested; a hypothesis that is necessary
// must produce a counterexample.
// ---------------------------------------------------------------------------
fn law_holds_interior(amax: i64, lam: i64, allow_a_below_f: bool) -> (u64, u64, String) {
    let mut n = 0u64;
    let mut bad = 0u64;
    let mut first = String::new();
    for f in [-1i64, 0, 1] {
        let mut al = -amax;
        while al <= amax {
            if (al - f).rem_euclid(2) != 0 { al += 1; continue; }
            if !allow_a_below_f && al.abs() < f.abs() { al += 1; continue; }
            let mut ar = -amax;
            while ar <= amax {
                if (ar - f).rem_euclid(2) != 0 { ar += 1; continue; }
                if !allow_a_below_f && ar.abs() < f.abs() { ar += 1; continue; }
                let target = al.abs().max(ar.abs());
                for il in 0..=lam {
                    let ml = al.abs().max(f.abs()) + 2 * il;
                    for ir in 0..=lam {
                        let mr = ar.abs().max(f.abs()) + 2 * ir;
                        let el0 = Edge { a: al, f, m: ml, pu: 0 };
                        let er0 = Edge { a: ar, f, m: mr, pu: 0 };
                        for pul in 0..=el0.u().max(0) {
                            for pur in 0..=er0.u().max(0) {
                                let el = Edge { a: al, f, m: ml, pu: pul };
                                let er = Edge { a: ar, f, m: mr, pu: pur };
                                if let Some((arr, dep)) = site_vectors(&el, &er, false, None) {
                                    if let Some(c) = mincost(&arr, &dep) {
                                        n += 1;
                                        if c != target {
                                            bad += 1;
                                            if first.is_empty() {
                                                first = format!("aL={} aR={} f={} mL={} mR={} puL={} puR={} cost={} target={}",
                                                                al, ar, f, ml, mr, pul, pur, c, target);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                ar += 1;
            }
            al += 1;
        }
    }
    (n, bad, first)
}

fn set_cw(b: i64, s: i64, p: i64) {
    CW[0].store(b, std::sync::atomic::Ordering::Relaxed);
    CW[1].store(s, std::sync::atomic::Ordering::Relaxed);
    CW[2].store(p, std::sync::atomic::Ordering::Relaxed);
}

fn mode_delete(amax: i64, lam: i64) {
    println!("[delete] hypothesis deletions, |a| <= {}, m up to minimal+{}", amax, 2 * lam);
    let base = [(0i64, 2i64, 1i64)];
    for &(b, sg, p) in base.iter() {
        set_cw(b, sg, p);
        let (n, bad, ex) = law_holds_interior(amax, lam, false);
        println!("  H0 model as stated              (bounce,flip,pass)=({},{},{}): {} configs, {} exceptions {}", b, sg, p, n, bad, ex);
    }
    // H1: the sign-flip bounce costs 2 -- delete by changing its value
    for sg in [0i64, 1, 3, 4] {
        set_cw(0, sg, 1);
        let (n, bad, ex) = law_holds_interior(amax, lam, false);
        println!("  H1 delete: flip cost 2 -> {}      : {} configs, {} exceptions   first: {}", sg, n, bad, ex);
    }
    // H2: the pass costs 1
    for p in [0i64, 2, 3] {
        set_cw(0, 2, p);
        let (n, bad, ex) = law_holds_interior(amax, lam, false);
        println!("  H2 delete: pass cost 1 -> {}      : {} configs, {} exceptions   first: {}", p, n, bad, ex);
    }
    // H3: the same-sign bounce is free
    for b in [1i64, 2] {
        set_cw(b, 2, 1);
        let (n, bad, ex) = law_holds_interior(amax, lam, false);
        println!("  H3 delete: bounce cost 0 -> {}    : {} configs, {} exceptions   first: {}", b, n, bad, ex);
    }
    // H4: the constraint |a| >= |f| (automatic in the model: bulk deposits are
    // even with f=0, travel deposits odd with f=+-1).  Delete it by admitting
    // an edge with f=+-1 and a=0, which the model never produces.
    set_cw(0, 2, 1);
    {
        let mut bad = 0u64;
        let mut n = 0u64;
        let mut first = String::new();
        for f in [-1i64, 1] {
            for al in [-2i64, 0, 2] {
                for ar in [-2i64, 0, 2] {
                    // a even while f is odd: parity is broken too, so use m >= |f|
                    for ml in [f.abs().max(al.abs()), f.abs().max(al.abs()) + 2] {
                        for mr in [f.abs().max(ar.abs()), f.abs().max(ar.abs()) + 2] {
                            let el0 = Edge { a: al, f, m: ml, pu: 0 };
                            let er0 = Edge { a: ar, f, m: mr, pu: 0 };
                            for pul in 0..=el0.u().max(0) {
                                for pur in 0..=er0.u().max(0) {
                                    let el = Edge { a: al, f, m: ml, pu: pul };
                                    let er = Edge { a: ar, f, m: mr, pu: pur };
                                    if let Some((arr, dep)) = site_vectors(&el, &er, false, None) {
                                        if let Some(c) = mincost(&arr, &dep) {
                                            n += 1;
                                            let t = al.abs().max(ar.abs());
                                            if c != t {
                                                bad += 1;
                                                if first.is_empty() {
                                                    first = format!("aL={} aR={} f={} mL={} mR={} cost={} target={}",
                                                                    al, ar, f, ml, mr, c, t);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        println!("  H4 delete: |a| >= |f| (a even with f=+-1): {} configs, {} exceptions   first: {}", n, bad, first);
    }
    set_cw(0, 2, 1);
}


// ---------------------------------------------------------------------------
// Mode: the shield law (M2).  Bulk configurations with k = 0 (no travel
// interval): deposits are even and sum to zero, the marker carries both virtual
// events at site 0.  For every configuration the relaxed length and the
// connectivity defect c are computed by exhaustive enumeration of realizations
// (every sign split, every site bijection) and compared with the closed forms
//     l_R    = sum_j m_j + sum_s max(|alpha_s|,|beta_s|,|Phi_s|)
//     c      = #{ interior sites s with alpha_s = beta_s = Phi_s = 0 }
// the second of which is the shield law: an interior gap run of length L has
// exactly L-1 such sites, so it contributes L-1.
// ---------------------------------------------------------------------------
fn mode_shield(nmax: usize, amax: i64) {
    let mut tested = 0u64;
    let mut bad_len = 0u64;
    let mut bad_c = 0u64;
    let mut shown = 0;
    let mut maxrun = 0usize;
    // deposit alphabet: even, |a| <= amax, including 0 (gap)
    let alpha_set: Vec<i64> = {
        let mut v = vec![];
        let mut a = -amax;
        while a <= amax { v.push(a); a += 2; }
        v
    };
    for n in 1..=nmax {
        // positions lo..lo+n-1, marker site 0 anywhere in lo..lo+n
        for lo in -(n as i64)..=0 {
            let hi = lo + n as i64;
            if 0 < lo || 0 > hi { continue; }
            // deposits
            let mut idx = vec![0usize; n];
            loop {
                let a: Vec<i64> = (0..n).map(|i| alpha_set[idx[i]]).collect();
                // the outermost edges must carry deposits (else the span is smaller)
                let ok_span = a[0] != 0 && a[n - 1] != 0;
                let ok_bal = a.iter().sum::<i64>() == 0;
                if ok_span && ok_bal {
                    for eps in [1i64, -1] {
                        for delta in [0i64, 1] {
                            let vd_class = (if delta == 1 { 2usize } else { 0usize })
                                + (if eps == 1 { 0 } else { 1 });
                            let site0 = (0 - lo) as usize; // index of site 0 among lo..hi
                            // crossing counts
                            let m: Vec<i64> = a.iter().map(|&x| if x == 0 { 2 } else { x.abs() }).collect();
                            // closed-form predictions
                            let mut pred_len: i64 = m.iter().sum();
                            let mut pred_c: i64 = 0;
                            for si in 0..=n {
                                let al = if si == 0 { 0 } else { a[si - 1] };
                                let ar = if si == n { 0 } else { a[si] };
                                let mut alpha = al;
                                let mut beta = ar;
                                let mut phi = 0i64; // f = 0 in the bulk
                                if si == site0 {
                                    alpha -= 1; phi += 1;
                                    if vd_class < 2 {
                                        alpha += if vd_class == 0 { 1 } else { -1 };
                                        phi -= 1;
                                    } else {
                                        beta -= if vd_class == 2 { 1 } else { -1 };
                                    }
                                }
                                pred_len += alpha.abs().max(beta.abs()).max(phi.abs());
                                if si > 0 && si < n && alpha == 0 && beta == 0 && phi == 0 {
                                    pred_c += 1;
                                }
                            }
                            // exhaustive enumeration over the sign splits
                            let mut best_cost = i64::MAX;
                            let mut best_cyc = i64::MAX;
                            let mut splits = vec![0usize; n];
                            loop {
                                let mut edges = Vec::with_capacity(n);
                                let mut feasible = true;
                                for i in 0..n {
                                    let u = (m[i] / 2) as usize;
                                    let dn = u;
                                    let pu = splits[i];
                                    let pdi = pu as i64 + a[i] / 2;
                                    if pu > u || pdi < 0 || pdi > dn as i64 { feasible = false; break; }
                                    edges.push(realize::Edge { a: a[i], m: m[i], u, dn, pu, pd: pdi as usize });
                                }
                                if feasible {
                                    let tbl = realize::enumerate(&edges, Some(site0), Some((site0, vd_class)));
                                    for (&cst, &cyc) in tbl.iter() {
                                        if cst < best_cost || (cst == best_cost && cyc < best_cyc) {
                                            if cst < best_cost { best_cost = cst; best_cyc = cyc; }
                                            else { best_cyc = best_cyc.min(cyc); }
                                        }
                                    }
                                }
                                // advance splits
                                let mut i = 0;
                                loop {
                                    if i == n { break; }
                                    splits[i] += 1;
                                    if splits[i] <= (m[i] / 2) as usize { break; }
                                    splits[i] = 0; i += 1;
                                }
                                if i == n { break; }
                            }
                            if best_cost == i64::MAX { continue; }
                            best_cost += m.iter().sum::<i64>(); // enumerate() returns site costs only
                            tested += 1;
                            // longest interior gap run exercised
                            let mut run = 0usize;
                            for i in 0..n {
                                if a[i] == 0 { run += 1; maxrun = maxrun.max(run); } else { run = 0; }
                            }
                            if best_cost != pred_len {
                                bad_len += 1;
                                if shown < 8 { shown += 1;
                                    println!("   LEN a={:?} lo={} eps={} delta={} true={} pred={}", a, lo, eps, delta, best_cost, pred_len); }
                            }
                            if best_cyc != pred_c {
                                bad_c += 1;
                                if shown < 8 { shown += 1;
                                    println!("   CYC a={:?} lo={} eps={} delta={} true_c={} pred_c={}", a, lo, eps, delta, best_cyc, pred_c); }
                            }
                        }
                    }
                }
                // advance deposits
                let mut i = 0;
                loop {
                    if i == n { break; }
                    idx[i] += 1;
                    if idx[i] < alpha_set.len() { break; }
                    idx[i] = 0; i += 1;
                }
                if i == n { break; }
            }
        }
    }
    println!("[shield] bulk configurations with k=0, up to {} edges, even deposits |a| <= {}, all four marker data",
             nmax, amax);
    println!("[shield] {} configurations enumerated exhaustively (every sign split, every site bijection); longest gap run exercised = {}", tested, maxrun);
    println!("[shield] relaxed-length closed-form exceptions: {}", bad_len);
    println!("[shield] defect closed-form (shield law) exceptions: {}", bad_c);
    println!("[shield] VERDICT: {}", if bad_len == 0 && bad_c == 0 {
        "l_R = sum m + sum max(|alpha|,|beta|,|Phi|) and c = #closed interior sites -- 0 exceptions"
    } else { "EXCEPTIONS FOUND" });
}


fn mode_dbg() {
    // a = [4,-4] at positions -2,-1 ; marker site 0 = site index 2 ; eps=1, delta=0
    let a = vec![4i64, -4];
    let m = vec![4i64, 4];
    let n = 2usize;
    let site0 = 2usize;
    let vd = 0usize;
    for pu0 in 0..=2usize {
        for pu1 in 0..=2usize {
            let pd0 = pu0 as i64 + a[0] / 2;
            let pd1 = pu1 as i64 + a[1] / 2;
            if pd0 < 0 || pd0 > 2 || pd1 < 0 || pd1 > 2 { continue; }
            let edges = vec![
                realize::Edge { a: a[0], m: m[0], u: 2, dn: 2, pu: pu0, pd: pd0 as usize },
                realize::Edge { a: a[1], m: m[1], u: 2, dn: 2, pu: pu1, pd: pd1 as usize },
            ];
            let tbl = realize::enumerate(&edges, Some(site0), Some((site0, vd)));
            let mut ks: Vec<i64> = tbl.keys().cloned().collect();
            ks.sort();
            println!("  split pu=({},{}) pd=({},{}) : cost->cycles {:?}", pu0, pu1, pd0, pd1,
                     ks.iter().map(|k| (*k, tbl[k])).collect::<Vec<_>>());
        }
    }
    let _ = n;
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("all");
    if env::var("SITECOST_DUAL").is_ok() {
        DUAL.store(true, std::sync::atomic::Ordering::Relaxed);
        println!("[dual] every site cost is computed by BOTH exact solvers; disagreement aborts");
    }
    let p1: i64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(12);
    let p2: i64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(3);
    match mode {
        "xcheck" => mode_xcheck(p1),
        "interior" => mode_interior(p1, p2),
        "marker" => mode_marker(p1, p2),
        "universal" => mode_universal(p1, p2),
        "delete" => mode_delete(p1, p2),
        "shield" => mode_shield(p1 as usize, p2),
        "dbg" => mode_dbg(),
        "probe" => { let p3: i64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(1); probe(p1, 0, p2, p3, true, None, 3); }
        _ => {
            mode_xcheck(4);
            mode_interior(12, 3);
            mode_marker(12, 3);
            mode_universal(12, 3);
        }
    }
}

// probe: print the exact matching data and cost for one cell
#[allow(dead_code)]
fn probe(al: i64, fl: i64, ar: i64, fr: i64, virt_arr: bool, vd: Option<usize>, lam: i64) {
    let mut best = INF;
    for il in 0..=lam {
        let ml = al.abs().max(fl.abs()) + 2 * il;
        for ir in 0..=lam {
            let mr = ar.abs().max(fr.abs()) + 2 * ir;
            let el0 = Edge { a: al, f: fl, m: ml, pu: 0 };
            let er0 = Edge { a: ar, f: fr, m: mr, pu: 0 };
            for pul in 0..=el0.u().max(0) {
                for pur in 0..=er0.u().max(0) {
                    let el = Edge { a: al, f: fl, m: ml, pu: pul };
                    let er = Edge { a: ar, f: fr, m: mr, pu: pur };
                    if let Some((arr, dep)) = site_vectors(&el, &er, virt_arr, vd) {
                        if let Some(c) = mincost(&arr, &dep) {
                            if c <= best {
                                println!("   mL={} mR={} puL={} puR={} arr={:?} dep={:?} cost={}", ml, mr, pul, pur, arr, dep, c);
                            }
                            best = best.min(c);
                        }
                    }
                }
            }
        }
    }
    println!("  probe(aL={},fL={},aR={},fR={}) min = {}", al, fl, ar, fr, best);
}
