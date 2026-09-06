// lipschitz_check -- is the potential  Phi = lR + 2c  1-Lipschitz along generators?
//
// The lower half of  wordLength = lR + 2c  is open.  Proposed attack: if Phi moves by
// at most 1 under every generator, induction on `Reaches` gives
// wordLength g >= Phi g - Phi one.  This measures the max jump, on four candidate
// (lR, c) pairs, because they are NOT the same object:
//
//   span LEAN  -- SiteCost.PathData as EltBridge.Elt.toPathData builds it.  `hA : A<=0`
//                 and `hB : 0<=B` force edge 0 into the span ALWAYS.
//   span NOGAP -- src/main.rs's `span`: the OCCUPIED edges only.  This is the model
//                 that has been checked against BFS word length.
//   c interior -- #{s : A < s < B+1, alpha=beta=Phi=0}   (= `pdCutSites`.card = Elt.c)
//   c +BS      -- interior, plus main.rs's hand-added boundary-shield site.
//
// All integer arithmetic; no floating point outside the ETA display.

use std::collections::HashMap;
use std::io::Write;
use std::time::Instant;

type Lamps = Vec<(i32, i32)>; // sorted by edge, non-zero values only

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }   // dl == 0  <->  delta = false

#[inline]
fn travel(k: i32, j: i32) -> i32 {
    if 0 <= j && j < k { 1 } else if k <= j && j < 0 { -1 } else { 0 }
}
#[inline]
fn dep(l: &Lamps, j: i32) -> i32 {
    match l.binary_search_by_key(&j, |&(x, _)| x) { Ok(i) => l[i].1, Err(_) => 0 }
}

/// Lean's span: A = min occ, B = max occ, occ = {0} u {j : d j /= 0 or travel /= 0}.
fn span_lean(e: &Elt) -> (i32, i32) {
    let (mut a, mut b) = (0i32, 0i32);
    for &(j, v) in &e.lamps { if v != 0 { a = a.min(j); b = b.max(j); } }
    if e.k > 0 { b = b.max(e.k - 1); }
    if e.k < 0 { a = a.min(e.k); }
    (a, b)
}

/// nogap's span: the occupied edges alone (edge 0 is NOT forced in).  Returns (A, B).
fn span_nogap(e: &Elt) -> (i32, i32) {
    let (mut lo, mut hi) = (0.min(e.k), 0.max(e.k));   // hi is one PAST the last edge
    for &(j, v) in &e.lamps { if v != 0 { lo = lo.min(j); hi = hi.max(j + 1); } }
    if e.k > 0 { lo = lo.min(0); hi = hi.max(e.k); }
    if e.k < 0 { lo = lo.min(e.k); hi = hi.max(0); }
    (lo, hi - 1)
}

/// (alpha_s, beta_s, Phi_s) exactly as Realisation.lean defines them.
fn abphi(e: &Elt, s: i32) -> (i32, i32, i32) {
    let varr = if s == 0 { 1 } else { 0 };
    let vd = if s == e.k { 1 } else { 0 };
    let (vl, vr) = if e.dl == 0 { (vd, 0) } else { (0, vd) };
    let eps = e.eps as i32;
    (dep(&e.lamps, s - 1) - varr + eps * vl,
     dep(&e.lamps, s) - eps * vr,
     travel(e.k, s - 1) + varr - vl)
}

fn mu(e: &Elt, j: i32) -> i64 {
    let (d, f) = (dep(&e.lamps, j), travel(e.k, j));
    if d == 0 && f == 0 { 2 } else { d.abs().max(f.abs()) as i64 }
}

/// lR over the span [a,b]: edge sum on a..=b, site sum on a..=b+1.
fn lr_on(e: &Elt, a: i32, b: i32) -> i64 {
    let mut t: i64 = 0;
    for j in a..=b { t += mu(e, j); }
    for s in a..=b + 1 {
        let (al, be, _) = abphi(e, s);
        t += al.abs().max(be.abs()) as i64;
    }
    t
}

fn is_cut(e: &Elt, s: i32) -> bool {
    let (al, be, ph) = abphi(e, s);
    al == 0 && be == 0 && ph == 0
}

/// cut sites strictly interior to [a, b+1]; `bs` adds main.rs's boundary-shield site.
fn cuts_on(e: &Elt, a: i32, b: i32, bs: bool) -> i64 {
    let mut n = 0i64;
    for s in a + 1..b + 1 { if is_cut(e, s) { n += 1; } }
    if bs && e.k == 0 && e.dl == 0 && a == 0 && b + 1 > 0 && is_cut(e, 0) { n += 1; }
    n
}

const NP: usize = 4;
const NAMES: [&str; NP] = ["lean  (Elt.lR + 2*Elt.c)", "nogap (span=occ, interior c)",
                           "nogapBS (span=occ, c=|Z| of main.rs)", "leanBS (lean span, c+BS)"];

#[derive(Clone, Copy)]
struct Stats { lr: [i64; 2], c: [i64; NP], phi: [i64; NP] }

fn stats(e: &Elt) -> Stats {
    let (al, bl) = span_lean(e);
    let (an, bn) = span_nogap(e);
    let lr = [lr_on(e, al, bl), lr_on(e, an, bn)];
    let c = [cuts_on(e, al, bl, false), cuts_on(e, an, bn, false),
             cuts_on(e, an, bn, true), cuts_on(e, al, bl, true)];
    let phi = [lr[0] + 2 * c[0], lr[1] + 2 * c[1], lr[1] + 2 * c[2], lr[0] + 2 * c[3]];
    Stats { lr, c, phi }
}

fn size(e: &Elt) -> i64 {
    e.k.abs() as i64 + e.lamps.iter().map(|&(_, v)| v.abs() as i64).sum::<i64>()
}

fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}

fn gens(e: &Elt) -> [Elt; 3] {
    [Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     if e.dl == 0 {
        Elt { eps: e.eps, dl: 1, k: e.k - 1, lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) }
     } else {
        Elt { eps: e.eps, dl: 0, k: e.k + 1, lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) }
     }]
}

fn show(e: &Elt) -> String {
    format!("k={} eps={} delta={} d={:?}", e.k, e.eps,
            if e.dl == 0 { "false" } else { "true" }, e.lamps)
}
fn showstats(s: &Stats) -> String {
    format!("lR_lean={} lR_nogap={} | c: lean={} nogap={} nogapBS={} leanBS={} | \
             Phi: lean={} nogap={} nogapBS={} leanBS={}",
            s.lr[0], s.lr[1], s.c[0], s.c[1], s.c[2], s.c[3],
            s.phi[0], s.phi[1], s.phi[2], s.phi[3])
}

/// Worst jump for one potential, keeping the SMALLEST witness at that jump.
struct Worst { max: i64, wsize: i64, wit: Option<(Elt, usize, Stats, Stats)> }
impl Worst {
    fn new() -> Self { Worst { max: 0, wsize: i64::MAX, wit: None } }
    fn see(&mut self, g: &Elt, i: usize, sg: Stats, sh: Stats, jump: i64) {
        let sz = size(g);
        if jump > self.max || (jump == self.max && jump > 1 && sz < self.wsize) {
            self.max = jump; self.wsize = sz; self.wit = Some((g.clone(), i, sg, sh));
        }
    }
    fn report(&self, name: &str) {
        println!("  max |dPhi| = {:<2}  [{}]", self.max, name);
        if let Some((g, i, sg, sh)) = &self.wit {
            println!("      witness  s{}  on  {}", i + 1, show(g));
            println!("        before {}", showstats(sg));
            println!("        after  {}", showstats(sh));
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let depth: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(18);
    let cap: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(12_000_000);
    let w: i32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(3);
    let dmax: i32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(4);
    let kmax: i32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(4);

    eprintln!("[lip] BFS depth {depth}, element cap {cap}");
    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    println!("identity:  {}", showstats(&stats(&ident)));

    let mut dist: HashMap<Elt, u8> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident.clone()];
    let t0 = Instant::now();
    let mut reached = 0u32;
    for d in 0..depth {
        let mut next = Vec::new();
        for e in &frontier {
            for c in gens(e) {
                if !dist.contains_key(&c) { dist.insert(c.clone(), (d + 1) as u8); next.push(c); }
            }
        }
        frontier = next;
        reached = d + 1;
        eprintln!("[lip] layer {:2}/{}: frontier {:>10}  total {:>11}  {:6.1}s",
                  d + 1, depth, frontier.len(), dist.len(), t0.elapsed().as_secs_f64());
        std::io::stderr().flush().ok();
        if dist.len() > cap { eprintln!("[lip] element cap hit; BFS stopped at depth {reached}"); break; }
    }
    let complete = reached.saturating_sub(1);

    // ---- 1. the metric identity wordLength = lR + 2c, on complete layers ----
    let mut bad = [0u64; NP];
    let mut firstbad: [Option<(Elt, u8, Stats)>; NP] = [None, None, None, None];
    let mut firstsz = [i64::MAX; NP];
    let (mut ctrue_lean_bad, mut ctrue_nogap_bad) = (0u64, 0u64);   // c cross-validation
    let mut parity_bad = 0u64;
    let mut used = 0u64;
    let mut maxc = [0i64; NP];
    let mut dmin = [i64::MAX; NP];
    let mut dmax_ = [i64::MIN; NP];
    for (e, &lt) in &dist {
        if lt as u32 > complete { continue; }
        let s = stats(e);
        used += 1;
        for p in 0..NP {
            maxc[p] = maxc[p].max(s.c[p]);
            let dv = s.phi[p] - lt as i64;
            dmin[p] = dmin[p].min(dv); dmax_[p] = dmax_[p].max(dv);
            if s.phi[p] != lt as i64 {
                bad[p] += 1;
                if size(e) < firstsz[p] { firstsz[p] = size(e); firstbad[p] = Some((e.clone(), lt, s)); }
            }
        }
        // c cross-validation: the defect statistic (l_T - l_R)/2 vs the cut-site count
        let dn = lt as i64 - s.lr[1];
        let dl_ = lt as i64 - s.lr[0];
        if dn < 0 || dn % 2 != 0 { parity_bad += 1; } else if dn / 2 != s.c[2] { ctrue_nogap_bad += 1; }
        if dl_ < 0 || dl_ % 2 != 0 { } else if dl_ / 2 != s.c[0] { ctrue_lean_bad += 1; }
    }
    println!("\n[lip] BFS reached depth {reached}; identity checked on layers 0..{complete} \
              ({used} elements; {} enumerated)", dist.len());
    for p in 0..NP {
        println!("  wordLength == lR + 2c  [{}] : {} violations (max c = {}); Phi - wordLength in [{}, {}]",
                 NAMES[p], bad[p], maxc[p], dmin[p], dmax_[p]);
        if let Some((e, lt, s)) = &firstbad[p] {
            println!("      smallest witness: wl={lt}  {}", show(e));
            println!("        {}", showstats(s));
        }
    }
    println!("  c cross-validation ((l_T-l_R)/2 vs cut count): nogapBS {} mismatches, \
              lean(Elt.c) {} mismatches; parity/negativity failures (nogap lR) {}",
             ctrue_nogap_bad, ctrue_lean_bad, parity_bad);

    // ---- 1b. what the boundary-shield term actually is ----
    // Claim: main.rs's BS site fires exactly on  kstar = 0, eps = +1, delta = false,
    // d j = 0 for all j <= 0, and d j /= 0 for some j >= 1.
    let (mut bs_fires, mut bs_pred, mut bs_disagree) = (0u64, 0u64, 0u64);
    for e in dist.keys() {
        let (an, bn) = span_nogap(e);
        let fires = cuts_on(e, an, bn, true) > cuts_on(e, an, bn, false);
        let pred = e.k == 0 && e.eps == 1 && e.dl == 0
            && e.lamps.iter().all(|&(j, v)| v == 0 || j >= 1)
            && e.lamps.iter().any(|&(j, v)| v != 0 && j >= 1);
        if fires { bs_fires += 1; }
        if pred { bs_pred += 1; }
        if fires != pred { bs_disagree += 1; }
    }
    println!("  boundary-shield term: fires on {bs_fires} elements; the characterisation \
              (kstar=0, eps=+1, delta=false, no deposit at j<=0, some deposit at j>=1) \
              holds on {bs_pred}; disagreements {bs_disagree}");

    // ---- 2. Lipschitz on the BFS ball ----
    let mut wb: Vec<Worst> = (0..NP).map(|_| Worst::new()).collect();
    for e in dist.keys() {
        let sg = stats(e);
        for (i, h) in gens(e).iter().enumerate() {
            let sh = stats(h);
            for p in 0..NP { wb[p].see(e, i, sg, sh, (sh.phi[p] - sg.phi[p]).abs()); }
        }
    }
    println!("\n[lip] Lipschitz on the BFS ball ({} elements):", dist.len());
    for p in 0..NP { wb[p].report(NAMES[p]); }
    drop(dist);

    // ---- 3. exhaustive structural sweep, no reachability assumed ----
    eprintln!("[lip] exhaustive sweep: edges [-{w},{}], |d| <= {dmax}, |k| <= {kmax}", w - 1);
    let edges: Vec<i32> = (-w..w).collect();
    let mut ws: Vec<Worst> = (0..NP).map(|_| Worst::new()).collect();
    let mut total: u64 = 0;
    for k in -kmax..=kmax {
        let choices: Vec<Vec<i32>> = edges.iter().map(|&j| {
            let par = ((travel(k, j) % 2) + 2) % 2;
            (-dmax..=dmax).filter(|v| ((v % 2) + 2) % 2 == par).collect()
        }).collect();
        let sizes: Vec<usize> = choices.iter().map(|c| c.len()).collect();
        let ncomb: u64 = sizes.iter().map(|&s| s as u64).product();
        for idx in 0..ncomb {
            let mut rem = idx;
            let mut lamps: Lamps = Vec::new();
            for (p, &j) in edges.iter().enumerate() {
                let v = choices[p][(rem % sizes[p] as u64) as usize];
                rem /= sizes[p] as u64;
                if v != 0 { lamps.push((j, v)); }
            }
            for eps in [1i8, -1i8] {
                for dl in [0u8, 1u8] {
                    let e = Elt { eps, dl, k, lamps: lamps.clone() };
                    let sg = stats(&e);
                    for (i, h) in gens(&e).iter().enumerate() {
                        let sh = stats(h);
                        for p in 0..NP { ws[p].see(&e, i, sg, sh, (sh.phi[p] - sg.phi[p]).abs()); }
                    }
                    total += 1;
                }
            }
        }
        eprintln!("[lip]   k={k} done, {total} elements, {:6.1}s", t0.elapsed().as_secs_f64());
    }
    println!("\n[lip] Lipschitz on the exhaustive sweep ({total} elements, no reachability assumed):");
    for p in 0..NP { ws[p].report(NAMES[p]); }
}
