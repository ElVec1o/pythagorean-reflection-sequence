// truelen_check -- is the UPPER half of the metric identity, wordLength <= lR + 2c,
// actually true on the group?  BFS from `one` over Elt (same generator rules as
// reach_check.rs / ../src/main.rs), and for every element reached compute lR and c
// exactly as Realisation.lean / EltBridge.lean define them:
//
//   travel k j = 1 for 0<=j<k, -1 for k<=j<0, 0 otherwise
//   occ        = {0} u {j : d j /= 0 or travel /= 0};  A = min occ, B = max occ
//   mu j       = 2 if d j = 0 and travel = 0, else max(|d j|,|travel|)
//   alpha s    = d(s-1) - [s=0] + eps*vL s        vL s = [delta=0][s=k]
//   beta  s    = d s     - eps*vR s               vR s = [delta=1][s=k]
//   Phi   s    = travel(s-1) + [s=0] - vL s
//   siteCost s = max(|alpha|,|beta|)
//   lR         = sum_{j in [A,B]} mu j + sum_{s in [A,B+1]} siteCost s
//   c          = #{s in (A,B] : alpha=beta=Phi=0}
//
// The LOWER half of the identity is open mathematics (paper's "what is not claimed"
// remark); nothing here touches it.  This only asks whether the upper half has any
// counterexample, and how much slack it carries.

use std::collections::HashMap;

type Lamps = Vec<(i32, i32)>;
#[derive(Clone, PartialEq, Eq, Hash)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }

fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}

fn gensl(e: &Elt) -> [(&'static str, Elt); 3] {
    let g = gens(e);
    [("s1", g[0].clone()), ("s2", g[1].clone()), ("s3", g[2].clone())]
}

fn gens(e: &Elt) -> [Elt; 3] {
    let s1 = Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() };
    let s2 = Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() };
    let s3 = if e.dl == 0 {
        Elt { eps: e.eps, dl: 1, k: e.k - 1, lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) }
    } else {
        Elt { eps: e.eps, dl: 0, k: e.k + 1, lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) }
    };
    [s1, s2, s3]
}

fn dep(l: &Lamps, j: i32) -> i32 {
    match l.binary_search_by_key(&j, |&(x, _)| x) { Ok(i) => l[i].1, Err(_) => 0 }
}
fn travel(k: i32, j: i32) -> i32 {
    if 0 <= j && j < k { 1 } else if k <= j && j < 0 { -1 } else { 0 }
}

fn gapcount(e: &Elt) -> i64 {
    let mut a = 0i32; let mut b = 0i32;
    for &(j, v) in e.lamps.iter() { if v != 0 { if j < a { a = j; } if j > b { b = j; } } }
    if e.k > 0 { if e.k - 1 > b { b = e.k - 1; } } else if e.k < 0 { if e.k < a { a = e.k; } }
    let mut g = 0i64;
    for j in a..=b { if dep(&e.lamps, j) == 0 && travel(e.k, j) == 0 { g += 1; } }
    g
}

// (lR, c, A, B)
fn lr_and_c(e: &Elt) -> (i64, i64, i32, i32) {
    let mut a = 0i32; let mut b = 0i32;
    for &(j, v) in e.lamps.iter() { if v != 0 { if j < a { a = j; } if j > b { b = j; } } }
    // travel support: [0,k) for k>0, [k,0) for k<0
    if e.k > 0 { if e.k - 1 > b { b = e.k - 1; } } else if e.k < 0 { if e.k < a { a = e.k; } }
    let eps = e.eps as i32;
    let vl = |s: i32| -> i32 { if e.dl == 0 && s == e.k { 1 } else { 0 } };
    let vr = |s: i32| -> i32 { if e.dl == 1 && s == e.k { 1 } else { 0 } };
    let alpha = |s: i32| -> i32 { dep(&e.lamps, s - 1) - if s == 0 { 1 } else { 0 } + eps * vl(s) };
    let beta  = |s: i32| -> i32 { dep(&e.lamps, s) - eps * vr(s) };
    let phi   = |s: i32| -> i32 { travel(e.k, s - 1) + if s == 0 { 1 } else { 0 } - vl(s) };
    let mut lr = 0i64;
    for j in a..=b {
        let d = dep(&e.lamps, j); let t = travel(e.k, j);
        lr += if d == 0 && t == 0 { 2 } else { d.abs().max(t.abs()) } as i64;
    }
    for s in a..=(b + 1) { lr += alpha(s).abs().max(beta(s).abs()) as i64; }
    let mut c = 0i64;
    for s in (a + 1)..=b { if alpha(s) == 0 && beta(s) == 0 && phi(s) == 0 { c += 1; } }
    (lr, c, a, b)
}

fn show(name: &str, e: &Elt, wl: Option<u32>) {
    let (lr, c, a, b) = lr_and_c(e);
    println!("  {name:8}: kstar={:3} eps={:2} delta={} d={:?} A={a} B={b}  lR={lr} c={c} lR+2c={}  wordLength={}",
        e.k, e.eps, e.dl, e.lamps, lr + 2 * c,
        wl.map(|x| x.to_string()).unwrap_or("?".into()));
}

fn main() {
    let depth: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(13);
    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    let mut dist: HashMap<Elt, u32> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut parent: HashMap<Elt, (Elt, &'static str)> = HashMap::new();
    let mut frontier = vec![ident.clone()];
    let mut hist: HashMap<(bool, i64), u64> = HashMap::new();
    let mut total = 0u64;
    let mut shown_up = 0u32;
    let mut shown_dn = 0u32;
    let mut record = |e: &Elt, wl: u32, hist: &mut HashMap<(bool, i64), u64>,
                      total: &mut u64, shown_up: &mut u32, shown_dn: &mut u32| {
        let (lr, c, _, _) = lr_and_c(e);
        *total += 1;
        // delta = wordLength - (lR + 2c); >0 means the UPPER bound holds strictly,
        // <0 means the upper bound FAILS.
        let dd = wl as i64 - (lr + 2 * c);
        *hist.entry((gapcount(e) > 0, dd)).or_insert(0) += 1;
        if dd < 0 && *shown_up < 6 { *shown_up += 1; show("SLACK(lo-fail)", e, Some(wl)); }
        if dd > 0 && *shown_dn < 6 { *shown_dn += 1; show("UPPER-BOUND-FAILS", e, Some(wl)); }
    };
    record(&ident, 0, &mut hist, &mut total, &mut shown_up, &mut shown_dn);

    for d in 0..depth {
        let mut next = Vec::new();
        for e in frontier.iter() {
            for (lbl, g) in gensl(e).iter() {
                if !dist.contains_key(g) {
                    dist.insert(g.clone(), d + 1);
                    parent.insert(g.clone(), (e.clone(), lbl));
                    next.push(g.clone());
                }
            }
        }
        for e in next.iter() {
            record(e, d + 1, &mut hist, &mut total, &mut shown_up, &mut shown_dn);
        }
        eprintln!("[truelen] depth {} -> {} new, cumulative {}", d + 1, next.len(), dist.len());
        frontier = next;
    }

    println!("\nchecked {total} elements to depth {depth}");
    let mut ks: Vec<(bool, i64)> = hist.keys().copied().collect();
    ks.sort();
    println!("histogram of  wordLength - (lR + 2c), split by has-gap-edge:");
    for k in ks { println!("   gap={} d={:4} : {}", k.0, k.1, hist[&k]); }

    println!("\nnamed witnesses:");
    show("one", &Elt { eps: 1, dl: 0, k: 0, lamps: vec![] },
        dist.get(&Elt { eps: 1, dl: 0, k: 0, lamps: vec![] }).copied());
    let we = Elt { eps: 1, dl: 0, k: 1, lamps: vec![(0, 1)] };
    show("witElt", &we, dist.get(&we).copied());
    let wn = Elt { eps: 1, dl: 0, k: -1, lamps: vec![(-1, -1), (2, 2)] };
    show("witNeg", &wn, dist.get(&wn).copied());

    println!("\npure-travel family  trav(n) = (kstar=n, eps=-1, delta=0, d_j = travel):");
    for n in 1..=8i32 {
        let lamps: Lamps = (0..n).map(|j| (j, 1)).collect();
        let t = Elt { eps: -1, dl: 0, k: n, lamps };
        let (lr, c, a, b) = lr_and_c(&t);
        println!("  n={n}: A={a} B={b} lR={lr} c={c} lR+2c={} wordLength={:?} gaps={}",
            lr + 2 * c, dist.get(&t), gapcount(&t));
    }
    println!("\nnegative-travel family (kstar=-n, eps=1, delta=0, d_j = travel):");
    for n in 1..=8i32 {
        let lamps: Lamps = (-n..0).map(|j| (j, -1)).collect();
        let t = Elt { eps: 1, dl: 0, k: -n, lamps };
        let (lr, c, a, b) = lr_and_c(&t);
        println!("  n={n}: A={a} B={b} lR={lr} c={c} lR+2c={} wordLength={:?} gaps={}",
            lr + 2 * c, dist.get(&t), gapcount(&t));
    }
    println!("\ngeodesic words (applied left to right, starting from `one`):");
    for (nm, t) in [("gBad+", Elt { eps: 1, dl: 0, k: 0, lamps: vec![(1, 2)] }),
                    ("gBad-", Elt { eps: 1, dl: 0, k: 0, lamps: vec![(1, -2)] }),
                    ("witElt", Elt { eps: 1, dl: 0, k: 1, lamps: vec![(0, 1)] }),
                    ("witNeg", Elt { eps: 1, dl: 0, k: -1, lamps: vec![(-1, -1), (2, 2)] })] {
        if let Some(&dd) = dist.get(&t) {
            let mut w = Vec::new();
            let mut cur = t.clone();
            while let Some((p, l)) = parent.get(&cur) { w.push(*l); cur = p.clone(); }
            w.reverse();
            println!("  {nm:8} len {dd}: {}", w.join(" "));
            // replay and print states
            let mut st = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
            for l in w.iter() {
                let g = gensl(&st);
                st = g.iter().find(|(x, _)| x == l).unwrap().1.clone();
                print!("      {l} -> k={} eps={} dl={} d={:?}\n", st.k, st.eps, st.dl, st.lamps);
            }
        } else { println!("  {nm:8} not reached"); }
    }
}
