// s3_jump -- isolate the max |dPhi| caused by s3 ALONE, on the correct (nogapBS)
// potential.  Prior blocks measured the combined max over all three generators;
// this checks s3 specifically before committing to a Lean proof strategy for it.

use std::collections::HashMap;

type Lamps = Vec<(i32, i32)>;
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }

#[inline]
fn travel(k: i32, j: i32) -> i32 {
    if 0 <= j && j < k { 1 } else if k <= j && j < 0 { -1 } else { 0 }
}
#[inline]
fn dep(l: &Lamps, j: i32) -> i32 {
    match l.binary_search_by_key(&j, |&(x, _)| x) { Ok(i) => l[i].1, Err(_) => 0 }
}
fn span_nogap(e: &Elt) -> (i32, i32) {
    let (mut lo, mut hi) = (0.min(e.k), 0.max(e.k));
    for &(j, v) in &e.lamps { if v != 0 { lo = lo.min(j); hi = hi.max(j + 1); } }
    if e.k > 0 { lo = lo.min(0); hi = hi.max(e.k); }
    if e.k < 0 { lo = lo.min(e.k); hi = hi.max(0); }
    (lo, hi - 1)
}
fn abphi(e: &Elt, s: i32) -> (i32, i32, i32) {
    let varr = if s == 0 { 1 } else { 0 };
    let vd = if s == e.k { 1 } else { 0 };
    let (vl, vr) = if e.dl == 0 { (vd, 0) } else { (0, vd) };
    let eps = e.eps as i32;
    (dep(&e.lamps, s - 1) - varr + eps * vl, dep(&e.lamps, s) - eps * vr, 0)
}
fn mu(e: &Elt, j: i32) -> i64 {
    let (d, f) = (dep(&e.lamps, j), travel(e.k, j));
    if d == 0 && f == 0 { 2 } else { d.abs().max(f.abs()) as i64 }
}
fn lr_on(e: &Elt, a: i32, b: i32) -> i64 {
    let mut t = 0i64;
    for j in a..=b { t += mu(e, j); }
    for s in a..=b + 1 {
        let (al, be, _) = abphi(e, s);
        t += al.abs().max(be.abs()) as i64;
    }
    t
}
fn is_cut(e: &Elt, s: i32) -> bool { let (a, b, _) = abphi(e, s); a == 0 && b == 0 }
fn cuts_on(e: &Elt, a: i32, b: i32) -> i64 {
    let mut n = 0i64;
    for s in a + 1..b + 1 { if is_cut(e, s) { n += 1; } }
    if e.k == 0 && e.dl == 0 && a == 0 && b + 1 > 0 && is_cut(e, 0) { n += 1; }
    n
}
fn phi(e: &Elt) -> i64 {
    let (a, b) = span_nogap(e);
    lr_on(e, a, b) + 2 * cuts_on(e, a, b)
}
fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}
fn s3(e: &Elt) -> Elt {
    if e.dl == 0 {
        Elt { eps: e.eps, dl: 1, k: e.k - 1, lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) }
    } else {
        Elt { eps: e.eps, dl: 0, k: e.k + 1, lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) }
    }
}
fn gens_all(e: &Elt) -> [Elt; 3] {
    [Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     s3(e)]
}
fn size(e: &Elt) -> i64 { e.k.abs() as i64 + e.lamps.iter().map(|&(_, v)| v.abs() as i64).sum::<i64>() }
fn show(e: &Elt) -> String {
    format!("k={} eps={} delta={} d={:?}", e.k, e.eps, if e.dl == 0 { "false" } else { "true" }, e.lamps)
}

fn main() {
    let depth: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(20);
    let cap: usize = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(6_000_000);

    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    let mut dist: HashMap<Elt, u8> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    for d in 0..depth {
        let mut next = Vec::new();
        for e in &frontier {
            for c in gens_all(e) {
                if !dist.contains_key(&c) { dist.insert(c.clone(), (d + 1) as u8); next.push(c); }
            }
        }
        frontier = next;
        if dist.len() > cap { eprintln!("[s3] cap hit at depth {}", d + 1); break; }
    }
    eprintln!("[s3] enumerated {} elements", dist.len());

    let (mut max_jump, mut wsize, mut wit): (i64, i64, Option<(Elt, Elt, i64, i64)>) = (0, i64::MAX, None);
    for e in dist.keys() {
        let e2 = s3(e);
        let (p1, p2) = (phi(e), phi(&e2));
        let jump = (p2 - p1).abs();
        let sz = size(e);
        if jump > max_jump || (jump == max_jump && sz < wsize) {
            max_jump = jump; wsize = sz; wit = Some((e.clone(), e2, p1, p2));
        }
    }
    println!("[s3] max |dPhi| under s3 ALONE (nogapBS potential) = {max_jump}");
    if let Some((e, e2, p1, p2)) = wit {
        println!("  witness: {}  ->  {}", show(&e), show(&e2));
        println!("  Phi before = {p1}, Phi after = {p2}");
    }
}
