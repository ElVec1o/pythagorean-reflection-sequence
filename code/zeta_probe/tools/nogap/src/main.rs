// nogap -- exact check of the no-gap / shield-law statements on real group elements.
//
//   M6a  no gap edge  =>  Z empty              (PROVED; this is falsification)
//   M6   no gap edge  =>  c = 0                (HEURISTIC)
//   M6b  Z empty      =>  c = 0                (CONJECTURE)
//   M4b  shield law   c = |Z|  at all k*       (HEURISTIC)
//   cut  prop:cut     c >= |Z|                 (PROVED -- a violation is a bug here)
//
// c is computed as (l_T - l_R)/2 with l_T the BFS word length (ground truth) and
// l_R the closed form of cor:lRclosed.  It is NEVER taken from relaxed_solve,
// which is FALSE on gap-bearing elements (see README).
//
// All integer arithmetic.  No floating point outside the ETA display.

use std::collections::HashMap;
use std::io::Write;
use std::time::Instant;

type Lamps = Vec<(i32, i32)>; // sorted, non-zero values only
#[derive(Clone, PartialEq, Eq, Hash)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }

#[inline]
fn f(k: i32, j: i32) -> i32 {
    if k > 0 && j >= 0 && j < k { 1 } else if k < 0 && j >= k && j < 0 { -1 } else { 0 }
}
#[inline]
fn dep(l: &Lamps, j: i32) -> i32 {
    match l.binary_search_by_key(&j, |&(x, _)| x) { Ok(i) => l[i].1, Err(_) => 0 }
}

fn span(k: i32, l: &Lamps) -> (i32, i32) {
    let (mut lo, mut hi) = (0.min(k), 0.max(k));
    for &(j, v) in l {
        if v != 0 { lo = lo.min(j); hi = hi.max(j + 1); }
    }
    if k > 0 { lo = lo.min(0); hi = hi.max(k); }
    if k < 0 { lo = lo.min(k); hi = hi.max(0); }
    (lo, hi)
}

// alpha, beta, Phi at site s, with the sitecost virtual-event fold-in.
fn abphi(e: &Elt, s: i32) -> (i32, i32, i32) {
    let (mut al, mut be, mut phi) = (dep(&e.lamps, s - 1), dep(&e.lamps, s), f(e.k, s - 1));
    if s == 0 { al -= 1; phi += 1; }
    if s == e.k {
        if e.dl == 0 { al += e.eps as i32; phi -= 1; } else { be -= e.eps as i32; }
    }
    (al, be, phi)
}

fn closed_lr(e: &Elt) -> i64 {
    let (lo, hi) = span(e.k, &e.lamps);
    let mut t: i64 = 0;
    for j in lo..hi {
        let m = dep(&e.lamps, j).abs().max(f(e.k, j).abs());
        t += if m == 0 { 2 } else { m } as i64;         // gap edge: reachability forces 2
    }
    for s in lo..=hi {
        let (a, b, p) = abphi(e, s);
        t += a.abs().max(b.abs()).max(p.abs()) as i64;
    }
    t
}

// Z: cut sites interior to the span, plus the boundary-shield site.
fn cutset(e: &Elt) -> usize {
    let (lo, hi) = span(e.k, &e.lamps);
    let mut n = 0;
    for s in lo..=hi {
        let interior = s > lo && s < hi;
        let boundary_shield = !interior && e.k == 0 && e.dl == 0 && s == 0 && lo == 0 && hi > 0;
        if !(interior || boundary_shield) { continue; }
        let (a, b, p) = abphi(e, s);
        if a == 0 && b == 0 && p == 0 { n += 1; }
    }
    n
}

fn has_gap(e: &Elt) -> bool {
    let (lo, hi) = span(e.k, &e.lamps);
    (lo..hi).any(|j| dep(&e.lamps, j) == 0 && f(e.k, j) == 0)
}

fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}

fn main() {
    let depth: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(21);
    eprintln!("[nogap] BFS to depth {depth}; c = (l_T - l_R)/2, l_R from the closed form");

    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    let mut dist: HashMap<Elt, u32> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    let t0 = Instant::now();

    for d in 0..depth {
        let mut next = Vec::new();
        for e in &frontier {
            let mut cands = Vec::with_capacity(3);
            cands.push(Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() });
            cands.push(Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() });
            if e.dl == 0 {
                cands.push(Elt { eps: e.eps, dl: 1, k: e.k - 1,
                                 lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) });
            } else {
                cands.push(Elt { eps: e.eps, dl: 0, k: e.k + 1,
                                 lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) });
            }
            for c in cands {
                if !dist.contains_key(&c) { dist.insert(c.clone(), d + 1); next.push(c); }
            }
        }
        frontier = next;
        let el = t0.elapsed().as_secs_f64();
        let eta = if d + 1 > 0 { el / (d + 1) as f64 * (depth - d - 1) as f64 } else { 0.0 };
        eprintln!("[nogap] layer {:2}/{}: frontier {:>9}  total {:>10}  {:6.1}s  ETA {:6.1}s",
                  d + 1, depth, frontier.len(), dist.len(), el, eta);
        std::io::stderr().flush().ok();
    }

    let (mut used, mut cut_v, mut sl_v) = (0u64, 0u64, 0u64);
    let (mut ng, mut ng_c, mut ng_z) = (0u64, 0u64, 0u64);
    let (mut ze, mut ze_v) = (0u64, 0u64);
    let (mut odd, mut neg) = (0u64, 0u64);
    for (e, &lt) in &dist {
        if lt >= depth { continue; }          // frontier layer may be incomplete
        let lr = closed_lr(e);
        let diff = lt as i64 - lr;
        if diff < 0 { neg += 1; continue; }
        if diff % 2 != 0 { odd += 1; continue; }
        let c = (diff / 2) as usize;
        let z = cutset(e);
        used += 1;
        if c < z { cut_v += 1; }
        if c != z { sl_v += 1; }
        if z == 0 { ze += 1; if c != 0 { ze_v += 1; } }
        if !has_gap(e) { ng += 1; if c != 0 { ng_c += 1; } if z != 0 { ng_z += 1; } }
    }
    println!("[nogap] depth {depth}: {used} elements used ({} enumerated)", dist.len());
    println!("  parity/negativity failures        : odd={odd} neg={neg}");
    println!("  prop:cut   c >= |Z|   violations  : {cut_v}   (PROVED -- must be 0)");
    println!("  M4b shield c == |Z|   violations  : {sl_v}");
    println!("  M6b  Z empty => c=0 : {ze:>8} elts, violations {ze_v}");
    println!("  M6   no gap  => c=0 : {ng:>8} elts, violations {ng_c}");
    println!("  M6a  no gap  => Z=0 : {ng:>8} elts, violations {ng_z}");
    // --- series mode: u_n (true length) and v_m (relaxed length), plus pure-travel ---
    let mut un = vec![0u64; (depth + 1) as usize];
    let mut vm = vec![0u64; (depth + 1) as usize];
    let mut pt = vec![0u64; (depth + 1) as usize];   // pure travel: supp inside I_k
    let mut maxc = 0usize;
    for (e, &lt) in &dist {
        if lt <= depth { un[lt as usize] += 1; }
        let lr = closed_lr(e);
        let c = ((lt as i64 - lr) / 2).max(0) as usize;
        maxc = maxc.max(c);
        if lr >= 0 && (lr as usize) <= depth as usize && lt < depth {
            vm[lr as usize] += 1;
            let pure = e.lamps.iter().all(|&(j, v)| v == 0 || f(e.k, j) != 0);
            if pure { pt[lr as usize] += 1; }
        }
    }
    // v_m is exact only while no element with that l_R was truncated by the BFS radius
    let vsafe = (depth as usize).saturating_sub(2 * maxc);
    println!("  max c observed = {maxc}; v_m exact for m <= {vsafe}");
    print!("  u_n :"); for n in 0..=20.min(depth as usize) { print!(" {}", un[n]); } println!();
    print!("  v_m :"); for n in 0..=vsafe.min(20) { print!(" {}", vm[n]); } println!();
    print!("  pureT:"); for n in 0..=vsafe.min(18) { print!(" {}", pt[n]); } println!();

    let verdict = cut_v == 0 && sl_v == 0 && ze_v == 0 && ng_c == 0 && ng_z == 0 && odd == 0 && neg == 0;
    println!("[nogap] VERDICT: {}", if verdict { "all statements hold, 0 exceptions" } else { "EXCEPTIONS PRESENT" });
}
