// An independent Rust re-derivation of `nogap/side_probe2.py`.
//
// That script is what `HasFreePair` rests on -- "146 of 146 multi-walk
// cost-minimal cases admit a shared-side pair" -- and it could not run at all
// until repaired, having referenced a `side.py` that no longer exists.  Its
// predecessor `side_probe.py` was ALSO wrong once (costs backwards), so the
// claim deserves a second implementation rather than a second reading.
//
// The model here is side_probe2's, NOT sitecost's.  EndData.sgn forces
// sgn(t a) = !sgn(a) whenever an arrival and its departure share a side, so a
// same-side pair is always a sign-flipped bounce costing 2 and a different-side
// pair is a pass costing 1.  Minimising therefore MAXIMISES passes -- the
// opposite of the free-sign model that `sitecost` certifies, where a same-class
// bounce costs 0.  The two models are the `EndData` / `GData` pair.
//
//   end        = (edge, strand index, top?)
//   site x     = edge + [top]
//   isUp x     = index < up[edge]
//   isArr x    = isUp x == top          (an up strand arrives at its top)
//   partner x  = flip top
//   turn t     = involution pairing arrivals to departures at each site

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct End { e: usize, i: usize, t: bool }

fn site(x: End) -> usize { x.e + if x.t { 1 } else { 0 } }
fn is_up(x: End, up: &[usize]) -> bool { x.i < up[x.e] }
fn is_arr(x: End, up: &[usize]) -> bool { is_up(x, up) == x.t }
fn partner(x: End) -> End { End { e: x.e, i: x.i, t: !x.t } }

fn ends(n: usize, m: &[usize]) -> Vec<End> {
    let mut v = vec![];
    for e in 0..n { for i in 0..m[e] { for &t in &[false, true] { v.push(End { e, i, t }); } } }
    v
}

/// every involution pairing arrivals to departures at each site
fn turns(es: &[End], up: &[usize]) -> Vec<HashMap<End, End>> {
    let mut bysite: HashMap<usize, (Vec<End>, Vec<End>)> = HashMap::new();
    for &x in es {
        let e = bysite.entry(site(x)).or_insert((vec![], vec![]));
        if is_arr(x, up) { e.0.push(x); } else { e.1.push(x); }
    }
    let mut sites: Vec<usize> = bysite.keys().copied().collect();
    sites.sort();
    for s in &sites {
        let (a, d) = &bysite[s];
        if a.len() != d.len() { return vec![]; }
    }
    let mut out: Vec<HashMap<End, End>> = vec![HashMap::new()];
    for s in &sites {
        let (a, d) = bysite[s].clone();
        let k = a.len();
        let mut perms: Vec<Vec<usize>> = vec![];
        let mut idx: Vec<usize> = (0..k).collect();
        fn go(j: usize, idx: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
            if j == idx.len() { out.push(idx.clone()); return; }
            for i in j..idx.len() { idx.swap(j, i); go(j + 1, idx, out); idx.swap(j, i); }
        }
        go(0, &mut idx, &mut perms);
        let mut next = vec![];
        for base in &out {
            for p in &perms {
                let mut t = base.clone();
                for j in 0..k { t.insert(a[j], d[p[j]]); t.insert(d[p[j]], a[j]); }
                next.push(t);
            }
        }
        out = next;
    }
    out
}

/// components of the graph joining each end to its partner and to its turn
fn walks(es: &[End], t: &HashMap<End, End>) -> (HashMap<End, usize>, usize) {
    let mut comp: HashMap<End, usize> = HashMap::new();
    let mut c = 0;
    for &x in es {
        if comp.contains_key(&x) { continue; }
        let mut stack = vec![x];
        while let Some(y) = stack.pop() {
            if comp.contains_key(&y) { continue; }
            comp.insert(y, c);
            stack.push(partner(y));
            if let Some(&z) = t.get(&y) { stack.push(z); }
        }
        c += 1;
    }
    (comp, c)
}

/// side_probe2's cost: same side is a sign-flipped bounce (2), different side a pass (1)
fn cost(es: &[End], t: &HashMap<End, End>, up: &[usize]) -> usize {
    es.iter().filter(|&&a| is_arr(a, up))
        .map(|&a| if a.t == t[&a].t { 2 } else { 1 }).sum()
}

/// The same probe in the FREE-sign model.  `HasFreePair`'s statement mentions only
/// the SIDE (= top?), not the sign, so it is model-independent; what the model changes
/// is which turns are COST-MINIMAL.  Here each end carries its own free sign and the
/// cost is GData.pcost: 0 same side and same sign, 2 same side opposite sign, 1 across.
///
/// `free_pair_of_minimal_fails_in_free_model` refutes the CRITERION in this model.  It
/// does not refute the conclusion, and that is what this measures.
pub fn run_free() {
    println!("[cutturn] freepair-g -- HasFreePair at cost-minimal data, configGData signs");
    println!("[cutturn] cost: same side+sign 0, same side opposite sign 2, across 1");
    println!("[cutturn] signs are per STRAND, as configGData has them, not per end");
    let (mut tot, mut multi, mut ok, mut bad) = (0u64, 0u64, 0u64, 0u64);
    let mut shown = 0;
    for n in 1..=3usize {
        for mcode in 0..2usize.pow(n as u32) {
            let mut c = mcode;
            let m: Vec<usize> = (0..n).map(|_| { let v = [2usize,4][c % 2]; c /= 2; v }).collect();
            for ucode in 0..5usize.pow(n as u32) {
                let mut c = ucode;
                let up: Vec<usize> = (0..n).map(|_| { let v = c % 5; c /= 5; v }).collect();
                if (0..n).any(|j| up[j] > m[j]) { continue; }
                let es = ends(n, &m);
                let ts = turns(&es, &up);
                if ts.is_empty() { continue; }
                // signs as configGData has them: one bit per STRAND, shared by its
                // two ends (sgnOf x = sg x.edge x.idx).  A per-END sign would be
                // strictly more general than any configuration.
                let mut strands: Vec<(usize, usize)> = vec![];
                for e in 0..n { for i in 0..m[e] { strands.push((e, i)); } }
                let nb = strands.len();
                if nb > 20 { continue; }
                for sgncode in 0u32..(1u32 << nb) {
                    let sidx: HashMap<(usize, usize), bool> = strands.iter().enumerate()
                        .map(|(k, &st)| (st, (sgncode >> k) & 1 == 1)).collect();
                    let sgn: HashMap<End, bool> = es.iter()
                        .map(|&e| (e, sidx[&(e.e, e.i)])).collect();
                    let gcost = |t: &HashMap<End, End>| -> usize {
                        es.iter().filter(|&&a| is_arr(a, &up)).map(|&a| {
                            let b = t[&a];
                            if a.t == b.t { if sgn[&a] == sgn[&b] { 0 } else { 2 } } else { 1 }
                        }).sum()
                    };
                    let best = ts.iter().map(|t| gcost(t)).min().unwrap();
                    for t in &ts {
                        if gcost(t) != best { continue; }
                        tot += 1;
                        let (comp, nc) = walks(&es, t);
                        if nc < 2 { continue; }
                        multi += 1;
                        let mut found = false;
                        'outer: for &a in &es {
                            if !is_arr(a, &up) { continue; }
                            for &a2 in &es {
                                if !is_arr(a2, &up) { continue; }
                                if site(a) != site(a2) || comp[&a] == comp[&a2] { continue; }
                                if a.t == a2.t || t[&a].t == t[&a2].t { found = true; break 'outer; }
                            }
                        }
                        if found { ok += 1; } else {
                            bad += 1;
                            if shown < 3 {
                                shown += 1;
                                println!("  NO SHARED-SIDE PAIR: n={} m={:?} up={:?} walks={} cost={}",
                                    n, m, up, nc, best);
                            }
                        }
                    }
                }
            }
        }
    }
    println!("  cost-minimal turns: {tot}  multi-walk: {multi}  shared-side pair exists: {ok}  none: {bad}");
    println!("  {}", if bad == 0 {
        "HasFreePair HOLDS at every cost-minimal multi-walk datum tested in the FREE-sign model"
    } else { "HasFreePair FAILS in the free-sign model -- counterexample above" });
}

pub fn run() {
    println!("[cutturn] freepair -- independent re-derivation of nogap/side_probe2.py");
    println!("[cutturn] model: same side 2, different side 1 (EndData derived sign)");
    let (mut tot, mut multi, mut ok, mut bad) = (0u64, 0u64, 0u64, 0u64);
    for n in 1..=3usize {
        let mchoices = [2usize, 4];
        for mcode in 0..mchoices.len().pow(n as u32) {
            let mut c = mcode;
            let m: Vec<usize> = (0..n).map(|_| { let v = mchoices[c % 2]; c /= 2; v }).collect();
            for ucode in 0..5usize.pow(n as u32) {
                let mut c = ucode;
                let up: Vec<usize> = (0..n).map(|_| { let v = c % 5; c /= 5; v }).collect();
                if (0..n).any(|j| up[j] > m[j]) { continue; }
                let es = ends(n, &m);
                let ts = turns(&es, &up);
                if ts.is_empty() { continue; }
                let best = ts.iter().map(|t| cost(&es, t, &up)).min().unwrap();
                for t in &ts {
                    if cost(&es, t, &up) != best { continue; }
                    tot += 1;
                    let (comp, nc) = walks(&es, t);
                    if nc < 2 { continue; }
                    multi += 1;
                    let mut found = false;
                    'outer: for &a in &es {
                        if !is_arr(a, &up) { continue; }
                        for &a2 in &es {
                            if !is_arr(a2, &up) { continue; }
                            if site(a) != site(a2) || comp[&a] == comp[&a2] { continue; }
                            if a.t == a2.t || t[&a].t == t[&a2].t { found = true; break 'outer; }
                        }
                    }
                    if found { ok += 1; } else { bad += 1; }
                }
            }
        }
    }
    println!("  cost-minimal turns: {tot}  multi-walk: {multi}  shared-side pair exists: {ok}  none: {bad}");
    println!("  python side_probe2.py reports: 263 / 146 / 146 / 0");
    println!("  {}", if tot == 263 && multi == 146 && ok == 146 && bad == 0 {
        "AGREES with the Python on all four counts" } else { "DISAGREES -- investigate" });
}
