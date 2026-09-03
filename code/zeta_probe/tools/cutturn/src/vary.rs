// Runs whose edges have DIFFERENT level counts, done properly.
//
// A first attempt forced exactly min(u[j],u[j+1]) passes with a fixed pairing for the
// excess, and reported runs that cannot reach one component.  That was wrong: the number
// of passes may be ANY value up to the minimum, and both the passes and the leftover
// bounces may pair any way.  So this enumerates every pairing at every site.
//
// A site between edges j and j+1 has arrivals  {up-tops of j} + {down-bottoms of j+1}
// and departures {down-tops of j} + {up-bottoms of j+1}; a turn is any bijection between
// them.  Passing is arrival-from-one-edge to departure-on-the-other.

use std::collections::HashSet;

fn perms_of(v: &[usize]) -> Vec<Vec<usize>> {
    let mut out = vec![]; let mut idx = v.to_vec();
    fn go(j: usize, idx: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if j == idx.len() { out.push(idx.clone()); return; }
        for i in j..idx.len() { idx.swap(j, i); go(j + 1, idx, out); idx.swap(j, i); }
    }
    go(0, &mut idx, &mut out); out
}

pub fn run(umax: usize) {
    println!("[cutturn] vary -- mixed-width runs, EVERY pairing at every site");
    let mut bad: Vec<(Vec<usize>, usize)> = vec![];
    for k in 2..=3usize {
        for code in 0..umax.pow(k as u32) {
            let mut c = code;
            let u: Vec<usize> = (0..k).map(|_| { let v = c % umax + 1; c /= umax; v }).collect();
            if u.iter().all(|&x| x == u[0]) { continue; }
            // strand ids
            let mut off = vec![0usize; k + 1];
            for j in 0..k { off[j + 1] = off[j] + 2 * u[j]; }
            let n = off[k];
            let id = |j: usize, l: usize, up: bool| off[j] + if up { l } else { u[j] + l };
            // at each site, arrivals and departures as strand ids paired by the turn
            // site 0: bottoms of edge 0 -- arrivals are the DOWN bottoms, departures the UP
            // site k: tops of edge k-1 -- arrivals the UP tops, departures the DOWN
            // interior site j+1: arrivals = up-tops of j, down-bottoms of j+1
            //                    departures = down-tops of j, up-bottoms of j+1
            let mut sites: Vec<(Vec<usize>, Vec<usize>)> = vec![];
            sites.push(((0..u[0]).map(|l| id(0, l, false)).collect(),
                        (0..u[0]).map(|l| id(0, l, true)).collect()));
            for j in 0..k - 1 {
                let mut a: Vec<usize> = (0..u[j]).map(|l| id(j, l, true)).collect();
                a.extend((0..u[j + 1]).map(|l| id(j + 1, l, false)));
                let mut d: Vec<usize> = (0..u[j]).map(|l| id(j, l, false)).collect();
                d.extend((0..u[j + 1]).map(|l| id(j + 1, l, true)));
                sites.push((a, d));
            }
            sites.push(((0..u[k - 1]).map(|l| id(k - 1, l, true)).collect(),
                        (0..u[k - 1]).map(|l| id(k - 1, l, false)).collect()));
            // every combination of per-site bijections
            let opts: Vec<Vec<Vec<usize>>> =
                sites.iter().map(|(_, d)| perms_of(d)).collect();
            let mut counters = vec![0usize; sites.len()];
            let mut best = usize::MAX;
            loop {
                let mut p: Vec<usize> = (0..n).collect();
                fn find(p: &mut Vec<usize>, x: usize) -> usize {
                    let mut x = x; while p[x] != x { p[x] = p[p[x]]; x = p[x]; } x
                }
                let mut uni = |p: &mut Vec<usize>, a: usize, b: usize| {
                    let (ra, rb) = (find(p, a), find(p, b)); if ra != rb { p[ra] = rb; }
                };
                for (si, (a, _)) in sites.iter().enumerate() {
                    let img = &opts[si][counters[si]];
                    for (t, &av) in a.iter().enumerate() { uni(&mut p, av, img[t]); }
                }
                let mut roots = HashSet::new();
                for x in 0..n { let r = find(&mut p, x); roots.insert(r); }
                best = best.min(roots.len());
                let mut c2 = 0;
                while c2 < sites.len() {
                    counters[c2] += 1;
                    if counters[c2] < opts[c2].len() { break; }
                    counters[c2] = 0; c2 += 1;
                }
                if c2 == sites.len() { break; }
            }
            if best != 1 { bad.push((u.clone(), best)); }
        }
    }
    if bad.is_empty() {
        println!("  every mixed-width run reaches ONE component for some pairing");
    } else {
        println!("  runs that cannot ({} of them):", bad.len());
        for (u, b) in bad.iter().take(8) { println!("    u = {:?}: fewest {}", u, b); }
    }
}
