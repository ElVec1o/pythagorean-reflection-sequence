// mndefect -- Myhill-Nerode census of the TRUE connectivity defect of paper1's
// right-triangle reflection group W_gen.  Crux C2.
//
// WHAT IS BEING DECIDED
// ---------------------
// paper1 claims  ell_T(g) = ell_R(g) + 2 c(g).  The upper bound is proved.  The
// lower bound needs the TRUE defect  c_true(g) = (ell_T(g) - ell_R(g))/2  to be a
// finite-state function of the edge profile WITH AN EXPLICIT STATE BOUND N; Moore's
// criterion then closes it against the paper's 4-state transducer A.  thm:Bproved was
// retracted on 2026-08-09 because its chain assumed that finite-stateness.
//
// ANTI-CIRCULARITY (trap 1)
// -------------------------
// c_true is NEVER computed from "true = relaxed + 2c".  It is computed as the
// difference of two INDEPENDENT minimisations over realisations of the element on the
// crossing multigraph:
//     ell_T  = min cost over realisations whose transition system is a SINGLE OPEN WALK
//     ell_R  = min cost over ALL realisations (isolated cycles free)
// Both are the site-by-site interface DP ported from route_b/lamp_lib.py
// (solve / relaxed_solve).  The ell_T oracle is validated against the genuine
// geodesic BFS of the group (the `validate` mode) before any defect is read off it.
//
// SUPPORT REPORTING (trap 2)
// --------------------------
// Two words are Myhill-Nerode equivalent for the defect iff
//     c(w v) - c(w) = c(w' v) - c(w')  for EVERY suffix v.
// Compared on too few suffixes, classes merge spuriously and a plateau appears that is
// pure artifact.  Every count printed here therefore carries SUPPORT = the number of
// suffixes actually compared.  Two independent numbers are printed per length:
//     LOWER = # distinct residual vectors over the compared suffixes
//             (distinctness is monotone in evidence => a genuine lower bound on the
//              number of MN classes)
//     UPPER = # distinct normalised DP frontier pairs
//             (equal frontiers => equal residuals for EVERY suffix, proved in the
//              README => a genuine upper bound on the number of MN classes)
// When LOWER == UPPER the MN class count is pinned EXACTLY and that number is N.
//
// Usage:
//   mndefect validate <depth> [lam_max]
//   mndefect mn --k K --eps E --delta D [--b B] --alpha "0,2,-2" --len L --probe P
//               [--lam LAM] [--cut C]
//   mndefect selftest

use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::time::Instant;

// =====================================================================
// 1. THE GROUP.  Element = (eps, delta, k, lamps).  Generators R_x, R_y, R_h.
//    Dynamics exactly as paper1 thm (symbolic normal form) and as
//    route_b/lamp_lib.py bfs():
//      R_x : delta -> 1-delta
//      R_y : (eps,delta) -> (-eps, 1-delta)
//      R_h : delta=0 -> a[k-1] += eps, k -= 1, delta = 1
//            delta=1 -> a[k]   -= eps, k += 1, delta = 0
// =====================================================================

type Lamps = Vec<(i32, i32)>; // sorted by position, all values nonzero

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct Elt {
    eps: i8,
    dl: u8,
    k: i32,
    a: Lamps,
}

fn lamp_add(a: &Lamps, pos: i32, v: i32) -> Lamps {
    let mut out: Lamps = Vec::with_capacity(a.len() + 1);
    let mut done = false;
    for &(p, x) in a.iter() {
        if p < pos {
            out.push((p, x));
        } else if p == pos {
            let nv = x + v;
            if nv != 0 {
                out.push((p, nv));
            }
            done = true;
        } else {
            if !done {
                out.push((pos, v));
                done = true;
            }
            out.push((p, x));
        }
    }
    if !done {
        out.push((pos, v));
    }
    out
}

/// Genuine geodesic BFS in the group.  Returns element -> word length.
fn group_bfs(maxd: usize, verbose: bool) -> HashMap<Elt, u32> {
    let ident = Elt { eps: 1, dl: 0, k: 0, a: vec![] };
    let mut dist: HashMap<Elt, u32> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    for d in 0..maxd {
        let mut next: Vec<Elt> = Vec::new();
        for e in frontier.iter() {
            let mut cands: Vec<Elt> = Vec::with_capacity(3);
            cands.push(Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, a: e.a.clone() }); // R_x
            cands.push(Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, a: e.a.clone() }); // R_y
            if e.dl == 0 {
                cands.push(Elt {
                    eps: e.eps,
                    dl: 1,
                    k: e.k - 1,
                    a: lamp_add(&e.a, e.k - 1, e.eps as i32),
                });
            } else {
                cands.push(Elt {
                    eps: e.eps,
                    dl: 0,
                    k: e.k + 1,
                    a: lamp_add(&e.a, e.k, -(e.eps as i32)),
                });
            }
            for c in cands {
                if !dist.contains_key(&c) {
                    dist.insert(c.clone(), (d + 1) as u32);
                    next.push(c);
                }
            }
        }
        if verbose {
            eprintln!("   BFS d = {:>2}: layer {:>8}, cumulative {:>9}", d + 1, next.len(), dist.len());
        }
        frontier = next;
        if frontier.is_empty() {
            break;
        }
    }
    dist
}

// =====================================================================
// 2. THE REALISATION DP (interface / "plumber profile").
//    Ported line for line from route_b/lamp_lib.py solve() and relaxed_solve().
// =====================================================================

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
struct Comp {
    upp: u8,
    upm: u8,
    dnp: u8,
    dnm: u8,
    st: bool,
    en: bool,
}

/// `fin` = the open walk has already closed (both markers consumed).
/// In TRUE mode `fin` implies `comps` is empty (a single open walk may not leave
/// anything behind).  In RELAXED mode live strands may survive past `fin`: they are
/// exactly the isolated cycles, which cost nothing and are dropped when they close.
/// This distinction is the whole content of the defect, so getting it wrong collapses
/// ell_R onto ell_T.  route_b/lamp_lib.py `relaxed_solve` DOES get it wrong -- it
/// carries the true-mode rejection `if finished is not None and newcomps: continue`
/// into the relaxed branch, which makes it return ell_T on e.g.
/// (eps=1, delta=0, k=0, a_1=2).  That function is not the one the paper's
/// certificates use (they use catalytic_funceq.relaxed_len_local); it is stale.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct DpKey {
    fin: bool,
    comps: Vec<Comp>,
    sp: bool,
    ep: bool,
}

type DpMap = BTreeMap<DpKey, i32>;

fn relax_into(m: &mut DpMap, k: DpKey, v: i32) {
    match m.get_mut(&k) {
        Some(old) => {
            if v < *old {
                *old = v;
            }
        }
        None => {
            m.insert(k, v);
        }
    }
}

fn f_of(j: i32, k: i32) -> i32 {
    if 0 <= j && j < k {
        1
    } else if k <= j && j < 0 {
        -1
    } else {
        0
    }
}

fn pcost(a_side: u8, a_sign: i8, d_side: u8, d_sign: i8) -> i32 {
    if a_side != d_side {
        1
    } else if a_sign == d_sign {
        0
    } else {
        2
    }
}

struct Ctx {
    k: i32,
    eps: i8,
    dl: u8,
    relaxed: bool,
    lam_max: i32,
}

/// Buffers reused across the pairing enumeration at one site.
struct Leaf<'a> {
    arr: &'a [(u8, i8, usize)],
    dep: &'a [(u8, i8, usize)],
    n: usize,
    pair: Vec<usize>,
    nc: usize,
    nid: usize,
    nref: usize,
    newrefs: &'a [(u8, i8)],
    comps: &'a [Comp],
    j: i32,
    ctx: &'a Ctx,
    sp: bool,
    ep: bool,
    fin: bool,
    parent: Vec<usize>,
    gs: Vec<[u8; 4]>,
    gst: Vec<bool>,
    gen: Vec<bool>,
    present: Vec<bool>,
}

impl<'a> Leaf<'a> {
    fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }

    fn finish(&mut self, cost: i32, out: &mut DpMap) {
        let nref = self.nref;
        for i in 0..nref {
            self.parent[i] = i;
            self.gs[i] = [0; 4];
            self.gst[i] = false;
            self.gen[i] = false;
            self.present[i] = false;
        }
        for i in 0..self.n {
            let ra = self.arr[i].2;
            let rd = self.dep[self.pair[i]].2;
            let x = Self::find(&mut self.parent, ra);
            let y = Self::find(&mut self.parent, rd);
            if x != y {
                self.parent[x] = y;
            }
        }
        for ni in 0..self.nid {
            let r = Self::find(&mut self.parent, self.nc + ni);
            self.present[r] = true;
            let (kind, sg) = self.newrefs[ni];
            // kind 1 = up, 0 = down
            let idx = if kind == 1 {
                if sg == 1 { 0 } else { 1 }
            } else if sg == 1 {
                2
            } else {
                3
            };
            self.gs[r][idx] += 1;
        }
        for ci in 0..self.nc {
            let r = Self::find(&mut self.parent, ci);
            self.present[r] = true;
            if self.comps[ci].st {
                self.gst[r] = true;
            }
            if self.comps[ci].en {
                self.gen[r] = true;
            }
        }
        if self.j == 0 {
            let r = Self::find(&mut self.parent, self.nc + self.nid);
            self.present[r] = true;
            self.gst[r] = true;
        }
        if self.j == self.ctx.k {
            let r = Self::find(&mut self.parent, self.nc + self.nid + 1);
            self.present[r] = true;
            self.gen[r] = true;
        }
        let mut newcomps: Vec<Comp> = Vec::new();
        let mut finished = false;
        for r in 0..nref {
            if !self.present[r] {
                continue;
            }
            let g = self.gs[r];
            let ns: u32 = g.iter().map(|&x| x as u32).sum();
            if ns == 0 {
                if self.gst[r] && self.gen[r] {
                    if finished || self.fin {
                        return; // two closed open-walks: invalid
                    }
                    finished = true;
                } else if self.gst[r] || self.gen[r] {
                    return; // dangling single marker: invalid in both models
                } else if !self.ctx.relaxed {
                    return; // isolated cycle: inadmissible for a single open walk
                }
                // relaxed: isolated cycle, FREE, dropped
            } else {
                newcomps.push(Comp {
                    upp: g[0],
                    upm: g[1],
                    dnp: g[2],
                    dnm: g[3],
                    st: self.gst[r],
                    en: self.gen[r],
                });
            }
        }
        if finished && !newcomps.is_empty() && !self.ctx.relaxed {
            return; // TRUE model only: the open walk may not close early
        }
        let nsp = self.sp || self.j == 0;
        let nep = self.ep || self.j == self.ctx.k;
        newcomps.sort();
        let key = DpKey { fin: self.fin || finished, comps: newcomps, sp: nsp, ep: nep };
        relax_into(out, key, cost);
    }

    fn rec(&mut self, i: usize, used: u32, cost: i32, out: &mut DpMap) {
        if i == self.n {
            self.finish(cost, out);
            return;
        }
        let (asd, asg, _) = self.arr[i];
        for d in 0..self.n {
            if used >> d & 1 == 1 {
                continue;
            }
            // multiset dedup: identical departures are interchangeable
            if d > 0 && self.dep[d] == self.dep[d - 1] && used >> (d - 1) & 1 == 0 {
                continue;
            }
            let (dsd, dsg, _) = self.dep[d];
            self.pair[i] = d;
            self.rec(i + 1, used | (1 << d), cost + pcost(asd, asg, dsd, dsg), out);
        }
    }
}

/// One site transition of the interface DP.
fn site_step(states: &DpMap, j: i32, aj: i32, fj: i32, ctx: &Ctx) -> DpMap {
    let mut out: DpMap = BTreeMap::new();
    let mut base = aj.abs().max(fj.abs());
    if (base - aj.abs()) % 2 != 0 {
        base += 1;
    }
    let mut cand: Vec<i32> = Vec::new();
    for lam in 0..=ctx.lam_max {
        let m = base + 2 * lam;
        if m == 0 && (aj != 0 || fj != 0) {
            continue;
        }
        cand.push(m);
    }

    for (key, &c0) in states.iter() {
        let comps = &key.comps;
        let prev_m: u32 = comps
            .iter()
            .map(|c| c.upp as u32 + c.upm as u32 + c.dnp as u32 + c.dnm as u32)
            .sum();
        for &m in cand.iter() {
            if (m - fj) % 2 != 0 {
                continue;
            }
            let u = (m + fj) / 2;
            let dn = (m - fj) / 2;
            if u < 0 || dn < 0 {
                continue;
            }
            if j <= -1 && prev_m > 0 && m == 0 {
                continue;
            }
            if j >= 1 && prev_m == 0 && m > 0 {
                continue;
            }
            for pu in 0..=u {
                let t = aj + dn - u + 2 * pu;
                if t % 2 != 0 {
                    continue;
                }
                let pd = t / 2;
                if pd < 0 || pd > dn {
                    continue;
                }
                // build arrivals / departures
                let nc = comps.len();
                let mut arr: Vec<(u8, i8, usize)> = Vec::new();
                let mut dep: Vec<(u8, i8, usize)> = Vec::new();
                for (ci, cc) in comps.iter().enumerate() {
                    for _ in 0..cc.upp {
                        arr.push((0, 1, ci));
                    }
                    for _ in 0..cc.upm {
                        arr.push((0, -1, ci));
                    }
                    for _ in 0..cc.dnp {
                        dep.push((0, 1, ci));
                    }
                    for _ in 0..cc.dnm {
                        dep.push((0, -1, ci));
                    }
                }
                let mut newrefs: Vec<(u8, i8)> = Vec::new();
                let mut nid = 0usize;
                for _ in 0..pd {
                    arr.push((1, 1, nc + nid));
                    newrefs.push((0, 1));
                    nid += 1;
                }
                for _ in 0..(dn - pd) {
                    arr.push((1, -1, nc + nid));
                    newrefs.push((0, -1));
                    nid += 1;
                }
                for _ in 0..pu {
                    dep.push((1, 1, nc + nid));
                    newrefs.push((1, 1));
                    nid += 1;
                }
                for _ in 0..(u - pu) {
                    dep.push((1, -1, nc + nid));
                    newrefs.push((1, -1));
                    nid += 1;
                }
                let nref = nc + nid + 2;
                if j == 0 {
                    arr.push((0, 1, nc + nid));
                }
                if j == ctx.k {
                    dep.push((
                        if ctx.dl == 1 { 1 } else { 0 },
                        if ctx.eps == 1 { 1 } else { -1 },
                        nc + nid + 1,
                    ));
                }
                if arr.len() != dep.len() {
                    continue;
                }
                let n = arr.len();
                if n == 0 {
                    if m != 0 {
                        continue;
                    }
                    if !comps.is_empty() {
                        continue;
                    }
                    relax_into(&mut out, key.clone(), c0);
                    continue;
                }
                dep.sort();
                let mut leaf = Leaf {
                    arr: &arr,
                    dep: &dep,
                    n,
                    pair: vec![0; n],
                    nc,
                    nid,
                    nref,
                    newrefs: &newrefs,
                    comps,
                    j,
                    ctx,
                    sp: key.sp,
                    ep: key.ep,
                    fin: key.fin,
                    parent: vec![0; nref],
                    gs: vec![[0u8; 4]; nref],
                    gst: vec![false; nref],
                    gen: vec![false; nref],
                    present: vec![false; nref],
                };
                leaf.rec(0, 0, c0 + m, &mut out);
            }
        }
    }
    out
}

fn init_dp() -> DpMap {
    let mut m: DpMap = BTreeMap::new();
    m.insert(DpKey { fin: false, comps: vec![], sp: false, ep: false }, 0);
    m
}

fn accept(states: &DpMap) -> Option<i32> {
    let mut best: Option<i32> = None;
    for (k, &v) in states.iter() {
        if k.fin && k.sp && k.ep && k.comps.is_empty() {
            best = Some(match best {
                None => v,
                Some(b) => b.min(v),
            });
        }
    }
    best
}

/// Element-level realisation length.  `relaxed=false` -> ell_T, `relaxed=true` -> ell_R.
fn realize_len(eps: i8, dl: u8, k: i32, a: &Lamps, relaxed: bool, lam_max: i32) -> Option<i32> {
    let ctx = Ctx { k, eps, dl, relaxed, lam_max };
    let mut hull: Vec<i32> = a.iter().filter(|&&(_, v)| v != 0).map(|&(p, _)| p).collect();
    if k > 0 {
        for j in 0..k {
            hull.push(j);
        }
    } else if k < 0 {
        for j in k..0 {
            hull.push(j);
        }
    }
    let lo = hull.iter().copied().chain(std::iter::once(0)).min().unwrap();
    let hi = hull.iter().copied().chain(std::iter::once(-1)).max().unwrap();
    let amap: HashMap<i32, i32> = a.iter().copied().collect();
    let mut states = init_dp();
    for j in (lo - 1)..=(hi + 1) {
        let aj = *amap.get(&j).unwrap_or(&0);
        states = site_step(&states, j, aj, f_of(j, k), &ctx);
        if states.is_empty() {
            return None;
        }
    }
    accept(&states)
}

// =====================================================================
// 3. c_pred -- the paper's closed form (route_b/c_formula.py).  Used only as an
//    independent cross-check in `validate`; it plays NO role in computing c_true.
// =====================================================================

fn sgn(x: i32) -> i32 {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

fn shield_right(k: i32, e: i8, dl: u8, b: i32) -> i32 {
    if k == 0 {
        return if e == 1 && dl == 0 { 0 } else { 1 };
    }
    if b.abs() >= 3 {
        return 1;
    }
    let s = sgn(b);
    if k > 0 {
        if dl == 1 { 1 } else if s == e as i32 { 1 } else { 0 }
    } else {
        if s == -1 { 1 } else { 0 }
    }
}

fn shield_left(k: i32, e: i8, dl: u8, b: i32) -> i32 {
    if k >= 0 {
        return 1;
    }
    if b.abs() >= 3 {
        return 1;
    }
    if dl == 0 { 1 } else if e as i32 == sgn(b) { 0 } else { 1 }
}

fn boundary_correction(e: i8, dl: u8, k: i32, a: &HashMap<i32, i32>) -> i32 {
    if k != 0 || dl != 0 {
        return 0;
    }
    let lev: Vec<i32> = a.iter().filter(|(&p, &v)| p <= -1 && v != 0).map(|(&p, _)| p).collect();
    let rev: Vec<i32> = a.iter().filter(|(&p, &v)| p >= 0 && v != 0).map(|(&p, _)| p).collect();
    if lev.is_empty() || rev.is_empty() {
        return 0;
    }
    if *lev.iter().max().unwrap() != -1 {
        return 0;
    }
    if *rev.iter().min().unwrap() == 0 {
        return 0;
    }
    if e == 1 {
        -1
    } else if *a.get(&-1).unwrap_or(&0) == 2 {
        1
    } else {
        0
    }
}

fn c_pred(eps: i8, dl: u8, k: i32, a: &Lamps) -> i32 {
    let amap: HashMap<i32, i32> = a.iter().copied().filter(|&(_, v)| v != 0).collect();
    let mut nz: Vec<i32> = amap.keys().copied().collect();
    nz.sort();
    let spine_l = 0.min(k);
    let spine_r = 0.max(k);
    let s_r = if k > 0 {
        *amap.get(&(k - 1)).unwrap_or(&0)
    } else if k < 0 {
        *amap.get(&-1).unwrap_or(&0)
    } else {
        0
    };
    let s_l = if k < 0 { *amap.get(&k).unwrap_or(&0) } else { 0 };
    let blocks_of = |edges: &Vec<i32>| -> Vec<Vec<i32>> {
        let mut bl: Vec<Vec<i32>> = Vec::new();
        for &p in edges.iter() {
            if let Some(last) = bl.last_mut() {
                if *last.last().unwrap() == p - 1 {
                    last.push(p);
                    continue;
                }
            }
            bl.push(vec![p]);
        }
        bl
    };
    let mut c = 0;
    let rr: Vec<i32> = nz.iter().copied().filter(|&p| p >= spine_r && f_of(p, k) == 0).collect();
    let rb = blocks_of(&rr);
    if !rb.is_empty() {
        c += 0.max((rb[0][0] - spine_r) - shield_right(k, eps, dl, s_r));
        for i in 1..rb.len() {
            c += 0.max((rb[i][0] - rb[i - 1][rb[i - 1].len() - 1] - 1) - 1);
        }
    }
    // left side: positions read outward (decreasing).  blocks_of expects the
    // "increasing by 1" adjacency test, so mirror the positions.
    let mut ll: Vec<i32> = nz.iter().copied().filter(|&p| p + 1 <= spine_l && f_of(p, k) == 0).collect();
    ll.sort_by(|x, y| y.cmp(x));
    let lm: Vec<i32> = ll.iter().map(|&p| -p).collect();
    let lbm = blocks_of(&lm);
    let lb: Vec<Vec<i32>> = lbm.iter().map(|b| b.iter().map(|&p| -p).collect()).collect();
    if !lb.is_empty() {
        c += 0.max((spine_l - lb[0][0] - 1) - shield_left(k, eps, dl, s_l));
        for i in 1..lb.len() {
            c += 0.max((lb[i - 1][lb[i - 1].len() - 1] - lb[i][0] - 1) - 1);
        }
    }
    c + boundary_correction(eps, dl, k, &amap)
}

// =====================================================================
// 4. VALIDATE.  The anti-circularity certificate.
// =====================================================================

fn cmd_validate(depth: usize, lam_max: i32) {
    let t0 = Instant::now();
    eprintln!("== validate: geodesic BFS to depth {}, lam_max = {} ==", depth, lam_max);
    let dist = group_bfs(depth, true);
    eprintln!("   ball size = {} elements   ({:.1}s)", dist.len(), t0.elapsed().as_secs_f64());

    let mut entries: Vec<(&Elt, u32)> = dist.iter().map(|(e, &d)| (e, d)).collect();
    entries.sort_by_key(|(_, d)| *d);
    let total = entries.len();
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(8);
    let chunk = (total + nthreads - 1) / nthreads;
    let counted = std::sync::atomic::AtomicUsize::new(0);
    let mut parts: Vec<(usize, usize, usize, usize, usize, usize, i32, Vec<String>, Vec<String>)> =
        Vec::new();
    std::thread::scope(|s| {
        let mut handles = Vec::new();
        for tix in 0..nthreads {
            let lo = tix * chunk;
            let hi = ((tix + 1) * chunk).min(total);
            let slice = &entries[lo.min(total)..hi];
            let counted = &counted;
            handles.push(s.spawn(move || {
                let mut n = 0usize;
                let (mut bad_t, mut bad_none, mut bad_ord, mut bad_par, mut bad_pred) =
                    (0usize, 0usize, 0usize, 0usize, 0usize);
                let mut max_c = 0i32;
                let mut ex_t: Vec<String> = Vec::new();
                let mut ex_pred: Vec<String> = Vec::new();
                for (g, d) in slice.iter() {
                    let d = *d;
                    n += 1;
                    let c = counted.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if c % 20000 == 0 && c > 0 {
                        eprintln!("   ... {}/{} elements checked", c, total);
                    }
                    let lt = realize_len(g.eps, g.dl, g.k, &g.a, false, lam_max);
                    let lr = realize_len(g.eps, g.dl, g.k, &g.a, true, lam_max);
                    match (lt, lr) {
                        (Some(lt), Some(lr)) => {
                            if lt != d as i32 {
                                bad_t += 1;
                                if ex_t.len() < 8 {
                                    ex_t.push(format!("{:?} BFS={} solve={}", g, d, lt));
                                }
                            }
                            if lr > lt {
                                bad_ord += 1;
                            }
                            let diff = d as i32 - lr;
                            if diff % 2 != 0 {
                                bad_par += 1;
                            }
                            let ctrue = diff / 2;
                            if ctrue > max_c {
                                max_c = ctrue;
                            }
                            let cp = c_pred(g.eps, g.dl, g.k, &g.a);
                            if cp != ctrue {
                                bad_pred += 1;
                                if ex_pred.len() < 8 {
                                    ex_pred.push(format!(
                                        "{:?} d={} relaxed={} c_true={} c_pred={}",
                                        g, d, lr, ctrue, cp
                                    ));
                                }
                            }
                        }
                        _ => {
                            bad_none += 1;
                        }
                    }
                }
                (n, bad_t, bad_none, bad_ord, bad_par, bad_pred, max_c, ex_t, ex_pred)
            }));
        }
        for h in handles {
            parts.push(h.join().unwrap());
        }
    });
    let mut n = 0usize;
    let (mut bad_t, mut bad_none, mut bad_ord, mut bad_par, mut bad_pred) = (0, 0, 0, 0, 0);
    let mut max_c = 0i32;
    let mut ex_t: Vec<String> = Vec::new();
    let mut ex_pred: Vec<String> = Vec::new();
    for p in parts.into_iter() {
        n += p.0;
        bad_t += p.1;
        bad_none += p.2;
        bad_ord += p.3;
        bad_par += p.4;
        bad_pred += p.5;
        max_c = max_c.max(p.6);
        for s in p.7 {
            if ex_t.len() < 8 {
                ex_t.push(s);
            }
        }
        for s in p.8 {
            if ex_pred.len() < 8 {
                ex_pred.push(s);
            }
        }
    }
    println!("VALIDATE depth={} lam_max={} elements={}", depth, lam_max, n);
    println!("  DP returned None                       : {}", bad_none);
    println!("  ell_T(DP) != geodesic BFS distance     : {}   <-- must be 0", bad_t);
    for s in ex_t.iter() {
        println!("      {}", s);
    }
    println!("  ell_R > ell_T                          : {}", bad_ord);
    println!("  (ell_T - ell_R) odd                    : {}", bad_par);
    println!("  c_true != c_pred (paper closed form)   : {}", bad_pred);
    for s in ex_pred.iter() {
        println!("      {}", s);
    }
    println!("  max c_true over the ball               : {}", max_c);
    println!("  wall {:.1}s", t0.elapsed().as_secs_f64());
}

// =====================================================================
// 5. MYHILL-NERODE CENSUS.
// =====================================================================

/// Canonical byte encoding of a normalised DP frontier (min cost subtracted).
/// Entries whose normalised cost exceeds `cut` are dropped (cut = i32::MAX means
/// no pruning; the honest upper bound uses no pruning).
fn norm_encode(m: &DpMap, cut: i32, buf: &mut Vec<u8>) {
    let mn = match m.values().min() {
        Some(&x) => x,
        None => {
            buf.push(0xFF);
            return;
        }
    };
    for (k, &v) in m.iter() {
        let nv = v - mn;
        if nv > cut {
            continue;
        }
        buf.push(if k.fin { 1 } else { 0 });
        buf.push(k.sp as u8);
        buf.push(k.ep as u8);
        buf.push(k.comps.len() as u8);
        for c in k.comps.iter() {
            buf.push(c.upp);
            buf.push(c.upm);
            buf.push(c.dnp);
            buf.push(c.dnm);
            buf.push(c.st as u8);
            buf.push(c.en as u8);
        }
        buf.extend_from_slice(&(nv as u32).to_le_bytes());
        buf.push(0xFE);
    }
    buf.push(0xFD);
}

#[derive(Clone, Debug)]
struct Root {
    k: i32,
    eps: i8,
    dl: u8,
    trav: Vec<i32>, // deposits on the travel edges min(0,k)..max(0,k)-1 -- odd
    /// OFF-SPINE LEFT CONTEXT, outermost first: deposits at positions
    /// min(0,k)-left.len() .. min(0,k)-1, all even.  The word read by the census is
    /// always the RIGHT side outward; the left side is frozen into the root.  Varying
    /// it is how side-independence gets tested rather than assumed.
    left: Vec<i32>,
}

struct MnCfg {
    roots: Vec<Root>,
    alpha: Vec<i32>,
    maxlen: usize,
    probe: usize,
    pmin: usize,
    lam: i32,
    cut: i32,
    verbose: bool,
    chk: usize,
    chk2: usize,
}

struct Node {
    t: DpMap,
    r: DpMap,
}

fn step_both(nd: &Node, j: i32, aj: i32, k: i32, eps: i8, dl: u8, lam: i32) -> Option<Node> {
    let ct = Ctx { k, eps, dl, relaxed: false, lam_max: lam };
    let cr = Ctx { k, eps, dl, relaxed: true, lam_max: lam };
    let fj = f_of(j, k);
    let t = site_step(&nd.t, j, aj, fj, &ct);
    let r = site_step(&nd.r, j, aj, fj, &cr);
    if t.is_empty() || r.is_empty() {
        return None;
    }
    Some(Node { t, r })
}

/// Close out at site `p` (deposit 0) and return c = (ell_T - ell_R)/2.
fn close_defect(nd: &Node, p: i32, k: i32, eps: i8, dl: u8, lam: i32) -> Option<i32> {
    let ct = Ctx { k, eps, dl, relaxed: false, lam_max: lam };
    let cr = Ctx { k, eps, dl, relaxed: true, lam_max: lam };
    let fj = f_of(p, k);
    let t = site_step(&nd.t, p, 0, fj, &ct);
    let r = site_step(&nd.r, p, 0, fj, &cr);
    let lt = accept(&t)?;
    let lr = accept(&r)?;
    if (lt - lr) % 2 != 0 {
        return None;
    }
    Some((lt - lr) / 2)
}

// ---------------------------------------------------------------------
// The residual (Myhill-Nerode) census.
//
// WHY THE COMPARED SUFFIXES END IN A BLOCK.  The defect of a profile is read on the
// ACTIVE SPAN: trailing gap edges beyond the outermost deposit are not edges of the
// element at all, and the paper's transducer accordingly "halts at the outermost block
// edge of that side".  A naive residual  c(wv) - c(w)  over unrestricted suffixes
// therefore separates 0^n from 0^m for every n /= m -- but it does so for the paper's
// own 4-state transducer just as much, so it measures the truncation convention and not
// the defect.  The right object is  w |-> c(w t)  on block-terminated profiles.  Every
// compared suffix here ends in a nonzero letter:
//     V(P) = { v t : v in Sigma^{<=P}, t in Sigma \ {0} },     SUPPORT = |V(P)|
// and the residual of w is  ( c(w u) - c(w t0) )_{u in V(P)},  t0 the first block letter.
// Equality of depth-P residual vectors IS Moore's ~_P; the printed table shows ~_P for
// P = pmin..probe together with its support, so a plateau can be seen to survive.
//
// STAGE 1 builds the concrete min-plus frontier automaton (states = normalised pairs of
// DP frontiers) and reads off, per state and letter, the pair of cost increments.  The
// DEFECT increment  delta = dT - dR  and the closing offset  z = clT - clR  turn the
// whole thing into an integer subsequential transducer:
//     2 c(w) = off(root) + sum_i delta(F_i, w_i) + z(F_|w|).
// STAGE 2 does all the Myhill-Nerode work on that transducer, so probe depth is cheap.
// ---------------------------------------------------------------------

fn state_key(nd: &Node, cut: i32, root_tag: Option<usize>) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::with_capacity(256);
    match root_tag {
        Some(r) => {
            buf.push(0xA0);
            buf.push(r as u8);
        }
        None => buf.push(0xA1),
    }
    norm_encode(&nd.t, cut, &mut buf);
    buf.push(0xFC);
    norm_encode(&nd.r, cut, &mut buf);
    buf
}

fn normalise(m: &mut DpMap) -> i32 {
    let mn = *m.values().min().unwrap();
    for v in m.values_mut() {
        *v -= mn;
    }
    mn
}

/// The integer transducer read off the min-plus frontier automaton.
struct Auto {
    nletters: usize,
    child: Vec<Vec<Option<usize>>>,
    delta: Vec<Vec<i32>>, // 2*(defect increment) on that letter
    zed: Vec<Option<i32>>,
    depth: Vec<usize>,
    word: Vec<Vec<i32>>,
    root: Vec<usize>,
    root_ids: Vec<usize>,
    root_off: Vec<i32>, // ell_T - ell_R offset accumulated in the boundary prefix
    /// true once this state's children have been computed.  A `None` child of an
    /// UNexplored state means "not looked at", not "infeasible"; confusing the two
    /// splits residual classes for free and manufactures exactly the kind of fake
    /// growth this tool exists to detect.  Every residual walk checks this flag.
    explored: Vec<bool>,
}

impl Auto {
    /// 2*c(w) for the word starting at state `s`; None if the profile is infeasible.
    fn twoc(&self, s0: usize, w: &[i32], letter_index: &HashMap<i32, usize>) -> Option<i32> {
        let mut s = s0;
        let mut acc = self.root_off[self.root[s0]];
        for &a in w.iter() {
            let ai = *letter_index.get(&a)?;
            acc += self.delta[s][ai];
            s = self.child[s][ai]?;
        }
        Some(acc + self.zed[s]?)
    }
}

fn build_auto(cfg: &MnCfg) -> Auto {
    let na = cfg.alpha.len();
    let mut nodes: Vec<Node> = Vec::new();
    let mut auto = Auto {
        nletters: na,
        child: vec![],
        delta: vec![],
        zed: vec![],
        depth: vec![],
        word: vec![],
        root: vec![],
        root_ids: vec![],
        root_off: vec![],
        explored: vec![],
    };
    let mut index: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut frontier: Vec<usize> = Vec::new();

    for (ri, root) in cfg.roots.iter().enumerate() {
        let lo = 0.min(root.k);
        let lo_all = lo - root.left.len() as i32;
        let start_pos = 0.max(root.k);
        let mut nd = Node { t: init_dp(), r: init_dp() };
        let mut ok = true;
        for j in (lo_all - 1)..start_pos {
            let aj = if j < lo {
                if j >= lo_all { root.left[(j - lo_all) as usize] } else { 0 }
            } else if f_of(j, root.k) != 0 {
                root.trav[(j - lo) as usize]
            } else {
                0
            };
            match step_both(&nd, j, aj, root.k, root.eps, root.dl, cfg.lam) {
                Some(x) => nd = x,
                None => {
                    eprintln!("   root {:?}: infeasible boundary prefix at site {}", root, j);
                    ok = false;
                    break;
                }
            }
        }
        auto.root_off.push(0);
        if !ok {
            auto.root_ids.push(usize::MAX);
            continue;
        }
        let ot = normalise(&mut nd.t);
        let or = normalise(&mut nd.r);
        auto.root_off[ri] = ot - or;
        let key = state_key(&nd, cfg.cut, Some(ri));
        let id = *index.entry(key).or_insert_with(|| {
            let id = nodes.len();
            nodes.push(nd);
            auto.child.push(vec![None; na]);
            auto.delta.push(vec![0; na]);
            auto.zed.push(None);
            auto.depth.push(0);
            auto.word.push(vec![]);
            auto.root.push(ri);
            auto.explored.push(false);
            id
        });
        auto.root_ids.push(id);
        frontier.push(id);
    }

    let horizon = cfg.maxlen + cfg.probe + 2;
    for _n in 0..horizon {
        let mut newf: Vec<usize> = Vec::new();
        for &sid in frontier.iter() {
            let root = cfg.roots[auto.root[sid]].clone();
            let pos = 0.max(root.k) + auto.depth[sid] as i32;
            for ai in 0..na {
                let a = cfg.alpha[ai];
                let ch = step_both(&nodes[sid], pos, a, root.k, root.eps, root.dl, cfg.lam);
                match ch {
                    None => {}
                    Some(mut c) => {
                        let dt = normalise(&mut c.t);
                        let dr = normalise(&mut c.r);
                        auto.delta[sid][ai] = dt - dr;
                        let key = state_key(&c, cfg.cut, None);
                        let cid = match index.get(&key) {
                            Some(&id) => id,
                            None => {
                                let id = nodes.len();
                                index.insert(key, id);
                                nodes.push(c);
                                auto.child.push(vec![None; na]);
                                auto.delta.push(vec![0; na]);
                                auto.zed.push(None);
                                auto.depth.push(auto.depth[sid] + 1);
                                let mut w = auto.word[sid].clone();
                                w.push(a);
                                auto.word.push(w);
                                auto.root.push(auto.root[sid]);
                                auto.explored.push(false);
                                newf.push(id);
                                id
                            }
                        };
                        auto.child[sid][ai] = Some(cid);
                    }
                }
            }
            auto.explored[sid] = true;
        }
        frontier = newf;
        if frontier.is_empty() {
            break;
        }
    }
    // closing offsets
    for s in 0..nodes.len() {
        let root = &cfg.roots[auto.root[s]];
        let pos = 0.max(root.k) + auto.depth[s] as i32;
        let ct = Ctx { k: root.k, eps: root.eps, dl: root.dl, relaxed: false, lam_max: cfg.lam };
        let cr = Ctx { k: root.k, eps: root.eps, dl: root.dl, relaxed: true, lam_max: cfg.lam };
        let fj = f_of(pos, root.k);
        let t = site_step(&nodes[s].t, pos, 0, fj, &ct);
        let r = site_step(&nodes[s].r, pos, 0, fj, &cr);
        auto.zed[s] = match (accept(&t), accept(&r)) {
            (Some(a), Some(b)) => Some(a - b),
            _ => None,
        };
    }
    auto
}

fn support_at(cfg: &MnCfg, p: usize) -> usize {
    let a = cfg.alpha.len();
    let nz = cfg.alpha.iter().filter(|&&x| x != 0).count();
    let vnodes: usize = (0..=p).map(|m| a.pow(m as u32)).sum();
    vnodes * nz
}

/// Residual vector at probe depth `p`, computed purely on the transducer.
/// Returns None if the reference suffix is infeasible, or if the walk ever reaches a
/// state whose children were never explored (in which case the vector would encode the
/// exploration horizon rather than the defect -- the artifact this tool must not make).
fn residual_vec(auto: &Auto, cfg: &MnCfg, s: usize, p: usize, offhorizon: &mut usize) -> Option<Vec<i32>> {
    let nzi: Vec<usize> = (0..cfg.alpha.len()).filter(|&i| cfg.alpha[i] != 0).collect();
    let mut out: Vec<i32> = Vec::with_capacity(support_at(cfg, p));
    let mut bad = false;
    fn walk(
        auto: &Auto,
        cfg: &MnCfg,
        s: Option<usize>,
        acc: i32,
        d: usize,
        p: usize,
        nzi: &[usize],
        out: &mut Vec<i32>,
        bad: &mut bool,
    ) {
        if let Some(si) = s {
            if !auto.explored[si] {
                *bad = true;
            }
        }
        for &t in nzi.iter() {
            let v = match s {
                None => i32::MIN,
                Some(s) => match auto.child[s][t] {
                    None => i32::MIN,
                    Some(c) => match auto.zed[c] {
                        None => i32::MIN,
                        Some(z) => acc + auto.delta[s][t] + z,
                    },
                },
            };
            out.push(v);
        }
        if d == p {
            return;
        }
        for a in 0..auto.nletters {
            match s {
                None => walk(auto, cfg, None, acc, d + 1, p, nzi, out, bad),
                Some(s) => {
                    let ns = auto.child[s][a];
                    walk(auto, cfg, ns, acc + auto.delta[s][a], d + 1, p, nzi, out, bad)
                }
            }
        }
    }
    walk(auto, cfg, Some(s), 0, 0, p, &nzi, &mut out, &mut bad);
    if bad {
        *offhorizon += 1;
        return None;
    }
    let base = out[0];
    if base == i32::MIN {
        return None;
    }
    Some(out.iter().map(|&x| if x == i32::MIN { i32::MIN } else { x - base }).collect())
}

fn cmd_mn(cfg: &MnCfg) {
    let t0 = Instant::now();
    let nz: Vec<i32> = cfg.alpha.iter().copied().filter(|&x| x != 0).collect();
    let mut letter_index: HashMap<i32, usize> = HashMap::new();
    for (i, &a) in cfg.alpha.iter().enumerate() {
        letter_index.insert(a, i);
    }
    println!("== MN residual census of the TRUE defect ==");
    println!("   roots     : {} boundary conditions", cfg.roots.len());
    for r in cfg.roots.iter() {
        if cfg.roots.len() <= 40 {
            println!(
                "               k={:<3} eps={:<3} delta={} trav={:?} left={:?}",
                r.k, r.eps, r.dl, r.trav, r.left
            );
        }
    }
    println!("   alphabet  : {:?}   (block letters {:?})", cfg.alpha, nz);
    println!(
        "   maxlen L  : {}    probe P : {}..{}    lam : {}    cut : {}",
        cfg.maxlen,
        cfg.pmin,
        cfg.probe,
        cfg.lam,
        if cfg.cut == i32::MAX { -1 } else { cfg.cut }
    );

    // ---------------- stage 1: the concrete transducer ----------------
    let auto = build_auto(cfg);
    let ns = auto.child.len();
    let mut cnt_by_depth: Vec<usize> = vec![0; cfg.maxlen + cfg.probe + 4];
    for s in 0..ns {
        cnt_by_depth[auto.depth[s]] += 1;
    }
    println!();
    println!("  concrete min-plus frontier states, by word length:");
    print!("   ");
    for d in 0..=cfg.maxlen {
        print!(" {}", cnt_by_depth[d]);
    }
    println!("     total {}", ns);
    println!("  (this automaton is the DP itself; it need not be finite -- only the defect quotient must be)");

    // ---------------- stage 1b: end-to-end check of the transducer ----------------
    // Re-derive c for every word of length <= chk directly from realize_len on the group
    // element, and compare with the transducer.  This validates the whole pipeline
    // (frontier identification across depths, normalisation, closing offsets).
    let chk = cfg.chk.min(cfg.maxlen);
    let mut nchk = 0usize;
    let mut badchk = 0usize;
    let mut ex: Vec<String> = Vec::new();
    for (ri, root) in cfg.roots.iter().enumerate() {
        if auto.root_ids[ri] == usize::MAX {
            continue;
        }
        let lo = 0.min(root.k);
        let start_pos = 0.max(root.k);
        let mut all: Vec<Vec<i32>> = vec![vec![]];
        let mut cur: Vec<Vec<i32>> = vec![vec![]];
        for _ in 0..chk {
            let mut nx = Vec::new();
            for w in cur.iter() {
                for &a in cfg.alpha.iter() {
                    let mut x = w.clone();
                    x.push(a);
                    nx.push(x);
                }
            }
            all.extend(nx.iter().cloned());
            cur = nx;
        }
        for w in all.iter() {
            let mut a: Lamps = Vec::new();
            for i in 0..root.left.len() {
                let p = lo - root.left.len() as i32 + i as i32;
                if root.left[i] != 0 {
                    a.push((p, root.left[i]));
                }
            }
            for i in 0..root.trav.len() {
                let p = lo + i as i32;
                if root.trav[i] != 0 {
                    a.push((p, root.trav[i]));
                }
            }
            for (i, &v) in w.iter().enumerate() {
                if v != 0 {
                    a.push((start_pos + i as i32, v));
                }
            }
            a.sort();
            let lt = realize_len(root.eps, root.dl, root.k, &a, false, cfg.lam);
            let lr = realize_len(root.eps, root.dl, root.k, &a, true, cfg.lam);
            let direct = match (lt, lr) {
                (Some(x), Some(y)) => Some(x - y),
                _ => None,
            };
            let viaauto = auto.twoc(auto.root_ids[ri], w, &letter_index);
            nchk += 1;
            if direct != viaauto {
                badchk += 1;
                if ex.len() < 6 {
                    ex.push(format!("root {:?} word {:?}: direct 2c={:?} transducer 2c={:?}", root, w, direct, viaauto));
                }
            }
        }
    }
    println!();
    println!(
        "  transducer vs direct DP on all {} profiles of length <= {} : {} mismatches",
        nchk, chk, badchk
    );
    for s in ex.iter() {
        println!("     {}", s);
    }
    if badchk > 0 {
        println!("  ABORT: the transducer does not reproduce the DP.");
        return;
    }

    // ---------------- stage 1c: the paper's closed form on long profiles ----------------
    let chk2 = cfg.chk2.min(cfg.maxlen);
    let mut n2 = 0usize;
    let mut bad2 = 0usize;
    let mut ex2: Vec<String> = Vec::new();
    for (ri, root) in cfg.roots.iter().enumerate() {
        if auto.root_ids[ri] == usize::MAX {
            continue;
        }
        let lo = 0.min(root.k);
        let start_pos = 0.max(root.k);
        let mut cur: Vec<Vec<i32>> = vec![vec![]];
        let mut all: Vec<Vec<i32>> = vec![vec![]];
        for _ in 0..chk2 {
            let mut nx = Vec::new();
            for w in cur.iter() {
                for &a in cfg.alpha.iter() {
                    let mut x = w.clone();
                    x.push(a);
                    nx.push(x);
                }
            }
            all.extend(nx.iter().cloned());
            cur = nx;
        }
        for w in all.iter() {
            let mut a: Lamps = Vec::new();
            for i in 0..root.left.len() {
                let p = lo - root.left.len() as i32 + i as i32;
                if root.left[i] != 0 {
                    a.push((p, root.left[i]));
                }
            }
            for i in 0..root.trav.len() {
                let p = lo + i as i32;
                if root.trav[i] != 0 {
                    a.push((p, root.trav[i]));
                }
            }
            for (i, &v) in w.iter().enumerate() {
                if v != 0 {
                    a.push((start_pos + i as i32, v));
                }
            }
            a.sort();
            let two = match auto.twoc(auto.root_ids[ri], w, &letter_index) {
                Some(x) => x,
                None => continue,
            };
            n2 += 1;
            let cp = c_pred(root.eps, root.dl, root.k, &a);
            if two != 2 * cp {
                bad2 += 1;
                if ex2.len() < 8 {
                    ex2.push(format!(
                        "k={} eps={} dl={} a={:?}: c_true={} c_pred={}",
                        root.k, root.eps, root.dl, a, two as f64 / 2.0, cp
                    ));
                }
            }
        }
    }
    println!(
        "  paper closed form c_pred vs c_true on all {} profiles of length <= {} : {} mismatches",
        n2, chk2, bad2
    );
    for s in ex2.iter() {
        println!("     {}", s);
    }

    // ---------------- stage 2: Myhill-Nerode ----------------
    // Only states within the census horizon take part: a state of depth <= maxlen has
    // its whole probe-depth suffix tree inside the explored region.
    let mut offh = 0usize;
    let mut resmax: Vec<Option<Vec<i32>>> = Vec::with_capacity(ns);
    let mut ncensus = 0usize;
    for s in 0..ns {
        if auto.depth[s] > cfg.maxlen {
            resmax.push(None);
            continue;
        }
        ncensus += 1;
        resmax.push(residual_vec(&auto, cfg, s, cfg.probe, &mut offh));
    }
    let nbad = (0..ns).filter(|&i| auto.depth[i] <= cfg.maxlen && resmax[i].is_none()).count();
    println!();
    println!("  census states (word length <= {}) : {}", cfg.maxlen, ncensus);
    if nbad > 0 {
        println!("  {} of them excluded: infeasible reference suffix", nbad);
    }
    if offh > 0 {
        println!("  *** {} residual walks ran past the exploration horizon -- raise --len ***", offh);
    }
    println!("   P    support    residual classes (~_P)");
    let mut prev: Option<usize> = None;
    let mut stable_from: Option<usize> = None;
    for p in cfg.pmin..=cfg.probe {
        let sup = support_at(cfg, p);
        let mut set: HashSet<&[i32]> = HashSet::new();
        for r in resmax.iter().flatten() {
            set.insert(&r[..sup]);
        }
        let cnt = set.len();
        let note = match prev {
            Some(x) if x == cnt => {
                if stable_from.is_none() {
                    stable_from = Some(p - 1);
                }
                "  (unchanged)"
            }
            Some(_) => {
                stable_from = None;
                "  <-- REFINED"
            }
            None => "",
        };
        println!("  {:>2} {:>10} {:>22}{}", p, sup, cnt, note);
        prev = Some(cnt);
    }

    // quotient at the deepest probe
    let sup = support_at(cfg, cfg.probe);
    let mut cls_of: Vec<Option<usize>> = vec![None; ns];
    let mut cls_rep: Vec<usize> = Vec::new();
    let mut cls_index: HashMap<Vec<i32>, usize> = HashMap::new();
    for i in 0..ns {
        if let Some(r) = &resmax[i] {
            let key = r[..sup].to_vec();
            let id = match cls_index.get(&key) {
                Some(&id) => id,
                None => {
                    let id = cls_rep.len();
                    cls_index.insert(key, id);
                    cls_rep.push(i);
                    id
                }
            };
            cls_of[i] = Some(id);
        }
    }
    let ncls = cls_rep.len();

    // congruence / closure check.  Only states whose children were all explored take
    // part (depth < maxlen).
    let mut by_class: Vec<Vec<usize>> = vec![vec![]; ncls];
    for i in 0..ns {
        if auto.depth[i] + 1 <= cfg.maxlen && auto.explored[i] {
            if let Some(c) = cls_of[i] {
                by_class[c].push(i);
            }
        }
    }
    // The canonical Mealy output of class [w] on letter a is  rho_w(a) = chat(wa)-chat(w),
    // where chat(w) = c(w t0).  That number is ALREADY an entry of the residual vector
    // (the entry at suffix v=a, t=t0), so it is constant on a class by construction and
    // needs no separate check.  What does need checking is that the transition is well
    // defined: w ~ w'  =>  wa ~ w'a.  NOTE the DP's own increment auto.delta is a
    // DIFFERENT (lazy) output schedule -- it defers the gap charge until a block arrives,
    // so it is unbounded and is NOT the Mealy output; using it here would report
    // violations that are pure bookkeeping.
    let sprev = if cfg.probe == 0 { 0 } else { support_at(cfg, cfg.probe - 1) };
    let nznum = cfg.alpha.iter().filter(|&&x| x != 0).count();
    let rho_index = |ai: usize| -> usize { nznum + ai * sprev };
    let mut viol = 0usize;
    let mut ex3: Vec<String> = Vec::new();
    let mut trans: Vec<Vec<Option<usize>>> = vec![vec![None; auto.nletters]; ncls];
    let mut outp: Vec<Vec<Option<i32>>> = vec![vec![None; auto.nletters]; ncls];
    for c in 0..ncls {
        for ai in 0..auto.nletters {
            let mut seen: Option<Option<usize>> = None;
            for &i in by_class[c].iter() {
                let ch = auto.child[i][ai].and_then(|j| cls_of[j]);
                match seen {
                    None => {
                        seen = Some(ch);
                        trans[c][ai] = ch;
                        if cfg.probe >= 1 {
                            let r = resmax[i].as_ref().unwrap();
                            let e = r[rho_index(ai)];
                            outp[c][ai] = if e == i32::MIN { None } else { Some(e) };
                        }
                    }
                    Some(pc) => {
                        if pc != ch {
                            viol += 1;
                            if ex3.len() < 10 {
                                ex3.push(format!(
                                    "class {} letter {}: {:?} -> class {:?} but {:?} -> class {:?}",
                                    c, cfg.alpha[ai], auto.word[by_class[c][0]], pc,
                                    auto.word[i], ch
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    let uncovered = (0..ncls).filter(|&c| by_class[c].is_empty()).count();
    // also: the closing output must be constant on a class
    let mut zviol = 0usize;
    for c in 0..ncls {
        let mut z: Option<Option<i32>> = None;
        for &i in by_class[c].iter() {
            match z {
                None => z = Some(auto.zed[i]),
                Some(p) => {
                    if p != auto.zed[i] {
                        zviol += 1;
                    }
                }
            }
        }
    }

    println!();
    println!("  QUOTIENT at probe P={}, support {}", cfg.probe, sup);
    println!("    residual classes (candidate MN states)   N = {}", ncls);
    println!("    classes with no fully-expanded member      = {}   (must be 0)", uncovered);
    println!("    right-congruence violations                = {}   (must be 0)", viol);
    for s in ex3.iter() {
        println!("       {}", s);
    }
    println!("    closing-output violations                  = {}   (must be 0)", zviol);
    if cfg.verbose {
        println!("    minimal machine (state: shortest word | letter -> state / 2*rho | 2*chat offset):");
        for c in 0..ncls {
            let i = cls_rep[c];
            let mut tr = String::new();
            for ai in 0..auto.nletters {
                tr.push_str(&format!(
                    "  {}->{}/{}",
                    cfg.alpha[ai],
                    match trans[c][ai] {
                        Some(x) => format!("q{}", x),
                        None => "-".to_string(),
                    },
                    match outp[c][ai] {
                        Some(x) => format!("{}", x),
                        None => "-".to_string(),
                    }
                ));
            }
            println!(
                "      q{:<3} root {} k={} eps={} dl={} w={:?} {} | z={:?}",
                c,
                auto.root[i],
                cfg.roots[auto.root[i]].k,
                cfg.roots[auto.root[i]].eps,
                cfg.roots[auto.root[i]].dl,
                auto.word[i],
                tr,
                auto.zed[i]
            );
        }
    }
    println!();
    if bad2 > 0 {
        println!("  *** {} c_pred mismatches above: the DP is being run outside its validity", bad2);
        println!("  *** domain (usually a --cut that prunes optimal frontier entries).  The state");
        println!("  *** count below is NOT a statement about the true defect.");
    }
    if viol == 0 && uncovered == 0 && zviol == 0 && stable_from.is_some() && bad2 == 0 {
        println!(
            "  VERDICT  FINITE-STATE on this alphabet and root set, N = {} states.",
            ncls
        );
        println!(
            "           ~_P stable from P = {} through P = {} (support {} -> {}), and the",
            stable_from.unwrap(),
            cfg.probe,
            support_at(cfg, stable_from.unwrap()),
            sup
        );
        println!("           depth-{} partition is a right congruence with all classes reachable.", cfg.probe);
    } else if viol > 0 || zviol > 0 {
        println!("  VERDICT  the depth-{} partition is NOT a congruence: not a machine at this probe depth.", cfg.probe);
    } else {
        println!("  VERDICT  still refining at probe depth {}: inconclusive, push --probe.", cfg.probe);
    }
    println!("  wall {:.1}s", t0.elapsed().as_secs_f64());
}



// =====================================================================
// 6. self test on tiny hand-checkable data
// =====================================================================

fn cmd_selftest() {
    // ball sizes of W_gen: the canonical u_d sequence
    let want = [1usize, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351];
    let dist = group_bfs(11, false);
    let mut layer = vec![0usize; 12];
    for (_, &d) in dist.iter() {
        layer[d as usize] += 1;
    }
    let ok = (0..12).all(|i| layer[i] == want[i]);
    println!("selftest  u_0..u_11 = {:?}", &layer[..12]);
    println!("selftest  expected  = {:?}", want);
    println!("selftest  growth sequence: {}", if ok { "PASS" } else { "FAIL" });

    // the four deposit-free elements at k=0
    for &(e, d, want) in [(1i8, 0u8, 0i32), (1, 1, 1), (-1, 1, 1), (-1, 0, 2)].iter() {
        let got = realize_len(e, d, 0, &vec![], false, 2);
        println!("selftest  empty profile eps={:+} delta={} -> ell_T = {:?} (want {})", e, d, got, want);
    }
}

// =====================================================================

fn parse_ints(s: &str) -> Vec<i32> {
    s.split(',')
        .filter(|x| !x.trim().is_empty())
        .map(|x| x.trim().parse::<i32>().expect("int"))
        .collect()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage:");
        eprintln!("  mndefect validate <depth> [lam_max]");
        eprintln!("  mndefect mn --k K --eps E --delta D [--b B[,B..]] --alpha \"0,2,-2\" --len L --probe P [--lam LAM] [--cut C]");
        eprintln!("  mndefect selftest");
        std::process::exit(2);
    }
    match args[1].as_str() {
        "selftest" => cmd_selftest(),
        "enum" => { let n: i32 = args[2].parse().unwrap(); cmd_enum(n, args.get(3).is_some()); }
        "ucount" => { let d: usize = args[2].parse().unwrap(); let dist = bfs_parent(d); let mut t = vec![[0u64;3]; d+1]; let mut cc: BTreeMap<(i32,i32,i32),u64> = BTreeMap::new(); let full = args.get(3).is_some(); let mut y2 = vec![[0u64;3]; d+1];
            for (g,&(dd,_)) in dist.iter() { let sg=(g.k.signum()+1) as usize; t[dd as usize][sg]+=1;
              if full { let cp = c_pred(g.eps,g.dl,g.k,&g.a); let lr = lr_closed(g.eps,g.dl,g.k,&g.a); *cc.entry((g.k.signum(), dd as i32 - lr - 2*cp, 0)).or_insert(0)+=1; let w = 2*(dd as i32) - lr; if (w as usize) <= d { y2[w as usize][sg]+=1; } } }
            for i in 0..=d { println!("U {} {} {} {}", i, t[i][0], t[i][1], t[i][2]); } for i in 0..=d { println!("Y2 {} {} {} {}", i, y2[i][0], y2[i][1], y2[i][2]); } println!("check(sgn, lT-lR-2cpred): {:?}", cc); }
        "ctrue" => { let d: usize = args[2].parse().unwrap(); cmd_ctrue(d); }
        "ksplit" => { let d: usize = args[2].parse().unwrap(); let l: i32 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(2); cmd_ksplit(d, l); }
        "validate" => {
            let depth: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(14);
            let lam: i32 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(2);
            cmd_validate(depth, lam);
        }
        "mn" => {
            let mut cfg = MnCfg {
                roots: vec![],
                alpha: vec![0, 2, -2],
                maxlen: 8,
                probe: 4,
                pmin: 1,
                lam: 2,
                cut: i32::MAX,
                verbose: false,
                chk: 5,
                chk2: 9,
            };
            // default single root, overridden by --roots
            let (mut k, mut eps, mut dl, mut trav): (i32, i8, u8, Vec<i32>) = (0, 1, 0, vec![]);
            let mut roots_spec: Option<String> = None;
            let mut i = 2;
            while i < args.len() {
                let key = args[i].as_str();
                if key == "-v" {
                    cfg.verbose = true;
                    i += 1;
                    continue;
                }
                let val = args.get(i + 1).cloned().unwrap_or_default();
                match key {
                    "--k" => k = val.parse().unwrap(),
                    "--eps" => eps = val.parse().unwrap(),
                    "--delta" => dl = val.parse().unwrap(),
                    "--b" => trav = parse_ints(&val),
                    "--roots" => roots_spec = Some(val),
                    "--alpha" => cfg.alpha = parse_ints(&val),
                    "--len" => cfg.maxlen = val.parse().unwrap(),
                    "--probe" => cfg.probe = val.parse().unwrap(),
                    "--pmin" => cfg.pmin = val.parse().unwrap(),
                    "--lam" => cfg.lam = val.parse().unwrap(),
                    "--cut" => cfg.cut = val.parse().unwrap(),
                    "--chk" => cfg.chk = val.parse().unwrap(),
                    "--chk2" => cfg.chk2 = val.parse().unwrap(),
                    _ => {
                        eprintln!("unknown flag {}", key);
                        std::process::exit(2);
                    }
                }
                i += 2;
            }
            // --roots "k:eps:delta:b1,b2|k:eps:delta|..."
            match roots_spec {
                Some(spec) => {
                    for part in spec.split('|') {
                        if part.trim().is_empty() {
                            continue;
                        }
                        let f: Vec<&str> = part.split(':').collect();
                        let rk: i32 = f[0].trim().parse().unwrap();
                        let re: i8 = f[1].trim().parse().unwrap();
                        let rd: u8 = f[2].trim().parse().unwrap();
                        let rb: Vec<i32> =
                            if f.len() > 3 { parse_ints(f[3]) } else { vec![] };
                        let rl: Vec<i32> =
                            if f.len() > 4 { parse_ints(f[4]) } else { vec![] };
                        if rb.len() != rk.unsigned_abs() as usize {
                            eprintln!(
                                "root {}: needs {} travel deposits, got {}",
                                part,
                                rk.abs(),
                                rb.len()
                            );
                            std::process::exit(2);
                        }
                        cfg.roots.push(Root { k: rk, eps: re, dl: rd, trav: rb, left: rl });
                    }
                }
                None => {
                    if trav.len() != k.unsigned_abs() as usize {
                        eprintln!("--b must supply {} travel deposits for k={}", k.abs(), k);
                        std::process::exit(2);
                    }
                    cfg.roots.push(Root { k, eps, dl, trav, left: vec![] });
                }
            }
            cmd_mn(&cfg);
        }
        other => {
            eprintln!("unknown mode {}", other);
            std::process::exit(2);
        }
    }
}

// ===================== room 49: k* sign split =====================
fn apply_gen(e: &Elt, g: u8) -> Elt {
    match g {
        0 => Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, a: e.a.clone() },
        1 => Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, a: e.a.clone() },
        _ => if e.dl == 0 {
            Elt { eps: e.eps, dl: 1, k: e.k - 1, a: lamp_add(&e.a, e.k - 1, e.eps as i32) }
        } else {
            Elt { eps: e.eps, dl: 0, k: e.k + 1, a: lamp_add(&e.a, e.k, -(e.eps as i32)) }
        },
    }
}
fn bfs_parent(maxd: usize) -> HashMap<Elt, (u32, u8)> {
    let ident = Elt { eps: 1, dl: 0, k: 0, a: vec![] };
    let mut dist: HashMap<Elt, (u32, u8)> = HashMap::new();
    dist.insert(ident.clone(), (0, 255));
    let mut frontier = vec![ident];
    for d in 0..maxd {
        let mut next = Vec::new();
        for e in frontier.iter() {
            for g in 0..3u8 {
                let c = apply_gen(e, g);
                if !dist.contains_key(&c) { dist.insert(c.clone(), ((d + 1) as u32, g)); next.push(c); }
            }
        }
        eprintln!("   BFS d={} layer {} cum {}", d + 1, next.len(), dist.len());
        frontier = next;
    }
    dist
}
/// paper2 cor:lRclosed + cor:localcost closed form
fn lr_closed(eps: i8, dl: u8, k: i32, a: &Lamps) -> i32 {
    let amap: HashMap<i32, i32> = a.iter().copied().collect();
    let mut hull: Vec<i32> = a.iter().map(|&(p, _)| p).collect();
    if k > 0 { for j in 0..k { hull.push(j); } } else if k < 0 { for j in k..0 { hull.push(j); } }
    let lo = hull.iter().copied().chain(std::iter::once(0)).min().unwrap();
    let hi = hull.iter().copied().chain(std::iter::once(-1)).max().unwrap();
    let d = |j: i32| -> i32 { if j < lo || j > hi { 0 } else { *amap.get(&j).unwrap_or(&0) } };
    let mut tot = 0;
    for j in lo..=hi {
        let v = d(j).abs().max(f_of(j, k).abs());
        tot += if v == 0 { 2 } else { v };
    }
    let e = eps as i32;
    for s in lo..=(hi + 1) {
        let al = d(s - 1) - (if s == 0 { 1 } else { 0 }) + (if s == k && dl == 0 { e } else { 0 });
        let be = d(s) - (if s == k && dl == 1 { e } else { 0 });
        tot += al.abs().max(be.abs());
    }
    tot
}
fn cmd_ksplit(depth: usize, lam: i32) {
    let t0 = Instant::now();
    let dist = bfs_parent(depth);
    let ident = Elt { eps: 1, dl: 0, k: 0, a: vec![] };
    // tallies[sgn+1][lr] and [sgn+1][(lr,c)] ; mismatches by sign
    let mut tal: [BTreeMap<(i32, i32), u64>; 3] = [BTreeMap::new(), BTreeMap::new(), BTreeMap::new()];
    let mut bad_cf = [0u64; 3]; let mut ncnt = [0u64; 3];
    let mut bad_inv_lr = 0u64; let mut bad_inv_k = 0u64; let mut bad_inv_lt = 0u64; let mut inv_marker: BTreeMap<(i8,u8,i8,u8),u64> = BTreeMap::new();
    let mut ex: Vec<String> = Vec::new();
    let mut lrcache: HashMap<Elt, i32> = HashMap::new();
    let mut idx = 0u64;
    for (g, &(d, _)) in dist.iter() {
        idx += 1; if idx % 200000 == 0 { eprintln!("  {} / {}  {:.0}s", idx, dist.len(), t0.elapsed().as_secs_f64()); }
        let sg = (g.k.signum() + 1) as usize;
        ncnt[sg] += 1;
        let lr = match lrcache.get(g) { Some(&v) => v, None => realize_len(g.eps, g.dl, g.k, &g.a, true, lam).unwrap_or(-999) };
        let cf = lr_closed(g.eps, g.dl, g.k, &g.a);
        if cf != lr { bad_cf[sg] += 1; if ex.len() < 10 { ex.push(format!("{:?} lr={} closed={}", g, lr, cf)); } }
        let c2 = d as i32 - lr;
        *tal[sg].entry((lr, c2)).or_insert(0) += 1;
        if std::env::var("DUMP").is_ok() { println!("E {} {} {} {} {} {:?}", g.eps, g.dl, g.k, d, lr, g.a); }
        // inverse: reconstruct word, apply reversed
        let mut word = Vec::new(); let mut cur = g.clone();
        while cur != ident { let gg = dist[&cur].1; word.push(gg); cur = apply_gen(&cur, gg); }
        // word lists ops from g back to identity: g = ops applied in order word.rev()
        let mut inv = ident.clone();
        for &gg in word.iter() { inv = apply_gen(&inv, gg); }
        match dist.get(&inv) { Some(&(di, _)) => { if di != d { bad_inv_lt += 1; } }, None => { bad_inv_lt += 1; } }
        if inv.k != -g.k { bad_inv_k += 1; }
        let lri = realize_len(inv.eps, inv.dl, inv.k, &inv.a, true, lam).unwrap_or(-999);
        lrcache.insert(inv.clone(), lri);
        if lri != lr { bad_inv_lr += 1; if ex.len() < 20 { ex.push(format!("INV {:?} lr={} ; inv {:?} lr={}", g, lr, inv, lri)); } }
        *inv_marker.entry((g.eps, g.dl, inv.eps, inv.dl)).or_insert(0) += 1;
    }
    println!("KSPLIT depth={} lam={} ball={}", depth, lam, dist.len());
    for (i, nm) in ["k<0", "k=0", "k>0"].iter().enumerate() {
        println!("  {}: elements {}  closed-form mismatches {}", nm, ncnt[i], bad_cf[i]);
    }
    println!("  inversion: l_T mismatch {}  k != -k {}  l_R mismatch {}", bad_inv_lt, bad_inv_k, bad_inv_lr);
    println!("  marker map (eps,dl)->(eps',dl') counts: {:?}", inv_marker);
    for s in ex.iter() { println!("    {}", s); }
    // compare tallies k<0 vs k>0 over COMPLETE range: l_T<=depth => all (lr,2c) with lr+2c<=depth
    let mut diff = 0; let mut rows = 0;
    let keys: std::collections::BTreeSet<(i32,i32)> = tal[0].keys().chain(tal[2].keys()).copied().collect();
    for kk in keys.iter() { rows += 1; let a = tal[0].get(kk).copied().unwrap_or(0); let b = tal[2].get(kk).copied().unwrap_or(0); if a != b { diff += 1; } }
    println!("  (l_R, 2c) tally cells {}  cells with #k<0 != #k>0: {}", rows, diff);
    // l_R series by sector restricted to complete range lr <= ? (l_T <= depth only) : print by l_T=lr+2c
    for sg in [0usize, 2] {
        let mut byl: BTreeMap<i32, u64> = BTreeMap::new();
        for (&(lr, c2), &n) in tal[sg].iter() { let _ = c2; *byl.entry(lr).or_insert(0) += n; }
        println!("  sector {} counts by l_R (incomplete above depth/..): {:?}", if sg==0 {"k<0"} else {"k>0"}, byl);
    }
    println!("  wall {:.1}s", t0.elapsed().as_secs_f64());
}

// ===== room 49: complete coordinate enumeration by closed-form l_R, split by sgn k =====
struct En { n: i32, k: i32, eps: i32, dl: u8, lo: i32, hi: i32, d: Vec<i32>, tal: Vec<u64>, dpchk: bool, bad: u64, chk: u64 }
fn site_cost(en: &En, s: i32, dm: i32, ds: i32) -> i32 {
    let al = dm - (if s == 0 { 1 } else { 0 }) + (if s == en.k && en.dl == 0 { en.eps } else { 0 });
    let be = ds - (if s == en.k && en.dl == 1 { en.eps } else { 0 });
    al.abs().max(be.abs())
}
fn en_rec(en: &mut En, j: i32, part: i32) {
    if part > en.n { return; }
    let dprev = if j - 1 >= en.lo && j - 1 <= en.hi { en.d[(j - 1 - en.lo) as usize] } else { 0 };
    if j > en.hi {
        let tot = part + site_cost(en, j, dprev, 0);
        if tot <= en.n {
            en.tal[tot as usize] += 1;
            if en.dpchk && tot <= 11 {
                let a: Lamps = (en.lo..=en.hi).filter_map(|p| { let v = en.d[(p - en.lo) as usize]; if v != 0 { Some((p, v)) } else { None } }).collect();
                en.chk += 1;
                match realize_len(en.eps as i8, en.dl, en.k, &a, true, 3) { Some(v) if v == tot => {}, _ => { en.bad += 1; } }
            }
        }
        return;
    }
    let f = f_of(j, en.k);
    let edge_forced_nonzero = (j == en.lo && j < en.k.min(0)) || (j == en.hi && j > en.k.max(0) - 1);
    let mut v = -en.n - 1;
    while v <= en.n + 1 {
        if (v - f).rem_euclid(2) == 0 && !(edge_forced_nonzero && v == 0) {
            let m = if v.abs().max(f.abs()) == 0 { 2 } else { v.abs().max(f.abs()) };
            let sc = site_cost(en, j, dprev, v);
            en.d[(j - en.lo) as usize] = v;
            en_rec(en, j + 1, part + m + sc);
        }
        v += 1;
    }
}
fn cmd_enum(n: i32, dpchk: bool) {
    let mut tal = vec![vec![0u64; (n + 1) as usize]; 3];
    let (mut bad, mut chk) = (0u64, 0u64);
    for k in -n..=n {
        for eps in [1i32, -1] { for dl in [0u8, 1] {
            let lmin = k.min(0); let hmax = k.max(0) - 1;
            for lo in (lmin - n)..=lmin { for hi in hmax..=(hmax + n) {
                if hi - lo + 1 > n { continue; }
                let mut en = En { n, k, eps, dl, lo, hi, d: vec![0; (hi - lo + 1).max(0) as usize], tal: vec![0; (n + 1) as usize], dpchk, bad: 0, chk: 0 };
                en_rec(&mut en, lo, 0);
                let sg = (k.signum() + 1) as usize;
                for i in 0..=(n as usize) { tal[sg][i] += en.tal[i]; }
                bad += en.bad; chk += en.chk;
            }}
        }}
    }
    println!("ENUM n={}  (closed-form l_R; DP cross-check on {} elements with l_R<=11: {} mismatches)", n, chk, bad);
    for (i, nm) in ["k<0", "k=0", "k>0"].iter().enumerate() { println!("  {} {:?}", nm, tal[i]); }
    let tot: Vec<u64> = (0..=(n as usize)).map(|i| tal[0][i] + tal[1][i] + tal[2][i]).collect();
    println!("  all {:?}", tot);
}

// ===================== room 58: cTrue (Lean CorrectedSpan) vs run rule vs c_pred vs BFS =====
fn cmd_ctrue(depth: usize) {
    let dist = bfs_parent(depth);
    let mut stats: BTreeMap<String, u64> = BTreeMap::new();
    let mut junc: BTreeMap<(i32, i32, u8, i32), u64> = BTreeMap::new();
    let mut biv: BTreeMap<(i32, i32, i32), u64> = BTreeMap::new();
    for (g, &(dd, _)) in dist.iter() {
        let amap: HashMap<i32, i32> = g.a.iter().copied().collect();
        let k = g.k; let e = g.eps as i32; let dl = g.dl;
        let dfn = |j: i32| -> i32 { *amap.get(&j).unwrap_or(&0) };
        let mut occ: Vec<i32> = g.a.iter().map(|&(p, _)| p).collect();
        if k > 0 { for j in 0..k { occ.push(j); } } else if k < 0 { for j in k..0 { occ.push(j); } }
        let (lo, hi) = if occ.is_empty() { (0, -1) } else { ((*occ.iter().min().unwrap()).min(0), (*occ.iter().max().unwrap()).max(-1)) };
        let cut = |s: i32| -> bool {
            let al = dfn(s - 1) - (if s == 0 { 1 } else { 0 }) + (if s == k && dl == 0 { e } else { 0 });
            let be = dfn(s) - (if s == k && dl == 1 { e } else { 0 });
            let ph = f_of(s - 1, k) + (if s == 0 { 1 } else { 0 }) - (if s == k && dl == 0 { 1 } else { 0 });
            al == 0 && be == 0 && ph == 0 };
        let mut ct = 0i32;
        for s in (lo + 1)..(hi + 1) { if cut(s) { ct += 1; } }
        let shield_fires = k == 0 && dl == 0 && g.a.iter().all(|&(p, _)| p >= 0) && g.a.iter().any(|&(p, _)| p >= 0);
        if shield_fires && cut(0) { ct += 1; }
        let lr = lr_closed(g.eps, g.dl, k, &g.a);
        let cp = c_pred(g.eps, g.dl, k, &g.a);
        let ok_lean = dd as i32 == lr + 2 * ct;
        *biv.entry((lr, ct, k.signum())).or_insert(0) += 1;
        *stats.entry(format!("lean_identity_ok={}", ok_lean)).or_insert(0) += 1;
        *stats.entry(format!("cTrue==c_pred {}", ct == cp)).or_insert(0) += 1;
        if k != 0 {
            // run rule: maximal runs of gap edges (d=0,f=0) in [lo,hi]
            let mut rr = 0i32; let mut j = lo;
            while j <= hi {
                if dfn(j) == 0 && f_of(j, k) == 0 {
                    let p = j; while j <= hi && dfn(j) == 0 && f_of(j, k) == 0 { j += 1; }
                    let l = j - p; rr += l - 1;
                    for &s in [p, p + l].iter() { if s == 0 || s == k {
                        let c = cut(s);
                        if c { rr += 1; }
                        *junc.entry((k.signum(), if s == 0 { 0 } else { 1 }, dl, c as i32)).or_insert(0) += 1;
                        // closed-form junction conditions (room 58 Lemma J)
                        let pred = if s == 0 { k < 0 && dfn(-1) == 1 && dfn(0) == 0 }
                                   else if k > 0 { dl == 0 && dfn(k - 1) == -e && dfn(k) == 0 }
                                   else { dl == 1 && dfn(k) == e && dfn(k - 1) == 0 };
                        *stats.entry(format!("lemmaJ_ok={}", pred == c)).or_insert(0) += 1;
                    } }
                } else { j += 1; }
            }
            // also check: no cut site outside gap-run sites
            *stats.entry(format!("runrule==cTrue {}", rr == ct)).or_insert(0) += 1;
        }
    }
    for (kk, v) in stats.iter() { println!("{} : {}", kk, v); }
    for ((a, c, sg), v) in biv.iter() { println!("BIV {} {} {} {}", a, c, sg, v); }
    println!("junction (sgn k, site[0=0,1=k*], delta, cut) : count");
    for (kk, v) in junc.iter() { println!("{:?} : {}", kk, v); }
}
