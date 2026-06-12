// fire — recompute A396406 from THEORY ALONE and fire it at the known terms.
//
//   Normal form (which elements exist) x Metric formula (their word lengths)
//   => the growth sequence, with NO group BFS anywhere in the pipeline.
//
// Modes:
//   cargo run --release -- verify 12     port-correctness gate: lamp-model BFS
//                                        vs the metric-formula solver; must
//                                        print zero mismatches.
//   cargo run --release -- fire 18       recompute u_0..u_18 from theory,
//                                        compare to the published terms.
//
// The element data is enumerated from the parity normal form (a_j odd exactly
// on the travel range); each element's length is the min-cost of the verified
// chain optimization (crossing numbers + Eulerian-connected site pairings,
// pass=1 / bounce=0 / sign flip free at passes, 2 at bounces).  The site
// transfer is exact: pairings are enumerated as count matrices between event
// classes; component merges via union-find; isolated cycles pruned.
//
// fire also reports the number of distinct reduced DP-state-vectors met —
// the experimental diagnostic for rationality of the growth series.

use std::collections::HashMap;
use std::time::Instant;

const PUB: [u64; 43] = [
    1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574, 11543,
    17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236, 1697179,
    2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781,
    // a(39)..a(42) from the depth-42 exact BFS (repo: rust_bfs_progress.json)
    43997388, 65932461, 98849591, 147969934,
];

// ---------------- component / profile state ----------------
// component: strand counts by type [up+, up-, dn+, dn-] over the CURRENT edge,
// plus has_start, has_end.
type Comp = ([u8; 4], bool, bool);
// profile: sorted components; the DONE profile is the empty list with flag.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct Profile {
    comps: Vec<Comp>,
    done: bool,
    sp: bool, // start placed
    ep: bool, // end placed
}

fn canon(mut comps: Vec<Comp>, done: bool, sp: bool, ep: bool) -> Profile {
    comps.sort();
    Profile { comps, done, sp, ep }
}

// ---------------- site transfer ----------------
// Event classes at a site:
//   arrivals:  for each old comp c: (side L, sign +) x c.up_p ; (L,-) x c.up_m
//              new dn-strands: (R,+) x pd ; (R,-) x dn-pd
//              virtual start (if site==0): (L,+)
//   departures: old comp: (L,+) x c.dn_p ; (L,-) x c.dn_m
//              new up-strands: (R,+) x pu ; (R,-) x u-pu
//              virtual end (if site==k): (side per delta*, sign eps*)
// pair cost: sides differ -> 1 ; same side same sign -> 0 ; same side flip -> 2.
//
// Owners: Old(i), NewUpP, NewUpM, NewDnP, NewDnM, Start, End.
// A count-matrix between arrival classes and departure classes determines the
// merge structure exactly:
//   - any entry >0 between two Old owners merges them (once);
//   - entries between Old and a New class attach that many new strands to it;
//   - entries between New classes create that many separate 2-strand comps;
//   - Start / End merge like Old owners with markers.
//
// Output: list of (cost, new Profile) candidates.

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Owner {
    Old(usize),
    NewUpP,
    NewUpM,
    NewDnP,
    NewDnM,
    Start,
    End,
}

#[derive(Clone, Copy)]
struct EvClass {
    side: u8, // 0 = L, 1 = R
    sign: i8,
    owner: Owner,
    count: u8,
}

fn pair_cost(a: &EvClass, d: &EvClass) -> u32 {
    if a.side != d.side {
        1
    } else if a.sign == d.sign {
        0
    } else {
        2
    }
}

struct Uf {
    p: Vec<usize>,
}
impl Uf {
    fn new(n: usize) -> Uf {
        Uf { p: (0..n).collect() }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.p[x] != x {
            self.p[x] = self.p[self.p[x]];
            x = self.p[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.p[ra] = rb;
        }
    }
}

// enumerate count matrices recursively; call sink on (cost, matrix)
fn enum_matrices(
    arrs: &[EvClass],
    deps: &[EvClass],
    sink: &mut dyn FnMut(u32, &Vec<Vec<u8>>),
) {
    let na = arrs.len();
    let nd = deps.len();
    let mut mat = vec![vec![0u8; nd]; na];
    let mut dep_rem: Vec<u8> = deps.iter().map(|d| d.count).collect();
    fn rec(
        i: usize,
        arrs: &[EvClass],
        deps: &[EvClass],
        mat: &mut Vec<Vec<u8>>,
        dep_rem: &mut Vec<u8>,
        cost: u32,
        sink: &mut dyn FnMut(u32, &Vec<Vec<u8>>),
    ) {
        if i == arrs.len() {
            if dep_rem.iter().all(|&r| r == 0) {
                sink(cost, mat);
            }
            return;
        }
        // distribute arrs[i].count among departure classes
        fn dist(
            i: usize,
            j: usize,
            left: u8,
            arrs: &[EvClass],
            deps: &[EvClass],
            mat: &mut Vec<Vec<u8>>,
            dep_rem: &mut Vec<u8>,
            cost: u32,
            sink: &mut dyn FnMut(u32, &Vec<Vec<u8>>),
        ) {
            if j == deps.len() {
                if left == 0 {
                    rec(i + 1, arrs, deps, mat, dep_rem, cost, sink);
                }
                return;
            }
            let maxc = left.min(dep_rem[j]);
            for c in 0..=maxc {
                mat[i][j] = c;
                dep_rem[j] -= c;
                let dc = (c as u32) * pair_cost(&arrs[i], &deps[j]);
                dist(i, j + 1, left - c, arrs, deps, mat, dep_rem, cost + dc, sink);
                dep_rem[j] += c;
                mat[i][j] = 0;
            }
        }
        dist(i, 0, arrs[i].count, arrs, deps, mat, dep_rem, cost, sink);
    }
    if na == 0 {
        if dep_rem.iter().all(|&r| r == 0) {
            sink(0, &mat);
        }
        return;
    }
    rec(0, arrs, deps, &mut mat, &mut dep_rem, 0, sink);
}

// process one site: given profile (components over left edge), new-edge strand
// counts (u, dn, pu, pd), virtual flags. Returns Vec<(cost, Profile)>.
#[allow(clippy::too_many_arguments)]
fn site_transfer(
    prof: &Profile,
    u: u8,
    dn: u8,
    pu: u8,
    pd: u8,
    inj_start: bool,
    inj_end: bool,
    end_side: u8,
    end_sign: i8,
) -> Vec<(u32, Profile)> {
    let mut out = Vec::new();
    if prof.done {
        // walk finished: nothing may happen at this site
        if u == 0 && dn == 0 && !inj_start && !inj_end {
            out.push((0, prof.clone()));
        }
        return out;
    }
    // build event classes
    let mut arrs: Vec<EvClass> = Vec::new();
    let mut deps: Vec<EvClass> = Vec::new();
    for (ci, c) in prof.comps.iter().enumerate() {
        if c.0[0] > 0 {
            arrs.push(EvClass { side: 0, sign: 1, owner: Owner::Old(ci), count: c.0[0] });
        }
        if c.0[1] > 0 {
            arrs.push(EvClass { side: 0, sign: -1, owner: Owner::Old(ci), count: c.0[1] });
        }
        if c.0[2] > 0 {
            deps.push(EvClass { side: 0, sign: 1, owner: Owner::Old(ci), count: c.0[2] });
        }
        if c.0[3] > 0 {
            deps.push(EvClass { side: 0, sign: -1, owner: Owner::Old(ci), count: c.0[3] });
        }
    }
    if pd > 0 {
        arrs.push(EvClass { side: 1, sign: 1, owner: Owner::NewDnP, count: pd });
    }
    if dn - pd > 0 {
        arrs.push(EvClass { side: 1, sign: -1, owner: Owner::NewDnM, count: dn - pd });
    }
    if pu > 0 {
        deps.push(EvClass { side: 1, sign: 1, owner: Owner::NewUpP, count: pu });
    }
    if u - pu > 0 {
        deps.push(EvClass { side: 1, sign: -1, owner: Owner::NewUpM, count: u - pu });
    }
    if inj_start {
        arrs.push(EvClass { side: 0, sign: 1, owner: Owner::Start, count: 1 });
    }
    if inj_end {
        deps.push(EvClass { side: end_side, sign: end_sign, owner: Owner::End, count: 1 });
    }
    let ta: u16 = arrs.iter().map(|e| e.count as u16).sum();
    let td: u16 = deps.iter().map(|e| e.count as u16).sum();
    if ta != td {
        return out;
    }
    if ta == 0 {
        // empty site: components must have no strands (they always do here:
        // comps hold left-edge strands; if any exist, events would exist)
        out.push((0, canon(prof.comps.clone(), false, prof.sp, prof.ep)));
        return out;
    }

    // owner indexing for union-find: old comps, 4 new classes, start, end
    let nold = prof.comps.len();
    let idx = |o: Owner| -> usize {
        match o {
            Owner::Old(i) => i,
            Owner::NewUpP => nold,
            Owner::NewUpM => nold + 1,
            Owner::NewDnP => nold + 2,
            Owner::NewDnM => nold + 3,
            Owner::Start => nold + 4,
            Owner::End => nold + 5,
        }
    };

    let arrs2 = arrs.clone();
    let deps2 = deps.clone();
    let prof2 = prof.clone();
    enum_matrices(&arrs, &deps, &mut |cost, mat| {
        // Determine merges. Subtlety: entries between two NEW classes make
        // separate fresh components (each pair its own comp), UNLESS the same
        // new strand could... each new strand is one event; a (new,new) entry
        // of count c yields c independent 2-strand components.
        // New strands matched to Old/Start/End join that component.
        // We must also count how many new strands of each type go where.
        let mut uf = Uf::new(nold + 6);
        // fresh-fresh pair components collected separately
        let mut fresh_pairs: Vec<([u8; 4], u8)> = Vec::new(); // (type-vector, count)
        // new strands attached to merged groups: counts per owner-root added later
        let mut attach: Vec<([u8; 4], usize)> = Vec::new(); // (typevec, owner idx)
        for (i, a) in arrs2.iter().enumerate() {
            for (j, d) in deps2.iter().enumerate() {
                let c = mat[i][j];
                if c == 0 {
                    continue;
                }
                let anew = !matches!(a.owner, Owner::Old(_) | Owner::Start | Owner::End);
                let dnew = !matches!(d.owner, Owner::Old(_) | Owner::Start | Owner::End);
                let tv = |o: Owner| -> [u8; 4] {
                    match o {
                        Owner::NewUpP => [1, 0, 0, 0],
                        Owner::NewUpM => [0, 1, 0, 0],
                        Owner::NewDnP => [0, 0, 1, 0],
                        Owner::NewDnM => [0, 0, 0, 1],
                        _ => [0, 0, 0, 0],
                    }
                };
                if anew && dnew {
                    let mut t = tv(a.owner);
                    let t2 = tv(d.owner);
                    for z in 0..4 {
                        t[z] += t2[z];
                    }
                    fresh_pairs.push((t, c));
                } else if anew {
                    for _ in 0..c {
                        attach.push((tv(a.owner), idx(d.owner)));
                    }
                } else if dnew {
                    for _ in 0..c {
                        attach.push((tv(d.owner), idx(a.owner)));
                    }
                } else {
                    uf.union(idx(a.owner), idx(d.owner));
                }
            }
        }
        // build groups over roots of {old comps, start, end}
        let mut groups: HashMap<usize, ([u8; 4], bool, bool)> = HashMap::new();
        for ci in 0..nold {
            let r = uf.find(ci);
            let g = groups.entry(r).or_insert(([0; 4], false, false));
            if prof2.comps[ci].1 {
                g.1 = true;
            }
            if prof2.comps[ci].2 {
                g.2 = true;
            }
        }
        if inj_start {
            let r = uf.find(nold + 4);
            let g = groups.entry(r).or_insert(([0; 4], false, false));
            g.1 = true;
        }
        if inj_end {
            let r = uf.find(nold + 5);
            let g = groups.entry(r).or_insert(([0; 4], false, false));
            g.2 = true;
        }
        for (t, o) in &attach {
            let r = uf.find(*o);
            let g = groups.entry(r).or_insert(([0; 4], false, false));
            for z in 0..4 {
                g.0[z] += t[z];
            }
        }
        // assemble: validity & new comps
        let mut comps: Vec<Comp> = Vec::new();
        let mut finished = false;
        let mut ok = true;
        for (_, g) in groups.iter() {
            let ns: u16 = g.0.iter().map(|&x| x as u16).sum();
            if ns == 0 {
                if g.1 && g.2 {
                    if finished {
                        ok = false;
                        break;
                    }
                    finished = true;
                } else {
                    ok = false; // isolated cycle or dangling marker
                    break;
                }
            } else {
                comps.push((g.0, g.1, g.2));
            }
        }
        if ok {
            for (t, c) in &fresh_pairs {
                for _ in 0..*c {
                    comps.push((*t, false, false));
                }
            }
            if finished && !comps.is_empty() {
                ok = false;
            }
            if ok {
                let nsp = prof2.sp || inj_start;
                let nep = prof2.ep || inj_end;
                if finished {
                    out.push((cost, Profile { comps: vec![], done: true, sp: nsp, ep: nep }));
                } else {
                    out.push((cost, canon(comps, false, nsp, nep)));
                }
            }
        }
    });
    out
}

// ---------------- per-element solver (verify mode) ----------------
fn f_of(j: i32, k: i32) -> i32 {
    if 0 <= j && j < k {
        1
    } else if k <= j && j < 0 {
        -1
    } else {
        0
    }
}

fn solve(eps_t: i8, dl_t: u8, k: i32, a: &HashMap<i32, i32>) -> Option<u32> {
    let nz: Vec<i32> = a.iter().filter(|(_, &v)| v != 0).map(|(&j, _)| j).collect();
    let mut hull = nz.clone();
    if k > 0 {
        for j in 0..k {
            hull.push(j);
        }
    }
    if k < 0 {
        for j in k..0 {
            hull.push(j);
        }
    }
    let end_side: u8 = if dl_t == 1 { 1 } else { 0 };
    let end_sign: i8 = if eps_t == 1 { 1 } else { -1 };
    if hull.is_empty() {
        // virtual arrival pairs virtual departure at site 0
        let c = if end_side == 0 {
            if end_sign == 1 {
                0
            } else {
                2
            }
        } else {
            1
        };
        return Some(c);
    }
    let aa = *hull.iter().min().unwrap().min(&0) - 1;
    let bb = *hull.iter().max().unwrap().max(&-1) + 1;
    // DP over edges aa..bb ; states: Profile -> cost
    let mut states: HashMap<Profile, u32> = HashMap::new();
    states.insert(Profile { comps: vec![], done: false, sp: false, ep: false }, 0);
    for j in aa..=bb {
        let fj = f_of(j, k);
        let aj = *a.get(&j).unwrap_or(&0);
        let mut base = aj.abs().max(fj.abs());
        if (base - aj.abs()) % 2 != 0 {
            base += 1;
        }
        let mut nstates: HashMap<Profile, u32> = HashMap::new();
        for (prof, &c0) in &states {
            let prev_m: u16 = prof
                .comps
                .iter()
                .map(|c| c.0.iter().map(|&x| x as u16).sum::<u16>())
                .sum();
            for lam in 0..3 {
                let m = base + 2 * lam;
                if m == 0 && (aj != 0 || fj != 0) {
                    continue;
                }
                if m > 40 {
                    break;
                }
                if j <= -1 && prev_m > 0 && m == 0 {
                    continue;
                }
                if j >= 1 && prev_m == 0 && m > 0 && !prof.done {
                    continue;
                }
                let u = (m + fj) / 2;
                let dn = (m - fj) / 2;
                if u < 0 || dn < 0 {
                    continue;
                }
                for pu in 0..=u {
                    let t = aj + dn - u + 2 * pu;
                    if t % 2 != 0 {
                        continue;
                    }
                    let pdv = t / 2;
                    if pdv < 0 || pdv > dn {
                        continue;
                    }
                    let res = site_transfer(
                        prof,
                        u as u8,
                        dn as u8,
                        pu as u8,
                        pdv as u8,
                        j == 0,
                        j == k,
                        end_side,
                        end_sign,
                    );
                    for (sc, np) in res {
                        let val = c0 + m as u32 + sc;
                        let e = nstates.entry(np).or_insert(u32::MAX);
                        if val < *e {
                            *e = val;
                        }
                    }
                }
            }
        }
        states = nstates;
        if states.is_empty() {
            return None;
        }
    }
    // final site bb+1
    let j = bb + 1;
    let mut best = u32::MAX;
    for (prof, &c0) in &states {
        if prof.done {
            if prof.sp && prof.ep {
                best = best.min(c0);
            }
            continue;
        }
        let res = site_transfer(prof, 0, 0, 0, 0, j == 0, j == k, end_side, end_sign);
        for (sc, np) in res {
            if np.done && np.sp && np.ep {
                best = best.min(c0 + sc);
            }
        }
    }
    if best == u32::MAX {
        None
    } else {
        Some(best)
    }
}

// ---------------- lamp-model BFS (referee for verify mode) ----------------
type LampState = (i8, u8, i32, Vec<(i32, i32)>);
fn lamp_bfs(maxd: u32) -> HashMap<LampState, u32> {
    let mut dist: HashMap<LampState, u32> = HashMap::new();
    let ident: LampState = (1, 0, 0, vec![]);
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    for d in 0..maxd {
        let mut nxt = Vec::new();
        for (e, dl, k, l) in &frontier {
            let mut cands: Vec<LampState> = vec![(*e, 1 - dl, *k, l.clone()), (-e, 1 - dl, *k, l.clone())];
            let mut m: HashMap<i32, i32> = l.iter().cloned().collect();
            if *dl == 0 {
                *m.entry(k - 1).or_insert(0) += *e as i32;
                if m[&(k - 1)] == 0 {
                    m.remove(&(k - 1));
                }
                let mut v: Vec<(i32, i32)> = m.into_iter().collect();
                v.sort();
                cands.push((*e, 1, k - 1, v));
            } else {
                *m.entry(*k).or_insert(0) -= *e as i32;
                if m[k] == 0 {
                    m.remove(k);
                }
                let mut v: Vec<(i32, i32)> = m.into_iter().collect();
                v.sort();
                cands.push((*e, 0, k + 1, v));
            }
            for ne in cands {
                if !dist.contains_key(&ne) {
                    dist.insert(ne.clone(), d + 1);
                    nxt.push(ne);
                }
            }
        }
        frontier = nxt;
    }
    dist
}

// ---------------- fire mode: theory-only enumeration ----------------
// Enumerate data (k, a-vector) via a left-to-right scan with the SAME
// site_transfer; histogram min-cost per element over all (eps*, delta*).
// Recursion carries the DP state-vector; memoization on the reduced vector.

fn fire(maxd: u32) {
    let t0 = Instant::now();
    let mut hist = vec![0u64; (maxd + 1) as usize];
    // elements grouped by k; for each k scan edges of the active window.
    // Window: edges from k.min(0)-pad .. k.max(0)-1+pad where pad bounded by budget.
    // For every element the scan is: [left excursion zone][travel][right zone].
    // We enumerate a_j edge by edge, carrying DP states; at the end close.
    // (Direct recursive enumeration with state-sharing; memo on suffix is
    // keyed by (j-phase data, budget, reduced state-vector) — here we keep the
    // simpler prefix-sharing recursion, which is already exponentially better
    // than per-element solve; memo diagnostics reported.)
    for k in -(maxd as i32) / 1..=(maxd as i32) {
        // crude budget: |k| travel edges each >= 1 move
        if k.abs() as u32 > maxd {
            continue;
        }
        for dl_t in 0..2u8 {
            for &eps_t in &[1i8, -1] {
                let end_side: u8 = if dl_t == 1 { 1 } else { 0 };
                let end_sign: i8 = eps_t;
                // window bounds
                let pad = ((maxd as i32) - k.abs()) / 2 + 1;
                let aa = k.min(0) - pad - 1;
                let bb = k.max(0) - 1 + pad + 1;
                // recursive scan
                struct Ctx {
                    k: i32,
                    end_side: u8,
                    end_sign: i8,
                    maxd: u32,
                    bb: i32,
                }
                let ctx = Ctx { k, end_side, end_sign, maxd, bb };
                fn rec(
                    ctx: &Ctx,
                    j: i32,
                    states: &HashMap<Profile, u32>,
                    hist: &mut Vec<u64>,
                ) {
                    if states.is_empty() {
                        return;
                    }
                    let minc = states.values().min().cloned().unwrap_or(u32::MAX);
                    if minc > ctx.maxd {
                        return;
                    }
                    if j == ctx.bb + 1 {
                        // close: final site
                        let mut best = u32::MAX;
                        for (prof, &c0) in states {
                            if prof.done {
                                if prof.sp && prof.ep {
                                    best = best.min(c0);
                                }
                                continue;
                            }
                            let res = site_transfer(
                                prof,
                                0,
                                0,
                                0,
                                0,
                                j == 0,
                                j == ctx.k,
                                ctx.end_side,
                                ctx.end_sign,
                            );
                            for (sc, np) in res {
                                if np.done && np.sp && np.ep {
                                    best = best.min(c0 + sc);
                                }
                            }
                        }
                        if best <= ctx.maxd {
                            hist[best as usize] += 1;
                        }
                        return;
                    }
                    let fj = f_of(j, ctx.k);
                    // enumerate a_j: parity = |f_j| mod 2 ; magnitude bounded by budget
                    let parity = (fj.abs() % 2) as i32;
                    let mut vals: Vec<i32> = Vec::new();
                    let rem = (ctx.maxd - minc) as i32;
                    if parity == 1 {
                        let mut v = 1;
                        while v <= rem {
                            vals.push(v);
                            vals.push(-v);
                            v += 2;
                        }
                    } else {
                        vals.push(0);
                        let mut v = 2;
                        while v <= rem {
                            vals.push(v);
                            vals.push(-v);
                            v += 2;
                        }
                    }
                    for aj in vals {
                        // transfer with this a_j
                        let mut nstates: HashMap<Profile, u32> = HashMap::new();
                        let mut base = aj.abs().max(fj.abs());
                        if (base - aj.abs()) % 2 != 0 {
                            base += 1;
                        }
                        for (prof, &c0) in states {
                            if prof.done {
                                if aj == 0 && fj == 0 && j != 0 && j != ctx.k {
                                    let e = nstates.entry(prof.clone()).or_insert(u32::MAX);
                                    if c0 < *e {
                                        *e = c0;
                                    }
                                }
                                continue;
                            }
                            let prev_m: u16 = prof
                                .comps
                                .iter()
                                .map(|c| c.0.iter().map(|&x| x as u16).sum::<u16>())
                                .sum();
                            for lam in 0..3 {
                                let m = base + 2 * lam;
                                if m == 0 && (aj != 0 || fj != 0) {
                                    continue;
                                }
                                if c0 + m as u32 > ctx.maxd {
                                    break;
                                }
                                if j <= -1 && prev_m > 0 && m == 0 {
                                    continue;
                                }
                                if j >= 1 && prev_m == 0 && m > 0 {
                                    continue;
                                }
                                let u = (m + fj) / 2;
                                let dn = (m - fj) / 2;
                                if u < 0 || dn < 0 {
                                    continue;
                                }
                                for pu in 0..=u {
                                    let t = aj + dn - u + 2 * pu;
                                    if t % 2 != 0 {
                                        continue;
                                    }
                                    let pdv = t / 2;
                                    if pdv < 0 || pdv > dn {
                                        continue;
                                    }
                                    let res = site_transfer(
                                        prof,
                                        u as u8,
                                        dn as u8,
                                        pu as u8,
                                        pdv as u8,
                                        j == 0,
                                        j == ctx.k,
                                        ctx.end_side,
                                        ctx.end_sign,
                                    );
                                    for (sc, np) in res {
                                        let val = c0 + m as u32 + sc;
                                        if val <= ctx.maxd {
                                            let e = nstates.entry(np).or_insert(u32::MAX);
                                            if val < *e {
                                                *e = val;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        rec(ctx, j + 1, &nstates, hist);
                    }
                }
                let mut init: HashMap<Profile, u32> = HashMap::new();
                init.insert(Profile { comps: vec![], done: false, sp: false, ep: false }, 0);
                rec(&ctx, aa, &init, &mut hist);
            }
        }
        eprintln!(
            "[{:6.1}s] k={} done, partial hist {:?}",
            t0.elapsed().as_secs_f64(),
            k,
            &hist[..(maxd.min(12) + 1) as usize]
        );
    }
    println!("\ncomputed (theory only): {:?}", hist);
    println!("published             : {:?}", &PUB[..(maxd + 1) as usize]);
    let ok = hist
        .iter()
        .zip(PUB.iter())
        .all(|(a, b)| a == b);
    println!("{}", if ok { "MATCH — the theory generates A396406" } else { "MISMATCH" });
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("verify");
    let d: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(12);
    match mode {
        "verify" => {
            let t0 = Instant::now();
            let dist = lamp_bfs(d);
            println!("[{:.1}s] lamp BFS: {} elements", t0.elapsed().as_secs_f64(), dist.len());
            let mut mism = 0u64;
            let mut tested = 0u64;
            for ((e, dl, k, l), dd) in &dist {
                let a: HashMap<i32, i32> = l.iter().cloned().collect();
                let fl = solve(*e, *dl, *k, &a);
                tested += 1;
                if fl != Some(*dd) {
                    mism += 1;
                    if mism <= 5 {
                        println!("MISMATCH {:?} true {} got {:?}", (e, dl, k, l), dd, fl);
                    }
                }
            }
            println!(
                "[{:.1}s] verify depth {}: tested {} mismatches {}",
                t0.elapsed().as_secs_f64(),
                d,
                tested,
                mism
            );
        }
        "fire" => fire(d),
        "kernel" => {
            // kernel c e : compute L_T = min length of a nontrivial kernel
            // element for the shape with mu_T = c t^2 - e t + c, minimizing
            // over a catalog of multipliers f and placements j0; then
            // n_T = ceil(L_T / 2).
            let c: i32 = args.get(2).and_then(|s| s.parse().ok()).expect("c");
            let e: i32 = args.get(3).and_then(|s| s.parse().ok()).expect("e");
            // catalog of f as coefficient vectors (low degree first)
            let catalog_full = args.get(4).map(|s| s == "full").unwrap_or(false);
            let mut cat: Vec<(&str, Vec<i32>)> = vec![("1", vec![1])];
            if catalog_full {
                cat.extend(vec![
                    ("1+t", vec![1, 1]),
                    ("1-t", vec![1, -1]),
                    ("1+t+t2", vec![1, 1, 1]),
                    ("1-t+t2", vec![1, -1, 1]),
                    ("1+t2", vec![1, 0, 1]),
                    ("1-t2", vec![1, 0, -1]),
                ]);
            }
            let mut best = u32::MAX;
            let mut bestdesc = String::new();
            for (name, f) in &cat {
                // mu * f  with mu = (c, -e, c)
                let mu = [c, -e, c];
                let mut prod = vec![0i32; f.len() + 2];
                for (i, &fc) in f.iter().enumerate() {
                    for (j, &mc) in mu.iter().enumerate() {
                        prod[i + j] += fc * mc;
                    }
                }
                // edge deposits a_j = 2 * coeff_j of (mu f), placed at j0..
                for j0 in -2i32..=0 {
                    let mut a: HashMap<i32, i32> = HashMap::new();
                    for (i, &p) in prod.iter().enumerate() {
                        if p != 0 {
                            a.insert(j0 + i as i32, 2 * p);
                        }
                    }
                    if a.is_empty() { continue; }
                    if let Some(l) = solve(1, 0, 0, &a) {
                        if l < best {
                            best = l;
                            bestdesc = format!("f={} j0={} deposits={:?}", name, j0, {
                                let mut v: Vec<(i32,i32)> = a.iter().map(|(&k,&v)|(k,v)).collect();
                                v.sort(); v
                            });
                        }
                    }
                }
                eprintln!("  f={} done, best so far {}", name, best);
            }
            println!("shape (c={}, e={}): L_T = {}  =>  n_T = {}", c, e, best, (best + 1) / 2);
            println!("  attained by {}", bestdesc);
        }
        "deep" => {
            let c: u32 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(d);
            eprintln!("deep: budget {}, lag cap {}", d, c);
            deep(d, c)
        }
        _ => eprintln!("usage: fire [verify|fire] D"),
    }
}

// ==================== deep mode: the counting grammar ====================
// The data scan is rebuilt as a phase automaton with NO absolute positions:
//   I  -> (L)* -> [Mp* | Mm*] -> (Rz)* -> CLOSE      (k = #M-steps; k=0 skips M)
// L-zone: edges left of min(0,k): even deposits, first edge nonzero, m>=2.
// Mp/Mm: travel edges (k>0 / k<0): odd deposits, f=+1/-1; start/end virtuals
//   are injected at the phase-entry sites.  Rz: even deposits right of
//   max(0,k), m>=2, closure allowed only right after a nonzero edge.
// State = (phase, reduced min-plus profile vector).  The memo of states IS
// the determinized counting automaton; path counts by cost give u_d.

use std::collections::VecDeque;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Phase {
    I,
    L,
    Mp,
    Mm,
    Rz { lastnz: bool },
}

type Vred = Vec<(Profile, u32)>; // sorted, min cost = 0

fn reduce(v: HashMap<Profile, u32>, cap: u32) -> Option<(u32, Vred)> {
    if v.is_empty() {
        return None;
    }
    let mn = *v.values().min().unwrap();
    let mut out: Vec<(Profile, u32)> = v
        .into_iter()
        .filter(|(_, c)| c - mn <= cap)
        .map(|(p, c)| (p, c - mn))
        .collect();
    out.sort();
    Some((mn, out))
}

// apply one edge (a_j, fj, injections) to a reduced vector; min-plus over configs
fn edge_transfer(
    v: &Vred,
    aj: i32,
    fj: i32,
    inj_start: bool,
    inj_end: bool,
    end_side: u8,
    end_sign: i8,
    min_m: i32,
    cap: u32,
) -> Option<(u32, Vred)> {
    let mut base = aj.abs().max(fj.abs()).max(min_m);
    if (base - aj.abs()) % 2 != 0 {
        base += 1;
    }
    let mut nv: HashMap<Profile, u32> = HashMap::new();
    for (prof, c0) in v {
        if prof.done {
            continue; // closed walks accept no further edges
        }
        for lam in 0..3 {
            let m = base + 2 * lam;
            if m == 0 && (aj != 0 || fj != 0) {
                continue;
            }
            let u = (m + fj) / 2;
            let dn = (m - fj) / 2;
            if u < 0 || dn < 0 {
                continue;
            }
            for pu in 0..=u {
                let t = aj + dn - u + 2 * pu;
                if t % 2 != 0 {
                    continue;
                }
                let pdv = t / 2;
                if pdv < 0 || pdv > dn {
                    continue;
                }
                let res = site_transfer(
                    prof, u as u8, dn as u8, pu as u8, pdv as u8, inj_start, inj_end, end_side,
                    end_sign,
                );
                for (sc, np) in res {
                    let val = c0 + m as u32 + sc;
                    if val <= cap + 60 {
                        let e = nv.entry(np).or_insert(u32::MAX);
                        if val < *e {
                            *e = val;
                        }
                    }
                }
            }
        }
    }
    reduce(nv, cap)
}

// closure: final site with pending injections; returns min closing cost
fn closure_cost(
    v: &Vred,
    inj_start: bool,
    inj_end: bool,
    end_side: u8,
    end_sign: i8,
) -> Option<u32> {
    let mut best = u32::MAX;
    for (prof, c0) in v {
        if prof.done {
            if prof.sp && prof.ep {
                best = best.min(*c0);
            }
            continue;
        }
        let res = site_transfer(prof, 0, 0, 0, 0, inj_start, inj_end, end_side, end_sign);
        for (sc, np) in res {
            if np.done && np.sp && np.ep {
                best = best.min(c0 + sc);
            }
        }
    }
    if best == u32::MAX {
        None
    } else {
        Some(best)
    }
}

fn deep(maxd: u32, lagcap: u32) {
    let t0 = Instant::now();
    let mut hist = vec![0u64; (maxd + 1) as usize];
    let mut total_states = 0usize;
    for &(eps_t, dl_t) in &[(1i8, 0u8), (1, 1), (-1, 0), (-1, 1)] {
        let end_side: u8 = if dl_t == 1 { 1 } else { 0 };
        let end_sign: i8 = eps_t;
        // automaton states
        let mut ids: HashMap<(Phase, Vred), usize> = HashMap::new();
        let mut trans: Vec<Vec<(u32, usize)>> = Vec::new(); // state -> (cost, target)
        let mut accept: Vec<Option<u32>> = Vec::new(); // closure cost
        let empty: Vred = vec![(
            Profile { comps: vec![], done: false, sp: false, ep: false },
            0,
        )];
        let mut get_id = |ph: Phase, v: Vred, trans: &mut Vec<Vec<(u32, usize)>>, accept: &mut Vec<Option<u32>>, ids: &mut HashMap<(Phase, Vred), usize>, queue: &mut VecDeque<usize>, keys: &mut Vec<(Phase, Vred)>| -> usize {
            let key = (ph, v);
            if let Some(&i) = ids.get(&key) {
                return i;
            }
            let i = ids.len();
            ids.insert(key.clone(), i);
            keys.push(key);
            trans.push(Vec::new());
            accept.push(None);
            queue.push_back(i);
            i
        };
        let mut queue: VecDeque<usize> = VecDeque::new();
        let mut keys: Vec<(Phase, Vred)> = Vec::new();
        let init = get_id(Phase::I, empty.clone(), &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
        while let Some(sid) = queue.pop_front() {
            let (ph, v) = keys[sid].clone();
            // closure
            let acc = match ph {
                Phase::I => closure_cost(&v, true, true, end_side, end_sign),
                Phase::L => closure_cost(&v, true, true, end_side, end_sign),
                Phase::Mp => closure_cost(&v, false, true, end_side, end_sign),
                Phase::Mm => closure_cost(&v, true, false, end_side, end_sign),
                Phase::Rz { lastnz } => {
                    if lastnz {
                        closure_cost(&v, false, false, end_side, end_sign)
                    } else {
                        None
                    }
                }
            };
            accept[sid] = acc;
            // transitions: enumerate successor edges by phase
            let mut push = |ph2: Phase,
                            aj: i32,
                            fj: i32,
                            is_: bool,
                            ie: bool,
                            minm: i32,
                            trans: &mut Vec<Vec<(u32, usize)>>,
                            accept: &mut Vec<Option<u32>>,
                            ids: &mut HashMap<(Phase, Vred), usize>,
                            queue: &mut VecDeque<usize>,
                            keys: &mut Vec<(Phase, Vred)>| {
                if let Some((dc, nv)) =
                    edge_transfer(&v, aj, fj, is_, ie, end_side, end_sign, minm, lagcap)
                {
                    if dc <= maxd {
                        let tid = get_id(ph2, nv, trans, accept, ids, queue, keys);
                        trans[sid].push((dc, tid));
                    }
                }
            };
            let evens: Vec<i32> = {
                let mut z = vec![0];
                let mut x = 2;
                while x <= maxd as i32 {
                    z.push(x);
                    z.push(-x);
                    x += 2;
                }
                z
            };
            let odds: Vec<i32> = {
                let mut z = vec![];
                let mut x = 1;
                while x <= maxd as i32 {
                    z.push(x);
                    z.push(-x);
                    x += 2;
                }
                z
            };
            match ph {
                Phase::I => {
                    for &a in &evens {
                        if a != 0 {
                            // first L edge (nonzero)
                            push(Phase::L, a, 0, false, false, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                        }
                    }
                    for &a in &odds {
                        push(Phase::Mp, a, 1, true, false, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                        push(Phase::Mm, a, -1, false, true, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                    for &a in &evens {
                        // k=0, first R edge (may be zero gap)
                        push(Phase::Rz { lastnz: a != 0 }, a, 0, true, true, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                }
                Phase::L => {
                    for &a in &evens {
                        push(Phase::L, a, 0, false, false, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                    for &a in &odds {
                        push(Phase::Mp, a, 1, true, false, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                        push(Phase::Mm, a, -1, false, true, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                    for &a in &evens {
                        push(Phase::Rz { lastnz: a != 0 }, a, 0, true, true, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                }
                Phase::Mp => {
                    for &a in &odds {
                        push(Phase::Mp, a, 1, false, false, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                    for &a in &evens {
                        push(Phase::Rz { lastnz: a != 0 }, a, 0, false, true, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                }
                Phase::Mm => {
                    for &a in &odds {
                        push(Phase::Mm, a, -1, false, false, 1, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                    for &a in &evens {
                        push(Phase::Rz { lastnz: a != 0 }, a, 0, true, false, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                }
                Phase::Rz { .. } => {
                    for &a in &evens {
                        push(Phase::Rz { lastnz: a != 0 }, a, 0, false, false, 2, &mut trans, &mut accept, &mut ids, &mut queue, &mut keys);
                    }
                }
            }
            if ids.len() % 2000 == 0 {
                eprintln!(
                    "[{:7.1}s] variant ({},{}): {} states discovered, queue {}",
                    t0.elapsed().as_secs_f64(),
                    eps_t,
                    dl_t,
                    ids.len(),
                    queue.len()
                );
            }
            if ids.len() > 3_000_000 {
                eprintln!("STATE EXPLOSION (>3M) — automaton not finite at this budget; aborting variant");
                break;
            }
        }
        let n = ids.len();
        total_states += n;
        // shape census: saturate strand counts at 2 (quotient out the counter)
        let mut shapes: std::collections::HashSet<String> = std::collections::HashSet::new();
        for ((ph, v), _) in ids.iter() {
            let mut sig = format!("{:?}|", ph);
            let mut comps_sig: Vec<String> = v
                .iter()
                .map(|(p, off)| {
                    let cc: Vec<String> = p
                        .comps
                        .iter()
                        .map(|c| {
                            format!(
                                "[{},{},{},{},{},{}]",
                                c.0[0].min(2), c.0[1].min(2), c.0[2].min(2), c.0[3].min(2),
                                c.1, c.2
                            )
                        })
                        .collect();
                    format!("({};{};{};{})", cc.join(""), p.done, p.sp as u8 + 2 * p.ep as u8, off)
                })
                .collect();
            comps_sig.sort();
            sig.push_str(&comps_sig.join("+"));
            shapes.insert(sig);
        }
        eprintln!(
            "[{:7.1}s] variant ({},{}): automaton complete: {} states, {} SHAPES (counter saturated at 2)",
            t0.elapsed().as_secs_f64(),
            eps_t,
            dl_t,
            n,
            shapes.len()
        );
        if std::env::args().any(|a| a == "census1") {
            // census mode: only the first variant
            println!("CENSUS: budget {}, states {}, shapes {}", maxd, n, shapes.len());
            return;
        }
        // path-count DP by cost
        let mut c = vec![vec![0u64; n]; (maxd + 1) as usize];
        c[0][init] = 1;
        for d in 0..=maxd {
            for s in 0..n {
                let cnt = c[d as usize][s];
                if cnt == 0 {
                    continue;
                }
                if let Some(acc) = accept[s] {
                    let fd = d + acc;
                    if fd <= maxd {
                        hist[fd as usize] += cnt;
                    }
                }
                for &(dc, t) in &trans[s] {
                    let nd = d + dc;
                    if nd <= maxd {
                        c[nd as usize][t] += cnt;
                    }
                }
            }
        }
    }
    println!("\nautomaton states (4 variants total): {}", total_states);
    println!("computed (theory only): {:?}", hist);
    let lim = (maxd + 1).min(PUB.len() as u32) as usize;
    println!("published             : {:?}", &PUB[..lim]);
    let ok = hist[..lim].iter().zip(PUB[..lim].iter()).all(|(a, b)| a == b);
    println!(
        "{}",
        if ok {
            "MATCH — the theory generates A396406"
        } else {
            "MISMATCH"
        }
    );
    if (maxd as usize) >= PUB.len() {
        println!("NEW TERMS beyond all prior computation:");
        for d in PUB.len()..=(maxd as usize) {
            println!("  u_{} = {}", d, hist[d]);
        }
    }
    // recurrence hunt on computed terms (exact, i128)
    if ok {
        let terms: Vec<i128> = hist.iter().map(|&x| x as i128).collect();
        for ord in 1..=((terms.len() as i32 - 8) / 2).max(0) as usize {
            if let Some(coef) = find_recurrence(&terms, ord) {
                println!("LINEAR RECURRENCE FOUND, order {}: {:?}", ord, coef);
                println!("characteristic polynomial: x^{} - sum coef_i x^(order-i); beta_2 = largest real root", ord);
                return;
            }
        }
        println!("no linear recurrence of order <= {} over Q fits the computed terms", ((terms.len() as i32 - 8) / 2).max(0));
    }
}

// exact rational recurrence finder via fraction-free Gaussian elimination
fn find_recurrence(t: &[i128], ord: usize) -> Option<Vec<f64>> {
    let need = 2 * ord + 4;
    if t.len() < need {
        return None;
    }
    // solve sum_{i=1..ord} c_i * t[n-i] = t[n] for n = ord..ord+ord-1, verify on rest
    let rows = ord;
    let mut a = vec![vec![0f64; ord + 1]; rows];
    for r in 0..rows {
        let n = ord + r;
        for i in 0..ord {
            a[r][i] = t[n - 1 - i] as f64;
        }
        a[r][ord] = t[n] as f64;
    }
    // gaussian
    for col in 0..ord {
        let mut piv = col;
        for r in col..rows {
            if a[r][col].abs() > a[piv][col].abs() {
                piv = r;
            }
        }
        if a[piv][col].abs() < 1e-9 {
            return None;
        }
        a.swap(col, piv);
        let p = a[col][col];
        for r in 0..rows {
            if r != col {
                let f = a[r][col] / p;
                for cc in col..=ord {
                    a[r][cc] -= f * a[col][cc];
                }
            }
        }
    }
    let coef: Vec<f64> = (0..ord).map(|i| a[i][ord] / a[i][i]).collect();
    // exact verification over ALL terms with rounded rational coefficients?
    // verify in f64 with tight tolerance over the full range
    for n in ord..t.len() {
        let mut s = 0f64;
        for i in 0..ord {
            s += coef[i] * t[n - 1 - i] as f64;
        }
        if (s - t[n] as f64).abs() > 0.5 {
            return None;
        }
    }
    Some(coef)
}
