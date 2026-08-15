// Direct enumeration of realizations, for the shield law (M2).
//
// A realization of a bulk configuration (all f_j = 0, marker at site 0, k = 0)
// is: crossing counts m_j, a sign split (p^u_j, p^d_j) per edge, and a bijection
// between arrivals and departures at every site.  Its cost is
// sum_j m_j + sum_s (pairing cost at s); its components are the classes of the
// walk-connectivity relation on the crossings, one of which carries the two
// virtual marker events and is the open walk.
//
// The relaxed length is the minimum cost; the connectivity defect c is the
// minimum number of isolated cycles (components other than the marker's) over
// the realizations attaining that minimum.
//
// Exact integer arithmetic, exhaustive over every sign split and every site
// bijection.

use std::collections::{HashMap, HashSet};

use crate::cost_of;

#[derive(Clone)]
pub struct Edge {
    pub a: i64,
    pub m: i64,
    pub u: usize,
    pub dn: usize,
    pub pu: usize, // up-crossings carrying sign +
    pub pd: usize, // down-crossings carrying sign +
}

impl Edge {
    fn is_up(&self, i: usize) -> bool {
        i < self.u
    }
    fn sign_plus(&self, i: usize) -> bool {
        if self.is_up(i) {
            i < self.pu
        } else {
            i - self.u < self.pd
        }
    }
}

struct Uf {
    p: Vec<usize>,
}
impl Uf {
    fn new(n: usize) -> Self {
        Uf { p: (0..n).collect() }
    }
    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.p[r] != r {
            r = self.p[r];
        }
        let mut c = x;
        while self.p[c] != c {
            let nx = self.p[c];
            self.p[c] = r;
            c = nx;
        }
        r
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.p[ra] = rb;
        }
    }
}

/// State carried across a site: the partition of the open items (the crossings
/// of the edge just processed), which class carries the marker, and whether the
/// marker has appeared / has already closed.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct State {
    part: Vec<u8>,
    nclass: u8,
    mcls: u8, // class carrying the marker, 255 = none open
    mseen: bool,
    mclosed: bool,
}

fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut out = vec![];
    let mut cur: Vec<usize> = (0..n).collect();
    fn rec(k: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if k == cur.len() {
            out.push(cur.clone());
            return;
        }
        for i in k..cur.len() {
            cur.swap(k, i);
            rec(k + 1, cur, out);
            cur.swap(k, i);
        }
    }
    rec(0, &mut cur, &mut out);
    out
}

thread_local! {
    static PERMS: Vec<Vec<Vec<usize>>> = (0..=8).map(permutations).collect();
}

/// Exhaustive enumeration for one configuration and one sign split.
/// Returns a map (total site cost) -> (minimal number of isolated cycles).
/// The edge crossings sum_j m_j is NOT included in the cost.
pub fn enumerate(
    edges: &[Edge],
    virt_arr_site: Option<usize>,
    virt_dep_site: Option<(usize, usize)>,
) -> HashMap<i64, i64> {
    let n = edges.len();
    let mut dp: HashMap<(State, i64), i64> = HashMap::new();
    dp.insert(
        (State { part: vec![], nclass: 0, mcls: 255, mseen: false, mclosed: false }, 0),
        0,
    );

    PERMS.with(|perms| {
        for s in 0..=n {
            let mut ndp: HashMap<(State, i64), i64> = HashMap::new();
            let (lu, ldn) = if s == 0 { (0, 0) } else { (edges[s - 1].u, edges[s - 1].dn) };
            let (ru, rdn) = if s == n { (0, 0) } else { (edges[s].u, edges[s].dn) };
            let rn = if s == n { 0 } else { edges[s].m as usize };

            // 0 = left item (index into the incoming partition), 1 = right
            // crossing, 2 = marker
            let mut arr_item: Vec<(usize, usize)> = vec![];
            let mut arr_class: Vec<usize> = vec![];
            for i in 0..lu {
                arr_item.push((0, i));
                arr_class.push(if edges[s - 1].sign_plus(i) { 0 } else { 1 });
            }
            for i in 0..rdn {
                let ci = ru + i;
                arr_item.push((1, ci));
                arr_class.push(if edges[s].sign_plus(ci) { 2 } else { 3 });
            }
            let mut dep_item: Vec<(usize, usize)> = vec![];
            let mut dep_class: Vec<usize> = vec![];
            for i in 0..ldn {
                let ci = lu + i;
                dep_item.push((0, ci));
                dep_class.push(if edges[s - 1].sign_plus(ci) { 0 } else { 1 });
            }
            for i in 0..ru {
                dep_item.push((1, i));
                dep_class.push(if edges[s].sign_plus(i) { 2 } else { 3 });
            }
            let mut virt_here = false;
            if virt_arr_site == Some(s) {
                arr_item.push((2, 0));
                arr_class.push(0); // the virtual arrival is (left,+)
                virt_here = true;
            }
            if let Some((ds, cls)) = virt_dep_site {
                if ds == s {
                    dep_item.push((2, 0));
                    dep_class.push(cls);
                    virt_here = true;
                }
            }
            if arr_item.len() != dep_item.len() {
                dp.clear();
                return;
            }
            let sz = arr_item.len();
            if sz > 8 {
                panic!("site of size {} exceeds the tabulated permutations (max 8); lower the deposit bound", sz);
            }

            for ((st, cost), closed) in dp.iter() {
                let base = st.nclass as usize;
                let mnode = base + rn;
                for perm in &perms[sz] {
                    let mut uf = Uf::new(mnode + 1);
                    // reattach the marker to its class
                    if st.mcls != 255 {
                        uf.union(mnode, st.mcls as usize);
                    }
                    let mut c = *cost;
                    for (ai, &di) in perm.iter().enumerate() {
                        c += cost_of(arr_class[ai], dep_class[di]);
                        let na = match arr_item[ai] {
                            (0, ci) => st.part[ci] as usize,
                            (1, ci) => base + ci,
                            _ => mnode,
                        };
                        let nd = match dep_item[di] {
                            (0, ci) => st.part[ci] as usize,
                            (1, ci) => base + ci,
                            _ => mnode,
                        };
                        uf.union(na, nd);
                    }
                    let mseen = st.mseen || virt_here;
                    // roots that stay open: those of the crossings of edge s
                    let mut labels: Vec<usize> = Vec::with_capacity(rn);
                    for ci in 0..rn {
                        labels.push(uf.find(base + ci));
                    }
                    let open_roots: HashSet<usize> = labels.iter().cloned().collect();
                    let mroot = uf.find(mnode);
                    // every real class present at this site
                    let mut roots: HashSet<usize> = HashSet::new();
                    for i in 0..base {
                        roots.insert(uf.find(i));
                    }
                    for ci in 0..rn {
                        roots.insert(uf.find(base + ci));
                    }
                    if mseen && !st.mclosed {
                        roots.insert(mroot);
                    }
                    let mut nclosed = *closed;
                    let mut mclosed = st.mclosed;
                    let marker_live = mseen && !st.mclosed;
                    for r in roots {
                        if open_roots.contains(&r) {
                            continue;
                        }
                        if marker_live && r == mroot {
                            mclosed = true; // the open walk has closed off
                        } else {
                            nclosed += 1;
                        }
                    }
                    // canonicalise the new partition
                    let mut map: HashMap<usize, u8> = HashMap::new();
                    let mut part = Vec::with_capacity(rn);
                    let mut next = 0u8;
                    for &l in &labels {
                        let e = *map.entry(l).or_insert_with(|| {
                            let v = next;
                            next += 1;
                            v
                        });
                        part.push(e);
                    }
                    let mcls = if mseen && !mclosed {
                        match map.get(&mroot) {
                            Some(&v) => v,
                            None => 255,
                        }
                    } else {
                        255
                    };
                    let nst = State { part, nclass: next, mcls, mseen, mclosed };
                    let e = ndp.entry((nst, c)).or_insert(i64::MAX);
                    if nclosed < *e {
                        *e = nclosed;
                    }
                }
            }
            dp = ndp;
            if dp.is_empty() {
                return;
            }
        }
    });

    let mut out: HashMap<i64, i64> = HashMap::new();
    for ((st, cost), closed) in dp.iter() {
        if !st.mseen || !st.mclosed {
            continue; // the marker must have appeared and closed
        }
        let e = out.entry(*cost).or_insert(i64::MAX);
        if *closed < *e {
            *e = *closed;
        }
    }
    out
}
