// mu = 4: sites with more than two pairings.
//
// Edge `j` carries `m_j` strands, `u_j = dn_j = m_j/2` each way (bulk, f = 0).
// `pu_j` of the up strands are "+" and `pd_j` of the down strands are "+", and
// the deposit is `a_j = 2*(pd_j - pu_j)`.  A strand carries one sign at both
// ends.  At site `s` the arrivals are the tops of edge `s-1`'s up strands
// (classes 0/1 by sign) and the bottoms of edge `s`'s down strands (classes
// 2/3); the departures are the tops of edge `s-1`'s down strands and the
// bottoms of edge `s`'s up strands.  Classes 0,1 are the left edge and 2,3 the
// right, so `cost_of` reads bounce/flip/pass off the class pair, and a pair is
// a PASS exactly when the two classes lie in different halves.
//
// The element is the deposit vector `a`; a realisation is `(m, pu, pd)`.  The
// relaxed length minimises `sum m + sum site cost` over realisations, so `m_j`
// above the minimum is allowed and swept.  Total cost decomposes over sites, so
// the min-cost pairings are the product of the per-site min-cost bijections --
// that is what makes the walk count computable here.

use std::collections::HashSet;

#[inline]
fn cost_of(i: usize, j: usize) -> usize {
    if i == j { 0 } else if i / 2 == j / 2 { 2 } else { 1 }
}

struct Dsu(Vec<usize>);
impl Dsu {
    fn new(n: usize) -> Self { Dsu((0..n).collect()) }
    fn find(&mut self, a: usize) -> usize {
        if self.0[a] != a { let r = self.find(self.0[a]); self.0[a] = r; }
        self.0[a]
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb { self.0[ra] = rb; }
    }
}

fn perms(n: usize) -> Vec<Vec<usize>> {
    let mut out = vec![];
    let mut idx: Vec<usize> = (0..n).collect();
    fn go(k: usize, idx: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if k == idx.len() { out.push(idx.clone()); return; }
        for i in k..idx.len() { idx.swap(k, i); go(k + 1, idx, out); idx.swap(k, i); }
    }
    go(0, &mut idx, &mut out);
    out
}

pub fn run(nmax: usize, amax: i64) {
    println!("[cutturn] mu=4 chains, n = 2..{nmax}, deposits |a_j| <= {amax}, sum a = 0");
    println!("[cutturn] realisations sweep m_j over the minimum and the minimum + 2");
    let mut tested = 0u64;
    let mut pass_at_cut = 0u64;
    let mut walks_ne = 0u64;
    let mut saw_mu4 = 0u64;
    let mut big_site = 0u64;          // sites with more than two pairings
    let mut pe_total = 0u64;          // minimal data passing at EVERY non-cut site
    let mut pe_wrong = 0u64;          // ... of those, how many miss |Z|+1 walks
    let mut noncut_sites = 0u64;      // interior non-cut sites seen
    let mut noncut_no_pass = 0u64;    // ... where NO min-cost pairing passes
    let mut cut_with_pass = 0u64;     // cut sites where SOME min-cost pairing passes
    let mut rows: Vec<String> = vec![];
    for n in 2..=nmax {
        let vals: Vec<i64> = (-(amax / 2)..=(amax / 2)).map(|x| 2 * x).collect();
        let total = vals.len().pow(n as u32);
        for code in 0..total {
            let mut c = code;
            let mut a = vec![0i64; n];
            for j in 0..n { a[j] = vals[c % vals.len()]; c /= vals.len(); }
            if a.iter().sum::<i64>() != 0 { continue; }
            let ncut = (1..n).filter(|&s| a[s - 1] == 0 && a[s] == 0).count();
            // realisations
            let mbase: Vec<usize> = a.iter().map(|&x| (x.unsigned_abs() as usize).max(2)).collect();
            let mut best_cost = usize::MAX;
            let mut best_walks = usize::MAX;
            let mut best_pass = false;
            let mut pe_seen = 0u64;
            let mut pe_bad = 0u64;
            for mextra in 0usize..(1usize << n) {
                let m: Vec<usize> = (0..n).map(|j| mbase[j] + 2 * ((mextra >> j) & 1)).collect();
                if m.iter().any(|&x| x > 4) { continue; }
                let u: Vec<usize> = m.iter().map(|&x| x / 2).collect();
                // pu ranges
                let mut puv = vec![0usize; n];
                let mut stack = vec![0usize];
                // iterate pu vectors by odometer
                loop {
                    let mut ok = true;
                    let mut pd = vec![0usize; n];
                    for j in 0..n {
                        let p = puv[j] as i64 + a[j] / 2;
                        if p < 0 || p > u[j] as i64 || puv[j] > u[j] { ok = false; break; }
                        pd[j] = p as usize;
                    }
                    if ok {
                        // strand ids: edge j, up strand i -> off[j]+i ; down strand i -> off[j]+u[j]+i
                        let mut off = vec![0usize; n + 1];
                        for j in 0..n { off[j + 1] = off[j] + m[j]; }
                        let nstr = off[n];
                        let mut total_cost: usize = m.iter().sum();
                        let mut site_opts: Vec<Vec<Vec<(usize, usize)>>> = vec![];
                        let mut feasible = true;
                        for s in 0..=n {
                            // arrivals: (class, strand)
                            let mut arr: Vec<(usize, usize)> = vec![];
                            let mut dep: Vec<(usize, usize)> = vec![];
                            if s > 0 {
                                let l = s - 1;
                                for i in 0..u[l] { arr.push((if i < puv[l] { 0 } else { 1 }, off[l] + i)); }
                                for i in 0..u[l] { dep.push((if i < pd[l] { 0 } else { 1 }, off[l] + u[l] + i)); }
                            }
                            if s < n {
                                for i in 0..u[s] { arr.push((if i < pd[s] { 2 } else { 3 }, off[s] + u[s] + i)); }
                                for i in 0..u[s] { dep.push((if i < puv[s] { 2 } else { 3 }, off[s] + i)); }
                            }
                            if arr.len() != dep.len() { feasible = false; break; }
                            if arr.len() > 2 { big_site += 1; }
                            let is_cut = s >= 1 && s < n && a[s - 1] == 0 && a[s] == 0;
                            let mut bestc = usize::MAX;
                            let mut opts: Vec<Vec<(usize, usize)>> = vec![];
                            for p in perms(arr.len()) {
                                let cst: usize = (0..arr.len())
                                    .map(|i| cost_of(arr[i].0, dep[p[i]].0)).sum();
                                let pairing: Vec<(usize, usize)> = (0..arr.len())
                                    .map(|i| (arr[i].1, dep[p[i]].1)).collect();
                                let passes = (0..arr.len())
                                    .any(|i| arr[i].0 / 2 != dep[p[i]].0 / 2);
                                let mut tagged = pairing.clone();
                                if passes { tagged.push((usize::MAX, s)); }  // pass marker
                                if cst < bestc { bestc = cst; opts = vec![tagged]; }
                                else if cst == bestc { opts.push(tagged); }
                            }
                            // does SOME min-cost pairing at this site pass?
                            let any_pass = opts.iter().any(|o| o.iter().any(|&(x, _)| x == usize::MAX));
                            if !is_cut && s >= 1 && s < n {
                                noncut_sites += 1;
                                if !any_pass { noncut_no_pass += 1; }
                            }
                            if is_cut && any_pass { cut_with_pass += 1; }
                            total_cost += bestc;
                            site_opts.push(opts);
                        }
                        if feasible {
                            if m.iter().any(|&x| x == 4) { saw_mu4 += 1; }
                            // product over sites of the min-cost bijections
                            let mut counts = vec![0usize; site_opts.len()];
                            loop {
                                let mut dsu = Dsu::new(nstr);
                                let mut passed_cut = false;
                                for (si, &ci) in counts.iter().enumerate() {
                                    for &(x, y) in &site_opts[si][ci] {
                                        if x == usize::MAX {
                                            let s = y;
                                            if s >= 1 && s < n && a[s - 1] == 0 && a[s] == 0 {
                                                passed_cut = true;
                                            }
                                        } else { dsu.union(x, y); }
                                    }
                                }
                                let mut roots = HashSet::new();
                                for x in 0..nstr { let r = dsu.find(x); roots.insert(r); }
                                let walks = roots.len();
                                // does this datum pass at EVERY interior non-cut site?
                                let mut passes_everywhere = true;
                                for s2 in 1..n {
                                    if a[s2 - 1] == 0 && a[s2] == 0 { continue; }
                                    let opt = &site_opts[s2][counts[s2]];
                                    if !opt.iter().any(|&(x, _)| x == usize::MAX) {
                                        passes_everywhere = false;
                                    }
                                }
                                if total_cost < best_cost {
                                    best_cost = total_cost; best_walks = walks; best_pass = passed_cut;
                                    pe_seen = 0; pe_bad = 0;
                                } 
                                if total_cost == best_cost && passes_everywhere && !passed_cut {
                                    pe_seen += 1;
                                    if walks != ncut + 1 { pe_bad += 1; }
                                }
                                if total_cost == best_cost {
                                    best_walks = best_walks.min(walks);
                                    if passed_cut { best_pass = true; }
                                }
                                let mut i = 0;
                                loop {
                                    if i == counts.len() { break; }
                                    counts[i] += 1;
                                    if counts[i] < site_opts[i].len() { break; }
                                    counts[i] = 0; i += 1;
                                }
                                if i == counts.len() { break; }
                            }
                        }
                    }
                    // advance pu odometer
                    let mut i = 0;
                    loop {
                        if i == n { break; }
                        puv[i] += 1;
                        if puv[i] <= u[i] { break; }
                        puv[i] = 0; i += 1;
                    }
                    if i == n { break; }
                    let _ = &mut stack;
                }
            }
            if best_cost == usize::MAX { continue; }
            tested += 1;
            if best_pass { pass_at_cut += 1; }
            pe_total += pe_seen;
            pe_wrong += pe_bad;
            if best_walks != ncut + 1 {
                walks_ne += 1;
                if rows.len() < 8 {
                    rows.push(format!("    a={:?}  |Z|={}  min cost={}  walks at min={}  |Z|+1={}",
                        a, ncut, best_cost, best_walks, ncut + 1));
                }
            }
        }
    }
    println!("  {tested} elements (deposit vectors with sum 0)");
    println!("  realisations reaching mu=4 on some edge      : {saw_mu4}");
    println!("  sites offering more than two pairings        : {big_site}");
    println!("  interior non-cut sites                       : {noncut_sites}");
    println!("  ... where NO min-cost pairing passes         : {noncut_no_pass}");
    println!("  cut sites where SOME min-cost pairing passes : {cut_with_pass}");
    println!("  min-cost pairings that pass at a cut site    : {pass_at_cut}");
    println!("  elements with walks-at-min != |Z|+1          : {walks_ne}");
    println!("  minimal data passing at EVERY non-cut site   : {pe_total}");
    println!("  ... of those, walks != |Z|+1                 : {pe_wrong}");
    for r in &rows { println!("{}", r); }
}
