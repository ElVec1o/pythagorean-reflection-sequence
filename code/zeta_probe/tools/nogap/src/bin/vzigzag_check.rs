// vzigzag_check -- the ODD-SPAN generalisation of `zigzag_check`'s verified
// "spine + zigzag" (Through2) construction, on the EXTENDED end type
// `VEndpt = Endpt (+) Bool`.
//
// Model.  Sites 0..n, edge e (0 <= e < n) carrying m[e] parallel strands.  Two
// extra "virtual" ends VLO and VHI sit at sites `lo` and `hi` (0 <= lo < hi <= n);
// they are the two ends of ONE long virtual strand, so `partner` pairs them with
// each other.  The widths are ODD exactly on the travel interval:
//
//     m[e] odd    for lo <= e < hi
//     m[e] even   (and >= 2) otherwise
//
// which is what `SiteCost.PathData.mu_par` forces for a real configuration
// (mu j = travel kstar j mod 2, and travel is +-1 exactly on the travel interval).
// Then every site carries an EVEN number of ends: at an interior travel site
// odd+odd, at sites lo and hi odd+even+1(virtual), elsewhere even+even.
//
// Cut sites Z must avoid the closed interval [lo, hi] (in the Lean development
// that is the hypothesis `hgap`, which holds because a cut site has Phi = 0 and
// hence zero travel on both adjacent edges).
//
// The turn.  Write k(e) = 0 if lo <= e < hi (odd edge, NO spine) and k(e) = 1
// otherwise (even edge, strand 0 is the spine).  Edge e's "chain" is strands
// k(e) .. m[e]-1, an ODD number of strands in both cases, zigzagged:
//
//     bottom bounces   (k+1,k+2), (k+3,k+4), ...
//     top bounces      (k,k+1),  (k+2,k+3), ...
//
// so the chain is one path from strand k's bottom end to strand m-1's top end.
// The virtual strand plays the role of the MISSING spine across [lo, hi]: the
// spine line runs  spine(0)..spine(lo-1) -- VLO--VHI -- spine(hi)..spine(n-1),
// and the chain line runs back the other way.  Every run is then one cycle.
//
// Component counts are computed TWICE by independent methods (union-find on ends
// and explicit walk tracing) and asserted equal; the turn is separately validated
// as a fixed-point-free, same-site involution never pairing two different real
// edges at a cut site.  Target in every case: components == |Z| + 1.
//
// No dependencies.  Self-contained, one file per question, per this directory's
// convention.

// ---------------------------------------------------------------- end indexing

// Real end (e, i, side): side 0 = bottom (site e), side 1 = top (site e+1).
// Global ids: 2*(off[e]+i) + side for real, then NREAL, NREAL+1 for VLO, VHI.

#[derive(Clone)]
struct Cfg {
    n: usize,
    m: Vec<usize>,
    lo: usize,
    hi: usize,
    cut: Vec<bool>, // indexed by site 0..=n; true iff the site is in Z
    off: Vec<usize>,
}

impl Cfg {
    fn new(m: &[usize], lo: usize, hi: usize, zset: &[usize]) -> Cfg {
        let n = m.len();
        assert!(lo < hi && hi <= n);
        let mut off = vec![0usize; n + 1];
        for e in 0..n {
            off[e + 1] = off[e] + m[e];
        }
        let mut cut = vec![false; n + 1];
        for &z in zset {
            assert!(z >= 1 && z < n, "cut sites are interior");
            assert!(!(lo <= z && z <= hi), "hgap: no cut site inside [lo,hi]");
            cut[z] = true;
        }
        Cfg { n, m: m.to_vec(), lo, hi, cut, off }
    }

    fn k(&self, e: usize) -> usize {
        if self.lo <= e && e < self.hi { 0 } else { 1 }
    }
    fn nreal(&self) -> usize { 2 * self.off[self.n] }
    fn nends(&self) -> usize { self.nreal() + 2 }
    fn vlo(&self) -> usize { self.nreal() }
    fn vhi(&self) -> usize { self.nreal() + 1 }

    fn id(&self, e: usize, i: usize, side: usize) -> usize {
        debug_assert!(i < self.m[e]);
        2 * (self.off[e] + i) + side
    }
    /// (e, i, side) of a real end
    fn dec(&self, x: usize) -> (usize, usize, usize) {
        let side = x % 2;
        let s = x / 2;
        // binary search for the edge
        let mut e = 0usize;
        while self.off[e + 1] <= s {
            e += 1;
        }
        (e, s - self.off[e], side)
    }
    fn site(&self, x: usize) -> usize {
        if x == self.vlo() {
            self.lo
        } else if x == self.vhi() {
            self.hi
        } else {
            let (e, _, side) = self.dec(x);
            e + side
        }
    }
    /// edge index of a real end; None for virtual
    fn edge_of(&self, x: usize) -> Option<usize> {
        if x >= self.nreal() { None } else { Some(self.dec(x).0) }
    }

    fn pass_lo(&self, e: usize) -> bool { e >= 1 && !self.cut[e] }
    fn pass_hi(&self, e: usize) -> bool { e + 1 < self.n && !self.cut[e + 1] }

    fn partner(&self, x: usize) -> usize {
        if x == self.vlo() {
            self.vhi()
        } else if x == self.vhi() {
            self.vlo()
        } else {
            x ^ 1
        }
    }

    fn turn(&self, x: usize) -> usize {
        if x == self.vlo() {
            // the virtual end at site lo
            return if self.lo == 0 {
                self.id(0, 0, 0) // chainBot of edge 0 (which has k = 0)
            } else {
                self.id(self.lo - 1, 0, 1) // spineTop of edge lo-1 (k = 1)
            };
        }
        if x == self.vhi() {
            return if self.hi == self.n {
                self.id(self.n - 1, self.m[self.n - 1] - 1, 1) // chainTop of edge n-1
            } else {
                self.id(self.hi, 0, 0) // spineBot of edge hi (k = 1)
            };
        }
        let (e, i, side) = self.dec(x);
        let nn = self.m[e];
        let k = self.k(e);
        if side == 0 {
            // ---- bottom end, at site e
            if i >= k + 1 {
                // internal chain bounce at the bottom: (k+1,k+2), (k+3,k+4), ...
                let j = if (i - k) % 2 == 1 { i + 1 } else { i - 1 };
                self.id(e, j, 0)
            } else if k == 1 && i == 0 {
                // spineBot
                if self.pass_lo(e) {
                    let f = e - 1;
                    if self.k(f) == 1 {
                        self.id(f, 0, 1) // previous spine's top
                    } else {
                        // k(f)=0, k(e)=1  =>  e = hi
                        self.vhi()
                    }
                } else {
                    self.id(e, k, 0) // bounce into its own chain's loose bottom
                }
            } else {
                // chainBot (i == k)
                if self.pass_lo(e) {
                    self.id(e - 1, self.m[e - 1] - 1, 1) // previous chain's loose top
                } else if k == 1 {
                    self.id(e, 0, 0) // bounce into its own spine
                } else {
                    // k(e) = 0 and site e bounces  =>  e = 0 = lo
                    self.vlo()
                }
            }
        } else {
            // ---- top end, at site e+1
            if k <= i && i + 2 <= nn {
                // internal chain bounce at the top: (k,k+1), (k+2,k+3), ...
                let j = if (i - k) % 2 == 0 { i + 1 } else { i - 1 };
                self.id(e, j, 1)
            } else if k == 1 && i == 0 {
                // spineTop
                if self.pass_hi(e) {
                    let f = e + 1;
                    if self.k(f) == 1 {
                        self.id(f, 0, 0) // next spine's bottom
                    } else {
                        // k(f)=0, k(e)=1  =>  f = lo
                        self.vlo()
                    }
                } else {
                    self.id(e, nn - 1, 1) // bounce into its own chain's loose top
                }
            } else {
                // chainTop (i == nn-1)
                if self.pass_hi(e) {
                    self.id(e + 1, self.k(e + 1), 0) // next chain's loose bottom
                } else if k == 1 {
                    self.id(e, 0, 1) // bounce into its own spine
                } else {
                    // k(e) = 0 and site e+1 bounces  =>  e+1 = n = hi
                    self.vhi()
                }
            }
        }
    }
}

// ---------------------------------------------------------------- validation

fn validate_turn(c: &Cfg) -> Result<(), String> {
    for x in 0..c.nends() {
        let y = c.turn(x);
        if y >= c.nends() {
            return Err(format!("turn out of range at {}", x));
        }
        if y == x {
            return Err(format!("turn has a fixed point at {}", x));
        }
        if c.turn(y) != x {
            return Err(format!("turn is not an involution at {}", x));
        }
        if c.site(y) != c.site(x) {
            return Err(format!(
                "turn changes site at {} ({} -> {})",
                x,
                c.site(x),
                c.site(y)
            ));
        }
        if c.partner(x) == y {
            return Err(format!("turn agrees with partner at {}", x));
        }
        // hturn: two REAL ends on different edges are never paired at a cut site
        if let (Some(ex), Some(ey)) = (c.edge_of(x), c.edge_of(y)) {
            if ex != ey && c.cut[c.site(x)] {
                return Err(format!("hturn violated at site {}", c.site(x)));
            }
        }
    }
    // the partner map must itself be a fixed-point-free involution
    for x in 0..c.nends() {
        let y = c.partner(x);
        if y == x || c.partner(y) != x {
            return Err(format!("partner broken at {}", x));
        }
    }
    Ok(())
}

// ---- method 1: union-find over all ends, edges = partner and turn

struct Uf {
    p: Vec<usize>,
}
impl Uf {
    fn new(k: usize) -> Uf { Uf { p: (0..k).collect() } }
    fn find(&mut self, a: usize) -> usize {
        let mut a = a;
        while self.p[a] != a {
            self.p[a] = self.p[self.p[a]];
            a = self.p[a];
        }
        a
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.p[ra] = rb;
        }
    }
}

fn components_uf(c: &Cfg) -> usize {
    let mut uf = Uf::new(c.nends());
    for x in 0..c.nends() {
        uf.union(x, c.partner(x));
        uf.union(x, c.turn(x));
    }
    let mut seen = vec![false; c.nends()];
    let mut cnt = 0;
    for x in 0..c.nends() {
        let r = uf.find(x);
        if !seen[r] {
            seen[r] = true;
            cnt += 1;
        }
    }
    cnt
}

// ---- method 2: explicit alternating-walk tracing (partner, turn, partner, ...)

fn components_walk(c: &Cfg) -> usize {
    let mut seen = vec![false; c.nends()];
    let mut cnt = 0;
    for start in 0..c.nends() {
        if seen[start] {
            continue;
        }
        cnt += 1;
        let mut x = start;
        loop {
            if seen[x] {
                break;
            }
            seen[x] = true;
            let y = c.partner(x);
            seen[y] = true;
            x = c.turn(y);
        }
        // the alternating walk from `start` is a cycle; make sure we also caught
        // the other direction (it is the same cycle, but assert it explicitly)
        let mut x = start;
        loop {
            let y = c.turn(x);
            let z = c.partner(y);
            if !seen[z] {
                panic!("walk tracing asymmetric at {}", start);
            }
            if z == start {
                break;
            }
            x = z;
        }
    }
    cnt
}

// ---------------------------------------------------------------- sweeps

fn check_one(m: &[usize], lo: usize, hi: usize, zset: &[usize]) -> Result<usize, String> {
    let c = Cfg::new(m, lo, hi, zset);
    validate_turn(&c)?;
    let a = components_uf(&c);
    let b = components_walk(&c);
    if a != b {
        return Err(format!("component counts disagree: uf={} walk={}", a, b));
    }
    Ok(a)
}

fn subsets(n: usize) -> Vec<Vec<usize>> {
    // all subsets of {1..n-1}
    let k = if n >= 1 { n - 1 } else { 0 };
    let mut out = Vec::new();
    for mask in 0u32..(1u32 << k) {
        let mut s = Vec::new();
        for b in 0..k {
            if mask >> b & 1 == 1 {
                s.push(b + 1);
            }
        }
        out.push(s);
    }
    out
}

/// enumerate all width vectors: odd choices on [lo,hi), even choices elsewhere
fn widths(n: usize, lo: usize, hi: usize, odds: &[usize], evens: &[usize]) -> Vec<Vec<usize>> {
    let mut out: Vec<Vec<usize>> = vec![vec![]];
    for e in 0..n {
        let opts: &[usize] = if lo <= e && e < hi { odds } else { evens };
        let mut nxt = Vec::new();
        for base in &out {
            for &o in opts {
                let mut v = base.clone();
                v.push(o);
                nxt.push(v);
            }
        }
        out = nxt;
    }
    out
}

fn sweep(nmax: usize, odds: &[usize], evens: &[usize], label: &str) {
    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut first_fail: Option<String> = None;
    for n in 1..=nmax {
        for lo in 0..n {
            for hi in (lo + 1)..=n {
                for ws in widths(n, lo, hi, odds, evens) {
                    for z in subsets(n) {
                        if z.iter().any(|&zz| lo <= zz && zz <= hi) {
                            continue;
                        }
                        match check_one(&ws, lo, hi, &z) {
                            Ok(cnt) => {
                                if cnt == z.len() + 1 {
                                    pass += 1;
                                } else {
                                    fail += 1;
                                    if first_fail.is_none() {
                                        first_fail = Some(format!(
                                            "m={:?} lo={} hi={} Z={:?}: components={} expected={}",
                                            ws, lo, hi, z, cnt, z.len() + 1
                                        ));
                                    }
                                }
                            }
                            Err(e) => {
                                fail += 1;
                                if first_fail.is_none() {
                                    first_fail = Some(format!(
                                        "m={:?} lo={} hi={} Z={:?}: {}",
                                        ws, lo, hi, z, e
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!("{:<44} pass {:>8}  fail {:>6}", label, pass, fail);
    if let Some(f) = first_fail {
        println!("    FIRST COUNTEREXAMPLE: {}", f);
    }
}

fn main() {
    println!("vzigzag_check -- odd-span spine+zigzag with one long virtual strand");
    println!();
    sweep(5, &[1, 3], &[2, 4], "n<=5, odd in {1,3}, even in {2,4}");
    sweep(4, &[1, 3, 5], &[2, 4, 6], "n<=4, odd in {1,3,5}, even in {2,4,6}");
    sweep(6, &[3], &[2], "n<=6, odd = 3, even = 2");
    sweep(6, &[1], &[4], "n<=6, odd = 1, even = 4");
    sweep(3, &[1, 3, 5, 7], &[2, 4, 6, 8], "n<=3, odd<=7, even<=8");
    sweep(7, &[1, 3], &[2, 4], "n<=7, odd in {1,3}, even in {2,4}  (stress)");

    // the two configurations the Lean file names as witnesses
    println!();
    for &(name, m, lo, hi, z) in &[
        ("VZigzag.vz_witness_shield  (w3, span [1,2), Z={3})", [2usize, 3, 4, 2], 1usize, 2usize, [3usize].as_slice()),
        ("VZigzag.witNeg_shield      (witNeg, span [0,1), Z={2})", [1, 2, 2, 2], 0, 1, [2].as_slice()),
    ] {
        match check_one(&m, lo, hi, z) {
            Ok(cnt) => println!(
                "{:<56} components {} (expected {}) {}",
                name, cnt, z.len() + 1,
                if cnt == z.len() + 1 { "OK" } else { "MISMATCH" }
            ),
            Err(e) => println!("{:<56} ERROR {}", name, e),
        }
    }

    // a couple of long chains, checked individually
    println!();
    for &(n, lo, hi) in &[(12usize, 3usize, 8usize), (12, 0, 12), (12, 0, 1), (12, 11, 12)] {
        let m: Vec<usize> = (0..n)
            .map(|e| if lo <= e && e < hi { 1 + 2 * (e % 3) } else { 2 + 2 * (e % 3) })
            .collect();
        let z: Vec<usize> = (1..n).filter(|&s| !(lo <= s && s <= hi) && s % 2 == 1).collect();
        match check_one(&m, lo, hi, &z) {
            Ok(cnt) => println!(
                "n={} lo={} hi={} |Z|={} -> components {} (expected {}) {}",
                n, lo, hi, z.len(), cnt, z.len() + 1,
                if cnt == z.len() + 1 { "OK" } else { "MISMATCH" }
            ),
            Err(e) => println!("n={} lo={} hi={} -> ERROR {}", n, lo, hi, e),
        }
    }
}
