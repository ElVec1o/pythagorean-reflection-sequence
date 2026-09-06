// pdcut_check -- the two questions left open by BLOCK 341, checked numerically
// before being formalised.
//
// (A) WHEN IS A VIRTUAL SITE A CUT SITE?  `VZigzag.pd_shield_law_{pos,neg}` carries
//     two hypotheses, `hne0` and `hne1`: neither of the two virtual sites (absolute
//     sites `0` and `kstar`) is a cut site.  EltBridge already has read-offs for
//     `kstar < 0` (`cut_at_zero_iff`, `cut_at_kstar_iff`).  This sweep determines the
//     `kstar > 0` and `kstar = 0` read-offs, so the hypotheses can be discharged where
//     they are automatic and characterised where they are not.
//
//       cut(s)  <=>  alpha(s) = 0  &  beta(s) = 0  &  Phi(s) = 0,   with
//       alpha(s) = d(s-1) - [s=0] + eps*vL(s),  beta(s) = d(s) - eps*vR(s),
//       Phi(s)   = f(s-1) + [s=0] - vL(s),      f = travel kstar,
//       vL(s) = [not delta][s=kstar],           vR(s) = [delta][s=kstar].
//
//     Conjectures checked, over every (kstar, eps, delta, d) with kstar in [-3,3],
//     eps = +-1, delta in {0,1} and d : [-3,3] -> [-2,2] satisfying the parity
//     constraint (d j - f j) even:
//
//       C1  kstar > 0  =>  site 0 is NEVER cut          (Phi(0) = 1)
//       C2  kstar > 0  =>  cut(kstar) <=> !delta & d(kstar-1) = -eps & d(kstar) = 0
//       C3  kstar < 0  =>  cut(0)     <=> d(-1) = 1 & d(0) = 0        (known)
//       C4  kstar < 0  =>  cut(kstar) <=> delta & d(kstar-1) = 0 & d(kstar) = eps
//       C5  kstar = 0  =>  cut(0)     <=> !delta & d(-1) = 1 - eps & d(0) = 0
//       C6  kstar = 0  =>  every mu j is EVEN and >= 2
//
//     C6 is what makes the `kstar = 0` case reachable at all: it says the widths of a
//     zero-travel element satisfy `EltBridge.EvenWidths`, so `zz_shield_law` (BLOCK
//     339, all widths even, no virtual points, NO exclusion hypotheses) applies
//     directly and the `kstar = 0` case needs no `hne0`/`hne1`.
//
// (B) THE TWO NEW WITNESSES, computed rather than asserted:
//       witZero: kstar = 0, d(-1) = d(2) = 2  -> span [-1,2], widths (2,2,2,2),
//                cut sites {2} (relative), so walkCount should be 2;
//       witCut0: kstar = -1, d(-1) = 1        -> span [-1,0], widths (1,2),
//                cut sites {1} (relative) and 1 = -A IS the low virtual site,
//                so `hne0` FAILS and `NoCut` is FALSE for it.
//     For witZero the even-width spine+zigzag turn of BLOCK 339 is built here and its
//     component count computed twice (union-find and explicit walk tracing).
//
// No dependencies.  One file, one question, per this directory's convention.

// ------------------------------------------------------------ (A) the cut algebra

fn travel(kstar: i64, j: i64) -> i64 {
    if 0 <= j && j < kstar {
        1
    } else if kstar <= j && j < 0 {
        -1
    } else {
        0
    }
}

fn mu(d: i64, f: i64) -> i64 {
    if d == 0 && f == 0 {
        2
    } else {
        d.abs().max(f.abs())
    }
}

struct Pd {
    kstar: i64,
    eps: i64,
    delta: bool,
    lo: i64,
    d: Vec<i64>, // d[(j - lo) as usize]
}

impl Pd {
    fn dat(&self, j: i64) -> i64 {
        let i = j - self.lo;
        if i < 0 || i as usize >= self.d.len() {
            0
        } else {
            self.d[i as usize]
        }
    }
    fn v_d(&self, s: i64) -> i64 {
        if s == self.kstar { 1 } else { 0 }
    }
    fn v_l(&self, s: i64) -> i64 {
        if self.delta { 0 } else { self.v_d(s) }
    }
    fn v_r(&self, s: i64) -> i64 {
        if self.delta { self.v_d(s) } else { 0 }
    }
    fn v_arr(&self, s: i64) -> i64 {
        if s == 0 { 1 } else { 0 }
    }
    fn alpha(&self, s: i64) -> i64 {
        self.dat(s - 1) - self.v_arr(s) + self.eps * self.v_l(s)
    }
    fn beta(&self, s: i64) -> i64 {
        self.dat(s) - self.eps * self.v_r(s)
    }
    fn phi(&self, s: i64) -> i64 {
        travel(self.kstar, s - 1) + self.v_arr(s) - self.v_l(s)
    }
    fn cut(&self, s: i64) -> bool {
        self.alpha(s) == 0 && self.beta(s) == 0 && self.phi(s) == 0
    }
    /// legal PathData parity constraint
    fn par_ok(&self) -> bool {
        for j in (self.lo - 2)..(self.lo + self.d.len() as i64 + 2) {
            if (self.dat(j) - travel(self.kstar, j)).rem_euclid(2) != 0 {
                return false;
            }
        }
        true
    }
}

fn sweep_cut_algebra() -> (u64, u64) {
    let lo: i64 = -3;
    let width: usize = 7; // j in [-3, 3]
    let vals: [i64; 5] = [-2, -1, 0, 1, 2];
    let mut pass = 0u64;
    let mut fail = 0u64;
    let total = vals.len().pow(width as u32);
    for kstar in -3i64..=3 {
        for &eps in &[1i64, -1] {
            for &delta in &[false, true] {
                for code0 in 0..total {
                    let mut code = code0;
                    let mut d = vec![0i64; width];
                    for k in 0..width {
                        d[k] = vals[code % vals.len()];
                        code /= vals.len();
                    }
                    let p = Pd { kstar, eps, delta, lo, d };
                    if !p.par_ok() {
                        continue;
                    }
                    let mut ok = true;
                    if kstar > 0 {
                        // C1
                        if p.cut(0) {
                            ok = false;
                        }
                        // C2
                        let want = !delta && p.dat(kstar - 1) == -eps && p.dat(kstar) == 0;
                        if p.cut(kstar) != want {
                            ok = false;
                        }
                    } else if kstar < 0 {
                        // C3
                        let want0 = p.dat(-1) == 1 && p.dat(0) == 0;
                        if p.cut(0) != want0 {
                            ok = false;
                        }
                        // C4
                        let want = delta && p.dat(kstar - 1) == 0 && p.dat(kstar) == eps;
                        if p.cut(kstar) != want {
                            ok = false;
                        }
                    } else {
                        // C5
                        let want0 = !delta && p.dat(-1) == 1 - eps && p.dat(0) == 0;
                        if p.cut(0) != want0 {
                            ok = false;
                        }
                        // C6
                        for j in lo..(lo + width as i64) {
                            let m = mu(p.dat(j), travel(kstar, j));
                            if m % 2 != 0 || m < 2 {
                                ok = false;
                            }
                        }
                    }
                    if ok {
                        pass += 1;
                    } else {
                        fail += 1;
                        if fail < 6 {
                            println!(
                                "  FAIL kstar={} eps={} delta={} d={:?}",
                                kstar, eps, delta, p.d
                            );
                        }
                    }
                }
            }
        }
    }
    (pass, fail)
}

// ------------------------------------------------------- (B) span, widths, cut set

/// span = least interval containing 0 and every j with d j != 0 or travel != 0
fn span(p: &Pd) -> (i64, i64) {
    let mut a = 0i64;
    let mut b = 0i64;
    for j in (p.lo - 2)..(p.lo + p.d.len() as i64 + 2) {
        if p.dat(j) != 0 || travel(p.kstar, j) != 0 {
            a = a.min(j);
            b = b.max(j);
        }
    }
    (a, b)
}

fn widths(p: &Pd) -> Vec<usize> {
    let (a, b) = span(p);
    (a..=b)
        .map(|j| mu(p.dat(j), travel(p.kstar, j)) as usize)
        .collect()
}

/// pdCutSites: relative offsets s with 0 < s < width and cut(A + s)
fn cut_sites(p: &Pd) -> Vec<i64> {
    let (a, b) = span(p);
    let w = b - a + 1;
    (1..w).filter(|&s| p.cut(a + s)).collect()
}

// -------------------------------- the even-width spine+zigzag turn (BLOCK 339)

struct Even {
    n: usize,
    m: Vec<usize>,
    cut: Vec<bool>, // sites 0..=n
    off: Vec<usize>,
}

impl Even {
    fn new(m: &[usize], zset: &[i64]) -> Even {
        let n = m.len();
        for &w in m {
            assert!(w >= 2 && w % 2 == 0, "even widths only");
        }
        let mut off = vec![0usize; n + 1];
        for e in 0..n {
            off[e + 1] = off[e] + m[e];
        }
        let mut cut = vec![false; n + 1];
        for &z in zset {
            assert!(z >= 1 && (z as usize) < n, "cut sites are interior");
            cut[z as usize] = true;
        }
        Even { n, m: m.to_vec(), cut, off }
    }
    fn nends(&self) -> usize {
        2 * self.off[self.n]
    }
    fn id(&self, e: usize, i: usize, side: usize) -> usize {
        2 * (self.off[e] + i) + side
    }
    fn dec(&self, x: usize) -> (usize, usize, usize) {
        let side = x % 2;
        let s = x / 2;
        let mut e = 0;
        while e + 1 < self.n && self.off[e + 1] <= s {
            e += 1;
        }
        (e, s - self.off[e], side)
    }
    fn site(&self, x: usize) -> usize {
        let (e, _, side) = self.dec(x);
        e + side
    }
    fn partner(&self, x: usize) -> usize {
        x ^ 1
    }
    fn pass_lo(&self, e: usize) -> bool {
        e >= 1 && !self.cut[e]
    }
    fn pass_hi(&self, e: usize) -> bool {
        e + 1 < self.n && !self.cut[e + 1]
    }
    /// k = 1 everywhere: strand 0 is the spine, strands 1..m-1 the (odd) chain
    fn turn(&self, x: usize) -> usize {
        let (e, i, side) = self.dec(x);
        let nn = self.m[e];
        if side == 0 {
            if i >= 2 {
                let j = if (i - 1) % 2 == 1 { i + 1 } else { i - 1 };
                self.id(e, j, 0)
            } else if i == 0 {
                if self.pass_lo(e) {
                    self.id(e - 1, 0, 1)
                } else {
                    self.id(e, 1, 0)
                }
            } else {
                if self.pass_lo(e) {
                    self.id(e - 1, self.m[e - 1] - 1, 1)
                } else {
                    self.id(e, 0, 0)
                }
            }
        } else {
            if 1 <= i && i + 2 <= nn {
                let j = if (i - 1) % 2 == 0 { i + 1 } else { i - 1 };
                self.id(e, j, 1)
            } else if i == 0 {
                if self.pass_hi(e) {
                    self.id(e + 1, 0, 0)
                } else {
                    self.id(e, nn - 1, 1)
                }
            } else {
                if self.pass_hi(e) {
                    self.id(e + 1, 1, 0)
                } else {
                    self.id(e, 0, 1)
                }
            }
        }
    }
    fn validate(&self) -> Result<(), String> {
        for x in 0..self.nends() {
            let y = self.turn(x);
            if y >= self.nends() {
                return Err(format!("turn out of range at {}", x));
            }
            if y == x {
                return Err(format!("fixed point at {}", x));
            }
            if self.turn(y) != x {
                return Err(format!("not an involution at {}", x));
            }
            if self.site(y) != self.site(x) {
                return Err(format!("site changed at {}", x));
            }
            if self.partner(x) == y {
                return Err(format!("turn = partner at {}", x));
            }
            let (ex, _, _) = self.dec(x);
            let (ey, _, _) = self.dec(y);
            if ex != ey && self.cut[self.site(x)] {
                return Err(format!("hturn violated at site {}", self.site(x)));
            }
        }
        Ok(())
    }
    fn components_uf(&self) -> usize {
        let k = self.nends();
        let mut p: Vec<usize> = (0..k).collect();
        fn find(p: &mut Vec<usize>, a: usize) -> usize {
            let mut a = a;
            while p[a] != a {
                p[a] = p[p[a]];
                a = p[a];
            }
            a
        }
        for x in 0..k {
            let a = find(&mut p, x);
            let b = find(&mut p, self.partner(x));
            p[a] = b;
            let a = find(&mut p, x);
            let b = find(&mut p, self.turn(x));
            p[a] = b;
        }
        let mut roots = std::collections::BTreeSet::new();
        for x in 0..k {
            let r = find(&mut p, x);
            roots.insert(r);
        }
        roots.len()
    }
    fn components_walk(&self) -> usize {
        let k = self.nends();
        let mut seen = vec![false; k];
        let mut c = 0;
        for start in 0..k {
            if seen[start] {
                continue;
            }
            c += 1;
            let mut x = start;
            loop {
                seen[x] = true;
                let y = self.partner(x);
                seen[y] = true;
                let z = self.turn(y);
                if z == start {
                    break;
                }
                x = z;
            }
        }
        c
    }
}

fn report(name: &str, p: &Pd) -> (Vec<usize>, Vec<i64>) {
    let (a, b) = span(p);
    let w = widths(p);
    let z = cut_sites(p);
    println!(
        "  {}: kstar={} eps={} delta={} span=[{},{}] width={} widths={:?} cutSites={:?}  (-A={}, kstar-A={})",
        name,
        p.kstar,
        p.eps,
        p.delta,
        a,
        b,
        b - a + 1,
        w,
        z,
        -a,
        p.kstar - a
    );
    (w, z)
}

fn main() {
    println!("pdcut_check");
    println!();
    println!("(A) cut-site read-offs at the two virtual sites, C1..C6");
    let (pass, fail) = sweep_cut_algebra();
    println!("  pass = {}, fail = {}", pass, fail);
    assert_eq!(fail, 0, "a cut read-off conjecture is FALSE");
    println!();

    println!("(B) the two new witnesses");
    // witZero: kstar = 0, d(-1) = 2, d(2) = 2
    let wz = Pd {
        kstar: 0,
        eps: 1,
        delta: true,
        lo: -3,
        d: vec![0, 0, 2, 0, 0, 2, 0], // j = -3..3
    };
    assert!(wz.par_ok(), "witZero violates the parity constraint");
    let (wzw, wzz) = report("witZero", &wz);
    assert_eq!(wzw, vec![2, 2, 2, 2]);
    assert_eq!(wzz, vec![2]);

    // witCut0: kstar = -1, d(-1) = 1
    let wc = Pd {
        kstar: -1,
        eps: 1,
        delta: false,
        lo: -3,
        d: vec![0, 0, 1, 0, 0, 0, 0],
    };
    assert!(wc.par_ok(), "witCut0 violates the parity constraint");
    let (wcw, wcz) = report("witCut0", &wc);
    assert_eq!(wcw, vec![1, 2]);
    assert_eq!(wcz, vec![1]);
    // the low virtual site of the negative-travel configuration is kstar - A = 0,
    // the high one is -A = 1, and 1 IS a cut site: hne0 fails, NoCut is false.
    let (a, _) = span(&wc);
    assert!(wcz.contains(&(-a)), "expected -A to be a cut site of witCut0");
    println!("  witCut0: -A = {} IS in cutSites  =>  hne0 FAILS, NoCut is FALSE", -a);
    println!();

    // witCutK: kstar = 1, d(0) = -1, d(2) = 2
    let wk = Pd {
        kstar: 1,
        eps: 1,
        delta: false,
        lo: -3,
        d: vec![0, 0, 0, -1, 0, 2, 0],
    };
    assert!(wk.par_ok(), "witCutK violates the parity constraint");
    let (wkw, wkz) = report("witCutK", &wk);
    assert_eq!(wkw, vec![1, 2, 2]);
    assert_eq!(wkz, vec![1]);
    let (ak, _) = span(&wk);
    assert!(wkz.contains(&(wk.kstar - ak)), "expected kstar-A to be a cut site of witCutK");
    println!(
        "  witCutK: kstar - A = {} IS in cutSites  =>  hne1 FAILS, NoCut is FALSE",
        wk.kstar - ak
    );
    println!();

    println!("(C) witZero through the even-width spine+zigzag turn");
    let ev = Even::new(&wzw, &wzz);
    match ev.validate() {
        Ok(()) => println!("  turn validated (involution, fixed-point-free, site-preserving, hturn)"),
        Err(e) => panic!("turn invalid: {}", e),
    }
    let c1 = ev.components_uf();
    let c2 = ev.components_walk();
    println!("  components: union-find = {}, walk-tracing = {}", c1, c2);
    assert_eq!(c1, c2, "the two component counters disagree");
    assert_eq!(c1, wzz.len() + 1, "walkCount != |Z| + 1");
    println!("  walkCount = |Z| + 1 = {}", c1);
    println!();

    // A wider sweep of even-width configurations reachable from kstar = 0 elements.
    println!("(D) sweep: kstar = 0 elements, all widths even, every interior cut set");
    let mut n_ok = 0u64;
    for n in 2usize..=5 {
        let ws: [usize; 2] = [2, 4];
        let total = ws.len().pow(n as u32);
        for code0 in 0..total {
            let mut code = code0;
            let mut m = vec![0usize; n];
            for k in 0..n {
                m[k] = ws[code % ws.len()];
                code /= ws.len();
            }
            for zcode in 0..(1u32 << (n.saturating_sub(1))) {
                let mut z = Vec::new();
                for s in 1..n {
                    if zcode & (1 << (s - 1)) != 0 {
                        z.push(s as i64);
                    }
                }
                let e = Even::new(&m, &z);
                e.validate().expect("turn invalid");
                let a = e.components_uf();
                let b = e.components_walk();
                assert_eq!(a, b);
                assert_eq!(a, z.len() + 1, "m={:?} z={:?} gave {}", m, z, a);
                n_ok += 1;
            }
        }
    }
    println!("  {} configurations, all walkCount = |Z| + 1", n_ok);
    println!();
    println!("ALL CHECKS PASSED");
}
