// maxchain -- does the rank-one telescoping that solved the travel/bulk chain
// (paper/journal/merged_novel_paper.tex, prop:travelexact / prop:bulkexact) apply to
// H1c's boundary-value recursion?
//
// H1c's bulk model, read off EltBridge.lean (LocalState.muOf 6067, LocalState.siteOf
// 6070, flagStepB's weight x^(sigma.st.muOf + tau.st.siteOf) at 7645,
// interior_kernel_eq_max 5862, sum_signed_eq_magnitudes / sum_prod_signed ~10160):
//
//   states  = deposit magnitudes a >= 0, with sign multiplicity m(b) = 1 if b=0 else 2
//   mu(a)   = 2 if a = 0, else a                      (fcur = 0, plain site)
//   step a -> b weighs  m(b) * X^( mu(a) + max(a,b) )
//   u(a)    = generating function of ALL walks from a (any length, incl. empty)
//
//           u(a) = 1 + X^mu(a) * sum_{b>=0} m(b) X^max(a,b) u(b)                 (*)
//
// This program checks, in exact i128 arithmetic truncated at degree D:
//
//  [1] BRUTE   solve (*) by direct iteration of the raw max-kernel double sum
//              (no algebra applied), plus an independent explicit DFS walk
//              enumeration at small D as a third opinion.
//  [2] CHAIN   the claim of this session: (*) collapses to a TWO-dimensional linear
//              recursion in a, with one global scalar shooting unknown T.  Namely with
//                 S(a)  = sum_{b<=a} m(b) u(b),   S'(a) = sum_{b<=a} m(b) X^b u(b),
//                 T     = S'(infinity),
//              the self-referential term cancels EXACTLY and
//                 u(a) = 1 + X^{2a} S(a-1) - X^a S'(a-1) + X^a T        (a >= 1)
//                 ( S(a), S'(a) ) = M_a ( S(a-1), S'(a-1) ) + src_a + T * srcT_a
//                 M_a = [[1+2X^{2a}, -2X^a], [2X^{3a}, 1-2X^{2a}]]
//              with S(0)=S'(0)=u(0)=1+X^2 T.  T is then fixed by S'(A)=T.
//  [3] STRUCT  M_a = I + c_a N_a with c_a = 2 X^{2a}, N_a^2 = 0, det M_a = 1 -- i.e.
//              EXACTLY the one-parameter rank-one-nilpotent family of prop:bulkexact,
//              at index shift +1.
//  [4] CLOSED  hence the telescoping of prop:bulkexact applies verbatim to the
//              homogeneous part; the predicted closed forms (this session's shift of
//              the bulk pair) are
//                 A_inf = sum_{k>=1} (-1)^{k-1} 2^k (1-X)^{k-1} X^{k^2} / (X;X)_{2k-1}
//                 B_inf = sum_{k>=0}            2^k (X-1)^k     X^{k^2+k} / (X;X)_{2k}
//              for the homogeneous chain started at (A_0,B_0)=(0,1), B = -S'.
//
// Rust only (repo rule: never Python for enumeration).  cargo run --release --bin maxchain

type Poly = Vec<i128>;

fn zero(d: usize) -> Poly { vec![0; d + 1] }
fn one(d: usize) -> Poly { let mut p = zero(d); p[0] = 1; p }
fn xpow(d: usize, k: usize) -> Poly { let mut p = zero(d); if k <= d { p[k] = 1; } p }

fn add(a: &Poly, b: &Poly) -> Poly {
    a.iter().zip(b.iter()).map(|(x, y)| x.checked_add(*y).expect("overflow in add")).collect()
}
fn sub(a: &Poly, b: &Poly) -> Poly {
    a.iter().zip(b.iter()).map(|(x, y)| x.checked_sub(*y).expect("overflow in sub")).collect()
}
fn scal(a: &Poly, c: i128) -> Poly {
    a.iter().map(|x| x.checked_mul(c).expect("overflow in scal")).collect()
}
fn shift(a: &Poly, k: usize) -> Poly {
    let d = a.len() - 1;
    let mut out = zero(d);
    for i in 0..=d { if i + k <= d { out[i + k] = a[i]; } }
    out
}
fn mul(a: &Poly, b: &Poly) -> Poly {
    let d = a.len() - 1;
    let mut out = zero(d);
    for i in 0..=d {
        if a[i] == 0 { continue; }
        for j in 0..=(d - i) {
            if b[j] == 0 { continue; }
            let t = a[i].checked_mul(b[j]).expect("overflow in mul");
            out[i + j] = out[i + j].checked_add(t).expect("overflow in mul-acc");
        }
    }
    out
}
/// formal inverse; requires constant term +-1
fn inv(a: &Poly) -> Poly {
    let d = a.len() - 1;
    assert!(a[0] == 1 || a[0] == -1, "inverse needs unit constant term, got {}", a[0]);
    let mut out = zero(d);
    out[0] = a[0];
    for n in 1..=d {
        let mut s: i128 = 0;
        for k in 1..=n { s += a[k] * out[n - k]; }
        out[n] = -a[0] * s;
    }
    out
}
fn eqp(a: &Poly, b: &Poly) -> bool { a == b }

fn muof(a: usize) -> usize { if a == 0 { 2 } else { a } }
fn mult(b: usize) -> i128 { if b == 0 { 1 } else { 2 } }

// ---------------------------------------------------------------- [1] BRUTE

/// Solve (*) by literal iteration of the raw max-kernel double sum.
fn brute(d: usize) -> Vec<Poly> {
    let amax = d;
    let mut u: Vec<Poly> = (0..=amax).map(|_| one(d)).collect();
    // each application of the kernel raises order by >= 2, so d/2+2 sweeps are exact
    for _ in 0..(d / 2 + 3) {
        let mut nu: Vec<Poly> = Vec::with_capacity(amax + 1);
        for a in 0..=amax {
            let mut acc = zero(d);
            for b in 0..=amax {
                let e = muof(a) + a.max(b);
                if e > d { continue; }
                acc = add(&acc, &scal(&shift(&u[b], e), mult(b)));
            }
            nu.push(add(&one(d), &acc));
        }
        u = nu;
    }
    u
}

/// Independent third opinion at small D: explicit DFS over walks, no fixed point.
fn dfs_walks(d: usize, start: usize) -> Poly {
    fn go(d: usize, a: usize, deg: usize, mlt: i128, out: &mut Poly) {
        out[deg] += mlt;
        for b in 0..=d {
            let e = muof(a) + a.max(b);
            if deg + e > d { continue; }
            go(d, b, deg + e, mlt * mult(b), out);
        }
    }
    let mut out = zero(d);
    go(d, start, 0, 1, &mut out);
    out
}

// ---------------------------------------------------------------- [2] CHAIN

/// An affine function of the shooting unknown T: p + q*T.
#[derive(Clone)]
struct Aff { p: Poly, q: Poly }
impl Aff {
    fn add(&self, o: &Aff) -> Aff { Aff { p: add(&self.p, &o.p), q: add(&self.q, &o.q) } }
    fn sub(&self, o: &Aff) -> Aff { Aff { p: sub(&self.p, &o.p), q: sub(&self.q, &o.q) } }
    fn scal(&self, c: i128) -> Aff { Aff { p: scal(&self.p, c), q: scal(&self.q, c) } }
    fn shift(&self, k: usize) -> Aff { Aff { p: shift(&self.p, k), q: shift(&self.q, k) } }
    fn eval(&self, t: &Poly) -> Poly { add(&self.p, &mul(&self.q, t)) }
}

/// The two-dimensional chain with shooting.  Returns (u, T).
fn chain(d: usize) -> (Vec<Poly>, Poly) {
    let amax = d;
    // S(0) = S'(0) = u(0) = 1 + X^2 T   (mu(0)=2, m(0)=1, and X^0 S(0) - S'(0) = 0)
    let mut s = Aff { p: one(d), q: xpow(d, 2) };
    let mut sp = Aff { p: one(d), q: xpow(d, 2) };
    let mut us: Vec<Aff> = vec![Aff { p: one(d), q: xpow(d, 2) }];
    for a in 1..=amax {
        // u(a) = 1 + X^{2a} S(a-1) - X^a S'(a-1) + X^a * T
        let ua = Aff { p: one(d), q: zero(d) }
            .add(&s.shift(2 * a))
            .sub(&sp.shift(a))
            .add(&Aff { p: zero(d), q: xpow(d, a) });
        s = s.add(&ua.scal(2));
        sp = sp.add(&ua.shift(a).scal(2));
        us.push(ua);
    }
    // closure: S'(amax) = T, since the omitted tail has order > amax >= d
    let t = mul(&sp.p, &inv(&sub(&one(d), &sp.q)));
    (us.iter().map(|a| a.eval(&t)).collect(), t)
}

// ---------------------------------------------------------------- [3][4] STRUCT/CLOSED

/// homogeneous chain in (A,B) = (S, -S'), started at (0,1) at index a=0
fn homog(d: usize) -> (Poly, Poly) {
    let mut a_ = zero(d);
    let mut b_ = one(d);
    for a in 1..=d {
        let na = add(&add(&a_, &scal(&shift(&a_, 2 * a), 2)), &scal(&shift(&b_, a), 2));
        let nb = sub(&sub(&b_, &scal(&shift(&b_, 2 * a), 2)), &scal(&shift(&a_, 3 * a), 2));
        a_ = na; b_ = nb;
    }
    (a_, b_)
}

fn qpoch(d: usize, r: usize) -> Poly {
    let mut p = one(d);
    for i in 1..=r { p = mul(&p, &sub(&one(d), &xpow(d, i))); }
    p
}

fn closed_forms(d: usize) -> (Poly, Poly) {
    let mut a_inf = zero(d);
    let mut b_inf = one(d); // k = 0 term of B
    let mut k = 1usize;
    loop {
        // A term: (-1)^{k-1} 2^k (1-X)^{k-1} X^{k^2} / (X;X)_{2k-1}
        if k * k > d { break; }
        let mut ta = scal(&xpow(d, k * k), 1i128 << k);
        for _ in 0..(k - 1) { ta = mul(&ta, &sub(&one(d), &xpow(d, 1))); }
        ta = mul(&ta, &inv(&qpoch(d, 2 * k - 1)));
        if k % 2 == 0 { ta = scal(&ta, -1); }
        a_inf = add(&a_inf, &ta);
        // B term: 2^k (X-1)^k X^{k^2+k} / (X;X)_{2k}
        if k * k + k <= d {
            let mut tb = scal(&xpow(d, k * k + k), 1i128 << k);
            for _ in 0..k { tb = mul(&tb, &sub(&xpow(d, 1), &one(d))); }
            tb = mul(&tb, &inv(&qpoch(d, 2 * k)));
            b_inf = add(&b_inf, &tb);
        }
        k += 1;
    }
    (a_inf, b_inf)
}

fn show(name: &str, p: &Poly, n: usize) {
    let s: Vec<String> = p.iter().take(n + 1).map(|c| c.to_string()).collect();
    println!("  {:<12} {}", name, s.join(", "));
}

fn main() {
    let mut fails = 0usize;

    // ---- [1] vs [2] at several working degrees
    for &d in &[12usize, 20, 30, 40, 56] {
        let ub = brute(d);
        let (uc, t) = chain(d);
        let mut bad = 0;
        for a in 0..=d {
            if !eqp(&ub[a], &uc[a]) { bad += 1; if bad <= 3 {
                println!("  MISMATCH D={} a={}", d, a); show("brute", &ub[a], 12); show("chain", &uc[a], 12); } }
        }
        println!("[1/2] D={:>3}  states 0..{:<3}  chain vs brute: {}",
                 d, d, if bad == 0 { "ALL EQUAL".to_string() } else { format!("{} MISMATCHES", bad) });
        if bad != 0 { fails += 1; }
        if d == 30 {
            show("u(0)", &ub[0], 16);
            show("u(1)", &ub[1], 16);
            show("u(2)", &ub[2], 16);
            show("T", &t, 16);
        }
    }

    // ---- [1] vs DFS walk enumeration (third, algebra-free opinion)
    for &d in &[8usize, 12, 14] {
        let ub = brute(d);
        let mut bad = 0;
        for a in 0..=4.min(d) {
            let w = dfs_walks(d, a);
            if !eqp(&ub[a], &w) { bad += 1; show("iter", &ub[a], 10); show("dfs ", &w, 10); }
        }
        println!("[1/DFS] D={:>3}  explicit walk enumeration from a=0..4: {}",
                 d, if bad == 0 { "ALL EQUAL" } else { "MISMATCH" });
        if bad != 0 { fails += 1; }
    }

    // ---- [3] structure of M_a: det = 1, N_a^2 = 0
    {
        let d = 40usize;
        let mut ok = true;
        for a in 1..=10 {
            // det( [[1+2X^{2a}, -2X^a],[2X^{3a}, 1-2X^{2a}]] )
            let m11 = add(&one(d), &scal(&xpow(d, 2 * a), 2));
            let m12 = scal(&xpow(d, a), -2);
            let m21 = scal(&xpow(d, 3 * a), 2);
            let m22 = sub(&one(d), &scal(&xpow(d, 2 * a), 2));
            let det = sub(&mul(&m11, &m22), &mul(&m12, &m21));
            if !eqp(&det, &one(d)) { ok = false; }
            // N_a = (M_a - I)/(2X^{2a}) = [[1, -X^{-a}],[X^a, -1]]; check N_a^2 = 0
            // clear the X^{-a}: work with D_a N_a D_a^{-1} = [[1,-1],[1,-1]] (D=diag(X^a,1))
            // (X^{-a} never materialises; the conjugated form is the fixed nilpotent)
            let f = [[1i64, -1], [1, -1]];
            let sq = [[f[0][0]*f[0][0]+f[0][1]*f[1][0], f[0][0]*f[0][1]+f[0][1]*f[1][1]],
                      [f[1][0]*f[0][0]+f[1][1]*f[1][0], f[1][0]*f[0][1]+f[1][1]*f[1][1]]];
            if sq != [[0i64,0],[0,0]] { ok = false; }
        }
        println!("[3] det M_a = 1 and N_a^2 = 0 for a=1..10: {}", if ok { "OK" } else { "FAIL" });
        if !ok { fails += 1; }
    }

    // ---- [4] homogeneous chain vs the predicted closed forms
    for &d in &[20usize, 36, 56, 72] {
        let (ha, hb) = homog(d);
        let (ca, cb) = closed_forms(d);
        let oka = eqp(&ha, &ca);
        let okb = eqp(&hb, &cb);
        println!("[4] D={:>3}  A_inf: {}   B_inf: {}", d,
                 if oka { "MATCH" } else { "MISMATCH" }, if okb { "MATCH" } else { "MISMATCH" });
        if !oka || !okb { fails += 1; show("chain A", &ha, 16); show("closed A", &ca, 16);
                          show("chain B", &hb, 16); show("closed B", &cb, 16); }
        if d == 36 { show("A_inf", &ha, 20); show("B_inf", &hb, 20); }
    }

    println!("\n{}", if fails == 0 { "ALL CHECKS PASS" } else { "SOME CHECKS FAILED" });
}
