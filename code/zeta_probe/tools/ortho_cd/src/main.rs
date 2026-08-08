// ortho_cd -- orbit growth of the right-corner orthoscheme reflection group, against the
// right-angled Coxeter envelope.  This is the certificate for paper 1b.
//
// WHAT IT SETTLES.  paper1b's Theorem "Class C faithfulness, all n >= 3, unconditional" argues:
// det Q_n = -prod a_i^2 is nonzero for EVERY positive tuple, so the form is nondegenerate, so
// by Tits' theorem rho_n is faithful, so u_d = [t^d] W_n(t) for all d.  The hypothesis of that
// chain does not mention the legs at all, so the conclusion would hold at EVERY positive tuple,
// including (1,...,1).  The paper's own collision-depth theorem says cd_n = 3 there.  Both
// cannot be true.  This program computes u_d directly and shows which one fails.
//
// GEOMETRY.  Orthoscheme O(a_1..a_n): V_0 = 0, V_k = V_{k-1} + a_k e_k.  The facet opposite V_j
// carries the reflection R_j:
//   R_0: hyperplane {x_1 = a_1},          normal e_1        (it contains V_1..V_n)
//   R_j: hyperplane through 0, normal  a_{j+1} e_j - a_j e_{j+1}   (1 <= j <= n-1)
//   R_n: hyperplane {x_n = 0},            normal e_n
// All rational, so exact arithmetic in F_p is faithful for a large prime (two primes are run).
//
// u_d is the number of chambers g.O at word distance d.  O is a fundamental domain, so this is
// the sphere size of the image group rho_n(W_n); we BFS the image group directly.
//
// ENVELOPE.  W_n(t) = (1+t)^{n+1} / J_{n+1}(t) with J_m = (1+t)(J_{m-1} - t J_{m-2}),
// J_0 = J_1 = 1 (the right-angled Coxeter group on the complement of the path P_{n+1}).
//
// Rule 8: BFS is capped by MAX_BALL and the depth is chosen so the ball stays in the low
// thousands; peak RSS is a few MB.

use std::collections::HashSet;

const MAX_BALL: usize = 3_000_000;

// ---------------------------------------------------------------- F_p

static mut P: u64 = 0;
#[inline]
fn p() -> u64 {
    unsafe { P }
}
#[inline]
fn add(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= p() { s - p() } else { s }
}
#[inline]
fn sub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a + p() - b }
}
#[inline]
fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % p() as u128) as u64
}
fn powm(a: u64, mut e: u64) -> u64 {
    let (mut r, mut b) = (1u64, a);
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, b);
        }
        b = mul(b, b);
        e >>= 1;
    }
    r
}
fn inv(a: u64) -> u64 {
    assert!(a != 0);
    powm(a, p() - 2)
}
fn fp(x: i64) -> u64 {
    let m = p() as i64;
    (((x % m) + m) % m) as u64
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for q in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % q == 0 { return n == q; }
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 { d /= 2; s += 1; }
    'o: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = { let (mut r, mut b, mut e) = (1u128, a as u128 % n as u128, d);
            while e > 0 { if e & 1 == 1 { r = r * b % n as u128; } b = b * b % n as u128; e >>= 1; }
            r as u64 };
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s - 1 {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n - 1 { continue 'o; }
        }
        return false;
    }
    true
}

// ---------------------------------------------------------------- affine maps in dim n

/// x |-> M x + t, stored row-major, dimension n.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Aff {
    n: usize,
    m: Vec<u64>,
    t: Vec<u64>,
}

fn ident(n: usize) -> Aff {
    let mut m = vec![0u64; n * n];
    for i in 0..n { m[i * n + i] = 1; }
    Aff { n, m, t: vec![0u64; n] }
}

/// f1 after f2
fn compose(f1: &Aff, f2: &Aff) -> Aff {
    let n = f1.n;
    let mut m = vec![0u64; n * n];
    for i in 0..n {
        for k in 0..n {
            let a = f1.m[i * n + k];
            if a == 0 { continue; }
            for j in 0..n {
                m[i * n + j] = add(m[i * n + j], mul(a, f2.m[k * n + j]));
            }
        }
    }
    let mut t = f1.t.clone();
    for i in 0..n {
        for k in 0..n {
            t[i] = add(t[i], mul(f1.m[i * n + k], f2.t[k]));
        }
    }
    Aff { n, m, t }
}

/// Reflection in {x : (x - pt).v = 0}, v not necessarily unit.
fn reflection(n: usize, pt: &[u64], v: &[u64]) -> Aff {
    let mut vv = 0u64;
    for i in 0..n { vv = add(vv, mul(v[i], v[i])); }
    assert!(vv != 0, "normal has zero length in F_p");
    let c = mul(2, inv(vv));
    let mut m = vec![0u64; n * n];
    for i in 0..n {
        for j in 0..n {
            let d = if i == j { 1u64 } else { 0u64 };
            m[i * n + j] = sub(d, mul(c, mul(v[i], v[j])));
        }
    }
    let mut pv = 0u64;
    for i in 0..n { pv = add(pv, mul(pt[i], v[i])); }
    let k = mul(c, pv);
    let t: Vec<u64> = (0..n).map(|i| mul(k, v[i])).collect();
    Aff { n, m, t }
}

/// The n+1 face reflections of the orthoscheme with legs a_1..a_n (given as rationals p/q).
fn ortho_gens(legs: &[(i64, i64)]) -> Vec<Aff> {
    let n = legs.len();
    let a: Vec<u64> = legs.iter().map(|&(x, y)| mul(fp(x), inv(fp(y)))).collect();
    let mut gens = Vec::new();
    // R_0: {x_1 = a_1}, normal e_1
    let mut pt = vec![0u64; n];
    pt[0] = a[0];
    let mut v = vec![0u64; n];
    v[0] = 1;
    gens.push(reflection(n, &pt, &v));
    // R_j, 1 <= j <= n-1: through 0, normal a_{j+1} e_j - a_j e_{j+1}   (1-indexed legs)
    for j in 1..n {
        let mut v = vec![0u64; n];
        v[j - 1] = a[j]; // a_{j+1} in 1-indexed = a[j] in 0-indexed
        v[j] = sub(0, a[j - 1]);
        gens.push(reflection(n, &vec![0u64; n], &v));
    }
    // R_n: {x_n = 0}, normal e_n
    let mut v = vec![0u64; n];
    v[n - 1] = 1;
    gens.push(reflection(n, &vec![0u64; n], &v));
    assert_eq!(gens.len(), n + 1);
    gens
}

fn spheres(gens: &[Aff], n: usize, depth: usize) -> Option<Vec<usize>> {
    let id = ident(n);
    let mut seen: HashSet<Aff> = HashSet::new();
    seen.insert(id.clone());
    let mut frontier = vec![id];
    let mut out = vec![1usize];
    for _ in 1..=depth {
        let mut next = Vec::new();
        for f in &frontier {
            for g in gens {
                let h = compose(f, g);
                if seen.insert(h.clone()) {
                    next.push(h);
                    if seen.len() > MAX_BALL { return None; }
                }
            }
        }
        out.push(next.len());
        frontier = next;
    }
    Some(out)
}

// ---------------------------------------------------------------- the RACG envelope

type Poly = Vec<i128>;
fn pmul(a: &Poly, b: &Poly) -> Poly {
    let mut c = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() { c[i + j] += x * y; }
    }
    c
}
fn psub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    (0..n).map(|i| a.get(i).copied().unwrap_or(0) - b.get(i).copied().unwrap_or(0)).collect()
}
/// coefficients of (1+t)^{n+1} / J_{n+1}(t)
fn envelope(n: usize, upto: usize) -> Vec<i128> {
    let one_pt: Poly = vec![1, 1];
    let t: Poly = vec![0, 1];
    let (mut a, mut b): (Poly, Poly) = (vec![1], vec![1]);
    for _ in 2..=(n + 1) {
        let nxt = pmul(&one_pt, &psub(&b, &pmul(&t, &a)));
        a = b;
        b = nxt;
    }
    let j = b;
    let mut num: Poly = vec![1];
    for _ in 0..(n + 1) { num = pmul(&num, &one_pt); }
    let mut out = vec![0i128; upto + 1];
    for i in 0..=upto {
        let mut acc = num.get(i).copied().unwrap_or(0);
        for k in 1..=i { acc -= j.get(k).copied().unwrap_or(0) * out[i - k]; }
        out[i] = acc;
    }
    out
}

fn e_t(legs: &[(i64, i64)]) -> (usize, usize) {
    let n = legs.len();
    let eq = |i: usize, j: usize| legs[i].0 * legs[j].1 == legs[j].0 * legs[i].1;
    let mut e = 0;
    if n >= 2 && eq(0, 1) { e += 1; }
    if n >= 2 && eq(n - 2, n - 1) { e += 1; }
    if n == 2 && eq(0, 1) { e = 1; }
    let mut t = 0;
    for i in 0..n.saturating_sub(2) {
        if eq(i, i + 1) && eq(i + 1, i + 2) { t += 1; }
    }
    (e, t)
}

fn run(label: &str, legs: &[(i64, i64)], depth: usize) {
    let n = legs.len();
    let gens = ortho_gens(legs);
    let env = envelope(n, depth);
    match spheres(&gens, n, depth) {
        None => println!("  {:22} n={}  BALL CAP HIT -- not verified", label, n),
        Some(sp) => {
            let cd = (1..=depth).find(|&d| (sp[d] as i128) < env[d]);
            let (e, t) = e_t(legs);
            let pred = if e == 0 && t == 0 { "inf".to_string() }
                       else if t >= 1 { "3".to_string() }
                       else { "4".to_string() };
            println!(
                "  {:22} n={} (e,t)=({},{})  u = {:?}",
                label, n, e, t, &sp[..=depth.min(7)]
            );
            println!(
                "  {:22}      envelope = {:?}",
                "", &env[..=depth.min(7)].iter().map(|&x| x as usize).collect::<Vec<_>>()
            );
            println!(
                "  {:22}      first deviation at d = {:?}   (e,t)-rule predicts cd = {})",
                "", cd, pred
            );
        }
    }
}

/// The three quartics, in the variables that actually occur.  The paper displays them with
/// X = a_i^2 and Z = a_{i+2}^2 and then calls them "empty over distinct-coordinate Q_{>0}^2",
/// which is FALSE for unrestricted X, Z: X^2 + 6XZ + Z^2 = k^2 has (X,Z,k) = (3,2,7).  The
/// statement is only correct when X and Z are themselves squares, i.e. as quartics in
/// (a_i, a_{i+2}).  This search confirms the restricted form has no nontrivial small solution.
fn quartic_search(bound: i64) {
    let is_sq = |v: i128| -> bool {
        if v < 0 { return false; }
        let mut r = (v as f64).sqrt() as i128;
        while r * r > v { r -= 1; }
        while (r + 1) * (r + 1) <= v { r += 1; }
        r * r == v
    };
    let forms: [(&str, i128, i128, i128); 3] = [
        ("V_1/4 : a^4 + 14 a^2 c^2 + c^4", 1, 14, 1),
        ("V_1/2 : a^4 +  6 a^2 c^2 + c^4", 1, 6, 1),
        ("V_3/4 : 9a^4 + 30 a^2 c^2 + 9c^4", 9, 30, 9),
    ];
    for (name, p2, q2, r2) in forms {
        let mut bad: Vec<(i64, i64)> = Vec::new();
        // in X, Z unrestricted (the paper's literal statement)
        let mut bad_xz: Vec<(i64, i64)> = Vec::new();
        for a in 1..=bound {
            for c in 1..=bound {
                if a == c { continue; }
                let (ai, ci) = (a as i128, c as i128);
                let v = p2 * ai * ai * ai * ai + q2 * ai * ai * ci * ci + r2 * ci * ci * ci * ci;
                if is_sq(v) && bad.len() < 4 { bad.push((a, c)); }
                let w = p2 * ai * ai + q2 * ai * ci + r2 * ci * ci;
                if is_sq(w) && bad_xz.len() < 4 { bad_xz.push((a, c)); }
            }
        }
        println!("  {}", name);
        println!("      as a quartic in (a,c), a != c, 1..{}: {}", bound,
                 if bad.is_empty() { "NO nontrivial solution".to_string() }
                 else { format!("SOLUTIONS {:?}", bad) });
        println!("      as a conic in (X,Z), X != Z, 1..{}: {}", bound,
                 if bad_xz.is_empty() { "none".to_string() }
                 else { format!("solutions {:?}  <-- the paper's literal claim fails here", bad_xz) });
    }
}

fn main() {
    println!("=== the three quartics ===");
    quartic_search(300);
    println!();

    for seed in [(1u64 << 61) - 1, 2_305_843_009_213_700_000] {
        let mut c = seed | 1;
        while !is_prime(c) { c += 2; }
        unsafe { P = c; }
        println!("=== p = {} ===", c);

        println!("\n[1] The internal contradiction: det Q_n != 0 at EVERY positive tuple, so the");
        println!("    faithfulness argument, which uses nothing else, would apply at (1,..,1) too.");
        run("n=3 legs (1,1,1)", &[(1, 1), (1, 1), (1, 1)], 6);
        run("n=4 legs (1,1,1,1)", &[(1, 1), (1, 1), (1, 1), (1, 1)], 6);

        println!("\n[2] The same argument run at n=2, where the answer is known independently.");
        run("n=2 legs (1,2)", &[(1, 1), (2, 1)], 12);

        println!("\n[3] Class C (pairwise distinct legs): the claim the paper actually wants.");
        run("n=3 legs (1,2,3)", &[(1, 1), (2, 1), (3, 1)], 10);
        run("n=4 legs (1,2,3,5)", &[(1, 1), (2, 1), (3, 1), (5, 1)], 8);

        println!("\n[4] The (e,t) rule on mixed tuples, including a NON-ADJACENT repeat.");
        run("n=4 legs (1,2,2,3)", &[(1, 1), (2, 1), (2, 1), (3, 1)], 8);
        run("n=4 legs (1,1,2,3)", &[(1, 1), (1, 1), (2, 1), (3, 1)], 8);
        run("n=5 legs (1,2,2,2,3)", &[(1, 1), (2, 1), (2, 1), (2, 1), (3, 1)], 7);
        // (1,2,1,3) is NOT Class C yet has no adjacent equal pair at all: the case the
        // (e,t)=(0,0) analysis has to cover and did not mention.
        run("n=4 legs (1,2,1,3)", &[(1, 1), (2, 1), (1, 1), (3, 1)], 8);
        println!();
    }
}
