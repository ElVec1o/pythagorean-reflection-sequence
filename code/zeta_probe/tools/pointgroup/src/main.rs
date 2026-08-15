// pointgroup -- orbit growth of the POINT GROUP of the right-corner orthoscheme, against the
// right-angled Coxeter envelope W_n.
//
// WHY THE POINT GROUP.  rho_a: W_n -> Isom(R^n) factors through the linear part
// pi: Isom(R^n) -> O(n).  If pi o rho_a is injective then rho_a is injective, so a faithful
// point group settles the generic form of the faithfulness problem, the ambient embedding
// problem (W_n <= O(n) directly), and finite presentation, all at once.  The converse fails:
// rho_a can be faithful while the point group is not, so a deviation here is NOT a deviation
// of rho_a.  This tool measures the point group only.
//
// GEOMETRY.  Orthoscheme O(a_1..a_n): normals m_0 = e_1, m_j = a_{j+1} e_j - a_j e_{j+1}
// (1 <= j <= n-1), m_n = e_n.  R_k = I - 2 m_k m_k^T / (m_k . m_k), all rational, so
// arithmetic in F_p is exact for rational legs.  Reduction mod p can only IDENTIFY elements
// that are already equal in characteristic zero, or collide mod p, so a printed sphere count
// is a LOWER bound for the characteristic-zero count.  The envelope is an UPPER bound.  When
// the two agree the count is exact.  Two independent primes are run and must agree.
//
// ENVELOPE.  W_n(t) = (1+t)^{floor(n/2)+1} / K_{n+1}(t), K_0 = K_1 = 1,
// K_{2j} = K_{2j-1} - t K_{2j-2},  K_{2j+1} = (1+t) K_{2j} - t K_{2j-1}.
//
// USAGE  pointgroup <legs, comma separated> <max depth> [max ball]
// Rule 8: run under ../runcap.sh.  Progress is printed per depth with elapsed time.

use std::collections::HashSet;
use std::time::Instant;

const P1: u128 = (1u128 << 61) - 1; // Mersenne primes, both > 2^60
const P2: u128 = (1u128 << 62) - 57;

fn mulmod(a: u64, b: u64, p: u128) -> u64 {
    ((a as u128 * b as u128) % p) as u64
}
fn addmod(a: u64, b: u64, p: u128) -> u64 {
    let s = a as u128 + b as u128;
    (if s >= p { s - p } else { s }) as u64
}
fn submod(a: u64, b: u64, p: u128) -> u64 {
    if a >= b { a - b } else { ((a as u128 + p) - b as u128) as u64 }
}
fn powmod(mut a: u64, mut e: u64, p: u128) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 { r = mulmod(r, a, p); }
        a = mulmod(a, a, p);
        e >>= 1;
    }
    r
}
fn invmod(a: u64, p: u128) -> u64 { powmod(a, (p - 2) as u64, p) }

fn imod(v: i64, p: u128) -> u64 {
    let m = p as i128;
    (((v as i128 % m) + m) % m) as u64
}

/// Reflection matrices of the orthoscheme point group, over F_p, row-major n x n.
fn generators(legs: &[i64], p: u128) -> Vec<Vec<u64>> {
    let n = legs.len();
    let mut normals: Vec<Vec<i64>> = Vec::new();
    let mut m0 = vec![0i64; n]; m0[0] = 1; normals.push(m0);
    for j in 1..n {
        let mut v = vec![0i64; n];
        v[j - 1] = legs[j];
        v[j] = -legs[j - 1];
        normals.push(v);
    }
    let mut mn = vec![0i64; n]; mn[n - 1] = 1; normals.push(mn);

    normals.iter().map(|m| {
        let d: i64 = m.iter().map(|x| x * x).sum();
        let dinv = invmod(imod(d, p), p);
        let two = imod(2, p);
        let mut mat = vec![0u64; n * n];
        for i in 0..n {
            for j in 0..n {
                let ident = if i == j { imod(1, p) } else { 0 };
                let mm = mulmod(imod(m[i], p), imod(m[j], p), p);
                let corr = mulmod(mulmod(two, mm, p), dinv, p);
                mat[i * n + j] = submod(ident, corr, p);
            }
        }
        mat
    }).collect()
}

fn matmul(a: &[u64], b: &[u64], n: usize, p: u128) -> Vec<u64> {
    let mut c = vec![0u64; n * n];
    for i in 0..n {
        for k in 0..n {
            let aik = a[i * n + k];
            if aik == 0 { continue; }
            for j in 0..n {
                c[i * n + j] = addmod(c[i * n + j], mulmod(aik, b[k * n + j], p), p);
            }
        }
    }
    c
}

/// 128-bit fingerprint of a matrix; two independent multiplicative hashes.
fn fingerprint(m: &[u64]) -> u128 {
    let mut h1: u64 = 0x9e3779b97f4a7c15;
    let mut h2: u64 = 0xff51afd7ed558ccd;
    for &x in m {
        h1 = h1.wrapping_add(x).wrapping_mul(0x9e3779b97f4a7c15);
        h1 ^= h1 >> 29;
        h2 = (h2 ^ x).wrapping_mul(0xc4ceb9fe1a85ec53);
        h2 ^= h2 >> 31;
    }
    ((h1 as u128) << 64) | (h2 as u128)
}

/// Sphere sizes of the right-angled Coxeter envelope W_n, as exact integers (i128 is ample).
fn envelope(n: usize, d_max: usize) -> Vec<i128> {
    // K polynomials, coefficient vectors
    let mut k: Vec<Vec<i128>> = vec![vec![1], vec![1]];
    for m in 2..=(n + 1) {
        let prev = k[m - 1].clone();
        let prev2 = k[m - 2].clone();
        let mut out;
        if m % 2 == 0 {
            out = prev.clone();
        } else {
            // (1+t) * prev
            out = vec![0i128; prev.len() + 1];
            for (i, c) in prev.iter().enumerate() { out[i] += c; out[i + 1] += c; }
        }
        // subtract t * prev2
        if out.len() < prev2.len() + 1 { out.resize(prev2.len() + 1, 0); }
        for (i, c) in prev2.iter().enumerate() { out[i + 1] -= c; }
        k.push(out);
    }
    let den = k[n + 1].clone();
    // numerator (1+t)^{floor(n/2)+1}
    let mut num: Vec<i128> = vec![1];
    for _ in 0..(n / 2 + 1) {
        let mut o = vec![0i128; num.len() + 1];
        for (i, c) in num.iter().enumerate() { o[i] += c; o[i + 1] += c; }
        num = o;
    }
    let mut s = vec![0i128; d_max + 1];
    for d in 0..=d_max {
        let mut c = if d < num.len() { num[d] } else { 0 };
        for j in 1..=d {
            if j < den.len() { c -= den[j] * s[d - j]; }
        }
        s[d] = c / den[0];
    }
    s
}

/// Bytes this search will hold once the ball has `ball` elements and the frontier `front`
/// elements: the frontier is a flat Vec of n*n u64, and `seen` is a hash set of u128 whose
/// table costs about 19 bytes per entry at the default load factor.
fn projected_bytes(n: usize, ball: usize, front: usize) -> u64 {
    (front as u64) * (n * n * 8) as u64 + (ball as u64) * 19
}

fn run(legs: &[i64], d_max: usize, max_ball: usize, budget_mb: u64, p: u128, env: &[i128])
    -> (Option<usize>, usize) {
    let n = legs.len();
    let sq = n * n;
    let gens = generators(legs, p);
    let mut ident = vec![0u64; sq];
    for i in 0..n { ident[i * n + i] = imod(1, p); }

    let mut seen: HashSet<u128> = HashSet::new();
    seen.insert(fingerprint(&ident));
    // Frontier stored FLAT: element k occupies front[k*sq .. (k+1)*sq].
    let mut front: Vec<u64> = ident.clone();
    let t0 = Instant::now();
    let budget = budget_mb * 1024 * 1024;
    let mut reached = 0usize;

    for d in 1..=d_max {
        // Rule 8 pre-flight, per depth: refuse to expand if the projection exceeds the budget.
        let n_front = front.len() / sq;
        let proj_front = n_front * gens.len();
        let proj_ball = seen.len() + proj_front;
        let proj = projected_bytes(n, proj_ball, proj_front);
        if proj > budget {
            println!("  depth {} would need about {} MB, budget is {} MB: stopping before expansion.",
                     d, proj / (1024 * 1024), budget_mb);
            return (None, reached);
        }
        let mut next: Vec<u64> = Vec::with_capacity(proj_front * sq);
        for k in 0..n_front {
            let x = &front[k * sq..(k + 1) * sq];
            for g in &gens {
                let y = matmul(x, g, n, p);
                let f = fingerprint(&y);
                if seen.insert(f) { next.extend_from_slice(&y); }
            }
        }
        front = next;
        front.shrink_to_fit();
        let got = (front.len() / sq) as i128;
        reached = d;
        let want = env[d];
        let ok = got == want;
        println!(
            "  d={:2}  point-group sphere {:>12}   envelope {:>12}   {}   [{:.1}s, ball {}]",
            d, got, want,
            if ok { "MATCH".to_string() } else { format!("DEVIATES by {}", want - got) },
            t0.elapsed().as_secs_f64(), seen.len()
        );
        if !ok { return (Some(d), reached); }
        if seen.len() > max_ball {
            println!("  ball cap {} reached at depth {}, stopping", max_ball, d);
            return (None, reached);
        }
    }
    (None, reached)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: pointgroup <legs,comma-separated> <max depth> [max ball]");
        std::process::exit(2);
    }
    let legs: Vec<i64> = args[1].split(',').map(|s| s.trim().parse().unwrap()).collect();
    let d_max: usize = args[2].parse().unwrap();
    let max_ball: usize = if args.len() > 3 { args[3].parse().unwrap() } else { 60_000_000 };
    // Rule 8: conservative default. This machine has 24 GB with swap routinely near full,
    // so the guard is what keeps the search inside resident memory, not the ball cap.
    let budget_mb: u64 = if args.len() > 4 { args[4].parse().unwrap() } else { 2500 };
    let n = legs.len();

    // Class C check: no endpoint equal pair, no three consecutive equal legs.
    let e = (legs[0] == legs[1]) || (legs[n - 2] == legs[n - 1]);
    let t = (0..n.saturating_sub(2)).any(|i| legs[i] == legs[i + 1] && legs[i + 1] == legs[i + 2]);
    let env = envelope(n, d_max);

    println!("n = {}, legs = {:?}, Class C = {} (e = {}, t = {})", n, legs, !e && !t, e, t);
    println!("envelope spheres: {:?}", &env[..=d_max.min(12)]);

    let mut first: Vec<Option<usize>> = Vec::new();
    let mut depths: Vec<usize> = Vec::new();
    for (tag, p) in [("p1", P1), ("p2", P2)] {
        println!("--- prime {} = {} ---", tag, p);
        let (dev, reached) = run(&legs, d_max, max_ball, budget_mb, p, &env);
        first.push(dev); depths.push(reached);
    }
    if first[0] != first[1] {
        println!("PRIME DISAGREEMENT {:?} vs {:?} -- result not trusted", first[0], first[1]);
        std::process::exit(1);
    }
    match first[0] {
        None => {
            let reached = depths.iter().copied().min().unwrap_or(0);
            println!("\nRESULT: point group matches the envelope through depth {} at both primes.\n\
                      Hence the point group representation of W_{} is injective on the ball of\n\
                      radius {}, so cd(point group) > {}.", reached, n, reached, reached)
        }
        Some(d) => println!("\nRESULT: point group first deviates at depth {} at both primes.", d),
    }
}
