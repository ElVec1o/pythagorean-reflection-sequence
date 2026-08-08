// racg_envelope -- certification of Theorem "the RACG envelope is rational" (paper3).
//
// The paper displays
//     W_n(t) = (1+t)^{floor(n/2)+1} / N_n(t),   N_n(t) = (1+t)^{n+1} c_{Gamma_n}(-1/(1+t))
// and asserts the growth rate is "1 plus the spectral radius 2cos(2pi/(n+3)) of the path
// P_{n+1}".  Two things are checked here:
//
//   (A) the displayed N_n is WRONG -- Steinberg's formula for a RACG reads
//           1/W_Gamma(t) = c_Gamma(-t/(1+t)),
//       with argument -t/(1+t), not -1/(1+t).  We evaluate both and print the disagreement.
//   (B) the spectral claim is WRONG -- the spectral radius of the path P_{n+1} is
//       2cos(pi/(n+2)), which is not 2cos(2pi/(n+3)).  We print both.
//
// and the corrected statement is certified:
//
//       W_n(t) = (1+t)^{n+1} / J_{n+1}(t),      J_m = (1+t)(J_{m-1} - t J_{m-2}),  J_0=J_1=1
//       J_m    = (1+t)^{floor(m/2)} K_m         (exact division, asserted)
//       W_n(t) = (1+t)^{floor(n/2)+1} / K_{n+1}
//       smallest positive root of K_{n+1} is 1/(1 + 2cos(2pi/(n+3)))    ==>  r_n
//
// plus a fully independent check of the coefficients: BFS of the Coxeter group in its
// Tits (canonical geometric) representation, which has INTEGER matrices here because the
// bilinear form takes values 1, 0, -1 only.  Sphere sizes are compared against the series.
//
// Rule 8: every loop below is bounded by an explicit constant; MAX_ELEMENTS caps the BFS
// and the program aborts cleanly rather than growing.  Peak memory is a few tens of MB.

use std::collections::HashSet;

const MAX_ELEMENTS: usize = 400_000; // hard cap on stored group elements (Rule 8)
const NMAX: usize = 30; // largest dimension for the polynomial certification

// ---------------------------------------------------------------- exact integer polynomials

type Poly = Vec<i128>; // coefficient i is the coefficient of t^i

fn p_trim(mut a: Poly) -> Poly {
    while a.len() > 1 && *a.last().unwrap() == 0 {
        a.pop();
    }
    a
}

fn p_add(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut c = vec![0i128; n];
    for i in 0..n {
        c[i] = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0);
    }
    p_trim(c)
}

fn p_sub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut c = vec![0i128; n];
    for i in 0..n {
        c[i] = a.get(i).copied().unwrap_or(0) - b.get(i).copied().unwrap_or(0);
    }
    p_trim(c)
}

fn p_mul(a: &Poly, b: &Poly) -> Poly {
    let mut c = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            c[i + j] += x * y;
        }
    }
    p_trim(c)
}

/// Exact division by (1+t); panics if the division is not exact.
fn p_div_1pt(a: &Poly) -> Poly {
    // synthetic division by (t + 1), i.e. evaluate the quotient by Horner from the top
    let n = a.len();
    let mut q = vec![0i128; n - 1];
    let mut carry = 0i128;
    for i in (1..n).rev() {
        let c = a[i] - carry;
        q[i - 1] = c;
        carry = c;
    }
    assert_eq!(a[0] - carry, 0, "division by (1+t) was not exact");
    p_trim(q)
}

fn p_eval_f64(a: &Poly, x: f64) -> f64 {
    let mut s = 0.0;
    for &c in a.iter().rev() {
        s = s * x + c as f64;
    }
    s
}

fn p_show(a: &Poly) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (i, &c) in a.iter().enumerate() {
        if c == 0 {
            continue;
        }
        let sign = if c < 0 { "-" } else { "+" };
        let m = c.abs();
        let term = match (i, m) {
            (0, _) => format!("{}", m),
            (1, 1) => "t".to_string(),
            (1, _) => format!("{}t", m),
            (_, 1) => format!("t^{}", i),
            _ => format!("{}t^{}", m, i),
        };
        if parts.is_empty() && sign == "+" {
            parts.push(term);
        } else {
            parts.push(format!("{} {}", sign, term));
        }
    }
    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" ")
    }
}

// ---------------------------------------------------------------- the two envelope routes

/// Independent-set (= clique of the complement) polynomial of the path on m vertices.
/// I_m = I_{m-1} + x I_{m-2}, I_0 = 1, I_1 = 1 + x.  Coefficient k counts independent
/// sets of size k, which are exactly the cliques of Gamma_n.
fn indep_poly(m: usize) -> Poly {
    let mut prev: Poly = vec![1];
    if m == 0 {
        return prev;
    }
    let mut cur: Poly = vec![1, 1];
    for _ in 2..=m {
        let nxt = p_add(&cur, &p_mul(&vec![0, 1], &prev));
        prev = cur;
        cur = nxt;
    }
    cur
}

/// J_m via the recurrence J_m = (1+t)(J_{m-1} - t J_{m-2}), J_0 = J_1 = 1.
fn j_recurrence(m: usize) -> Poly {
    let one_pt: Poly = vec![1, 1];
    let t: Poly = vec![0, 1];
    let mut a: Poly = vec![1]; // J_0
    let mut b: Poly = vec![1]; // J_1
    if m == 0 {
        return a;
    }
    for _ in 2..=m {
        let nxt = p_mul(&one_pt, &p_sub(&b, &p_mul(&t, &a)));
        a = b;
        b = nxt;
    }
    b
}

/// J_m built directly from Steinberg: (1+t)^m * c_Gamma(-t/(1+t))
///   = sum_k a_k (-t)^k (1+t)^{m-k},  a_k = #cliques of size k.
fn j_steinberg(m: usize) -> Poly {
    let c = indep_poly(m);
    let one_pt: Poly = vec![1, 1];
    let mut total: Poly = vec![0];
    for (k, &a_k) in c.iter().enumerate() {
        if a_k == 0 || k > m {
            continue;
        }
        // (-t)^k
        let mut term = vec![0i128; k + 1];
        term[k] = if k % 2 == 0 { a_k } else { -a_k };
        for _ in 0..(m - k) {
            term = p_mul(&term, &one_pt);
        }
        total = p_add(&total, &term);
    }
    total
}

/// The paper's DISPLAYED denominator: (1+t)^{n+1} c_Gamma(-1/(1+t)).
/// Kept so the disagreement is exhibited rather than merely asserted.
fn j_paper_displayed(m: usize) -> Poly {
    let c = indep_poly(m);
    let one_pt: Poly = vec![1, 1];
    let mut total: Poly = vec![0];
    for (k, &a_k) in c.iter().enumerate() {
        if a_k == 0 || k > m {
            continue;
        }
        // (-1)^k * (1+t)^{m-k}
        let mut term: Poly = vec![if k % 2 == 0 { a_k } else { -a_k }];
        for _ in 0..(m - k) {
            term = p_mul(&term, &one_pt);
        }
        total = p_add(&total, &term);
    }
    total
}

/// Smallest root in (0, 1) by sign-change scan + bisection.
fn smallest_positive_root(p: &Poly) -> Option<f64> {
    let steps = 2_000_000usize; // bounded
    let hi = 1.0f64;
    let mut prev_x = 1e-12;
    let mut prev_v = p_eval_f64(p, prev_x);
    for i in 1..=steps {
        let x = hi * (i as f64) / (steps as f64);
        let v = p_eval_f64(p, x);
        if prev_v == 0.0 {
            return Some(prev_x);
        }
        if (prev_v < 0.0) != (v < 0.0) {
            let (mut lo, mut hh) = (prev_x, x);
            for _ in 0..200 {
                let mid = 0.5 * (lo + hh);
                if (p_eval_f64(p, lo) < 0.0) != (p_eval_f64(p, mid) < 0.0) {
                    hh = mid;
                } else {
                    lo = mid;
                }
            }
            return Some(0.5 * (lo + hh));
        }
        prev_x = x;
        prev_v = v;
    }
    None
}

// ---------------------------------------------------------------- Tits representation BFS

/// Canonical geometric representation of the RACG on Gamma_n.
/// Basis e_0..e_n; B(e_i,e_i) = 1; B(e_i,e_j) = 0 if |i-j| >= 2 (an edge of Gamma_n,
/// so the generators commute); B(e_i,e_j) = -1 if |i-j| = 1 (no edge, infinite bond).
/// s_i(e_j) = e_j - 2 B(e_i,e_j) e_i, hence integer matrices.
/// Tits' theorem: this representation is faithful, so BFS distance = Coxeter length.
fn gen_matrix(n: usize, i: usize) -> Vec<i64> {
    let d = n + 1;
    let mut m = vec![0i64; d * d];
    // column j holds the image of e_j
    for j in 0..d {
        let b: i64 = if i == j {
            1
        } else if i.abs_diff(j) == 1 {
            -1
        } else {
            0
        };
        // s_i(e_j) = e_j - 2 b e_i
        m[j * d + j] += 1;
        m[j * d + i] -= 2 * b;
    }
    m
}

fn mat_mul(a: &[i64], b: &[i64], d: usize) -> Option<Vec<i64>> {
    let mut c = vec![0i64; d * d];
    for i in 0..d {
        for k in 0..d {
            let x = a[i * d + k];
            if x == 0 {
                continue;
            }
            for j in 0..d {
                let prod = x.checked_mul(b[k * d + j])?;
                c[i * d + j] = c[i * d + j].checked_add(prod)?;
            }
        }
    }
    Some(c)
}

/// Sphere sizes of the RACG up to `depth`, by BFS in the faithful Tits representation.
/// Returns None if the element cap or an integer overflow is hit (reported, not ignored).
fn bfs_spheres(n: usize, depth: usize) -> Option<Vec<usize>> {
    let d = n + 1;
    let gens: Vec<Vec<i64>> = (0..d).map(|i| gen_matrix(n, i)).collect();
    let mut ident = vec![0i64; d * d];
    for i in 0..d {
        ident[i * d + i] = 1;
    }
    let mut seen: HashSet<Vec<i64>> = HashSet::new();
    seen.insert(ident.clone());
    let mut frontier = vec![ident];
    let mut spheres = vec![1usize];
    for _ in 1..=depth {
        let mut next: Vec<Vec<i64>> = Vec::new();
        for g in &frontier {
            for s in &gens {
                let h = mat_mul(g, s, d)?;
                if seen.insert(h.clone()) {
                    next.push(h);
                    if seen.len() > MAX_ELEMENTS {
                        return None; // Rule 8: abort cleanly at the cap
                    }
                }
            }
        }
        spheres.push(next.len());
        frontier = next;
    }
    Some(spheres)
}

/// Series coefficients of (1+t)^{num_pow} / K(t), by long division.
fn series_coeffs(num_pow: usize, k: &Poly, upto: usize) -> Vec<i128> {
    let mut num: Poly = vec![1];
    for _ in 0..num_pow {
        num = p_mul(&num, &vec![1, 1]);
    }
    let mut out = vec![0i128; upto + 1];
    for i in 0..=upto {
        let mut acc = num.get(i).copied().unwrap_or(0);
        for j in 1..=i {
            acc -= k.get(j).copied().unwrap_or(0) * out[i - j];
        }
        assert_eq!(k[0], 1, "constant term of K must be 1");
        out[i] = acc;
    }
    out
}

fn main() {
    println!("=== paper3 Theorem (RACG envelope): certification ===\n");

    // ---- Part A: the displayed formula versus Steinberg's ----
    println!("[A] The displayed denominator N_n(t) = (1+t)^(n+1) c(-1/(1+t)) vs Steinberg's");
    println!("    correct c(-t/(1+t)).  n = 2, 3:");
    for n in 2..=3usize {
        let good = j_steinberg(n + 1);
        let bad = j_paper_displayed(n + 1);
        println!("    n={}:  correct J_(n+1) = {}", n, p_show(&good));
        println!("           displayed N_n   = {}", p_show(&bad));
        println!(
            "           equal? {}",
            if good == bad { "YES" } else { "NO  <-- displayed formula is wrong" }
        );
    }
    println!();

    // ---- Part B: the spectral claim ----
    println!("[B] Claimed: r_n - 1 = 2cos(2pi/(n+3)) is 'the spectral radius of the path P_(n+1)'.");
    println!("    Spectral radius of P_(n+1) is 2cos(pi/(n+2)).  Compare:");
    for n in 2..=7usize {
        let claimed = 2.0 * (2.0 * std::f64::consts::PI / (n as f64 + 3.0)).cos();
        let path_sr = 2.0 * (std::f64::consts::PI / (n as f64 + 2.0)).cos();
        println!(
            "    n={}:  2cos(2pi/(n+3)) = {:.6}   spec.rad. P_(n+1) = 2cos(pi/(n+2)) = {:.6}   {}",
            n,
            claimed,
            path_sr,
            if (claimed - path_sr).abs() < 1e-9 { "equal" } else { "DIFFERENT" }
        );
    }
    println!();

    // ---- Part C: corrected statement, certified ----
    println!("[C] Corrected envelope, n = 2..{}:", NMAX);
    println!("    J_m by recurrence == J_m by Steinberg;  J_(n+1) = (1+t)^floor((n+1)/2) K_(n+1);");
    println!("    r_n = 1/(smallest positive root of K_(n+1)) == 1 + 2cos(2pi/(n+3)).\n");
    let mut all_ok = true;
    for n in 2..=NMAX {
        let m = n + 1;
        let j_rec = j_recurrence(m);
        let j_st = j_steinberg(m);
        assert_eq!(j_rec, j_st, "recurrence and Steinberg disagree at n={}", n);

        // strip (1+t)^{floor(m/2)}
        let mut k = j_rec.clone();
        for _ in 0..(m / 2) {
            k = p_div_1pt(&k);
        }
        // K must not be divisible by (1+t) any more: K(-1) != 0
        let at_minus1 = p_eval_f64(&k, -1.0);
        assert!(at_minus1.abs() > 0.5, "K still divisible by (1+t) at n={}", n);

        let root = smallest_positive_root(&k).expect("no root found in (0,1)");
        let r_num = 1.0 / root;
        let r_cf = 1.0 + 2.0 * (2.0 * std::f64::consts::PI / (n as f64 + 3.0)).cos();
        let ok = (r_num - r_cf).abs() < 1e-9;
        all_ok &= ok;
        if n <= 7 {
            println!(
                "    n={:2}: W_n(t) = (1+t)^{} / [{}]",
                n,
                n / 2 + 1,
                p_show(&k)
            );
        }
        println!(
            "    n={:2}: r_n(root) = {:.12}   1+2cos(2pi/(n+3)) = {:.12}   {}",
            n,
            r_num,
            r_cf,
            if ok { "OK" } else { "MISMATCH" }
        );
    }
    println!("\n    all n: {}", if all_ok { "ALL OK" } else { "FAILURES PRESENT" });

    // ---- Part D: independent coefficient check by faithful-representation BFS ----
    println!("\n[D] Independent check: BFS in the Tits (faithful) representation vs the series.");
    println!("    cap MAX_ELEMENTS = {}", MAX_ELEMENTS);
    for n in 2..=6usize {
        let m = n + 1;
        let mut k = j_recurrence(m);
        for _ in 0..(m / 2) {
            k = p_div_1pt(&k);
        }
        let depth = match n {
            2 => 14,
            3 => 12,
            4 => 11,
            5 => 10,
            6 => 9,
            _ => 8,
        };
        match bfs_spheres(n, depth) {
            None => println!("    n={}: BFS hit the element cap or overflowed -- NOT VERIFIED", n),
            Some(sph) => {
                let ser = series_coeffs(n / 2 + 1, &k, depth);
                let agree = (0..=depth).all(|d| sph[d] as i128 == ser[d]);
                println!(
                    "    n={}: depth {:2}  BFS {:?}",
                    n,
                    depth,
                    &sph[..=depth.min(8)]
                );
                println!(
                    "           series {:?}   {}",
                    &ser[..=depth.min(8)],
                    if agree { "AGREE to full depth" } else { "DISAGREE" }
                );
                assert!(agree, "series does not match the group at n={}", n);
            }
        }
    }

    // ---- Part F: each row of the paper's table, against the computed denominator ----
    // A necessary condition that needs no theory: [t^1] W_n(t) must be n+1, the number of
    // generators.  Any tabulated denominator failing this is wrong on its face.
    println!("\n[F] The paper's tabulated rows, checked against the computed K_(n+1)");
    println!("    and against [t^1] W_n = n+1 (the generator count).");
    let table: Vec<(usize, Poly)> = vec![
        (2, vec![1, -1, -1]),
        (3, vec![1, -2]),
        (4, vec![1, -2, -1, 1]),
        (5, vec![1, -3, 1, 1]),
        (6, vec![1, -3, 0, 3]),
        (7, vec![1, -2, -3, 4, -1]),
    ];
    for (n, paper_k) in &table {
        let m = n + 1;
        let mut k = j_recurrence(m);
        for _ in 0..(m / 2) {
            k = p_div_1pt(&k);
        }
        let num_pow = n / 2 + 1;
        // [t^1] of (1+t)^num_pow / K  is  num_pow - K_1
        let s1_paper = num_pow as i128 - paper_k.get(1).copied().unwrap_or(0);
        let s1_ours = num_pow as i128 - k.get(1).copied().unwrap_or(0);
        let same = &k == paper_k;
        println!(
            "    n={}: paper [{}]  computed [{}]  {}",
            n,
            p_show(paper_k),
            p_show(&k),
            if same { "identical" } else { "DIFFER" }
        );
        println!(
            "           [t^1] from paper row = {}, from computed = {}, generators = {}   {}",
            s1_paper,
            s1_ours,
            n + 1,
            if s1_paper == (*n as i128 + 1) { "row ok" } else { "ROW IS WRONG" }
        );
    }

    // ---- Part E: the planar corollary ----
    println!("\n[E] Planar case n=2: is [t^d] W_2(t) = F_(d+3) for all d <= 9?");
    let mut k2 = j_recurrence(3);
    k2 = p_div_1pt(&k2);
    let ser = series_coeffs(2, &k2, 9);
    let mut fib = vec![0i128, 1]; // F_0 = 0, F_1 = 1
    for i in 2..=13usize {
        let x = fib[i - 1] + fib[i - 2];
        fib.push(x);
    }
    for d in 0..=9usize {
        let f = fib[d + 3];
        println!(
            "    d={}: [t^d]W_2 = {:3}   F_(d+3) = {:3}   {}",
            d,
            ser[d],
            f,
            if ser[d] == f { "match" } else { "MISMATCH <-- claim fails here" }
        );
    }
}
