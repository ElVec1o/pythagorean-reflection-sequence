// qcos_rank -- exclusion sweeps for the zero curve of the Hahn-Exton q-cosine.
//
// Regenerates every rank exclusion quoted in rem:zerocurve-arith of
// paper/journal/hahn_exton_qcosine.tex: the algebraic-relation exclusion (a),
// the holonomy exclusion (h), and the Mahler / system / difference-differential /
// quasi-modular / log-linear battery (i).
//
// Object.  u_1(q) = z_1(q) is the least positive zero of
//     G(q,z) = sum_{k>=0} (-1)^k q^{k(k-1)} z^k / (q;q)_{2k},
// an element of 1 + q Z[[q]] (thm:integrality).  It is obtained here by Newton
// iteration inside F_p[[q]], which reproduces the integer coefficients reduced
// mod p exactly: every step is a ring operation and the only inverse taken is of
// a series with constant term -1.  The Newton residual is asserted to vanish
// identically to the working order before any rank is computed.
//
// Method, and what a full-rank verdict proves.  Each exclusion asks whether a
// fixed finite family of series (monomials in u_1 and its transforms, times
// powers of q) is linearly dependent over the constants.  That is a rank question
// on an integer matrix.  Any relation may be scaled to a primitive integer one,
// which survives reduction mod p; hence FULL COLUMN RANK MOD p IMPLIES FULL
// COLUMN RANK OVER Q, and a full-rank verdict is a proof of non-existence, not
// evidence.  Two distinct primes are used, per Rule 7; a disagreement is a bug.
//
// Usage:  qcos_rank [ORDER]        (default 4000)
// Rule 8: run under code/zeta_probe/tools/runcap.sh with a 14000 MB cap.

use std::time::Instant;

const P1: u64 = 2_147_483_647; // 2^31 - 1
const P2: u64 = 2_147_483_629;

#[inline(always)]
fn addm(a: u64, b: u64, p: u64) -> u64 {
    let s = a + b;
    if s >= p {
        s - p
    } else {
        s
    }
}
#[inline(always)]
fn subm(a: u64, b: u64, p: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a + p - b
    }
}
#[inline(always)]
fn mulm(a: u64, b: u64, p: u64) -> u64 {
    (a * b) % p
}
fn powm(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1u64;
    a %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = mulm(r, a, p);
        }
        a = mulm(a, a, p);
        e >>= 1;
    }
    r
}
#[inline(always)]
fn invm(a: u64, p: u64) -> u64 {
    powm(a, p - 2, p)
}

// ---------------------------------------------------------------- series ----

type S = Vec<u64>;

fn zero(n: usize) -> S {
    vec![0u64; n]
}
fn one(n: usize, p: u64) -> S {
    let mut a = zero(n);
    a[0] = 1 % p;
    a
}
fn trunc(a: &S, n: usize) -> S {
    let mut b = zero(n);
    let m = a.len().min(n);
    b[..m].copy_from_slice(&a[..m]);
    b
}

fn mul(a: &S, b: &S, n: usize, p: u64) -> S {
    let mut c = vec![0u64; n];
    for i in 0..a.len().min(n) {
        let ai = a[i];
        if ai == 0 {
            continue;
        }
        let hi = (n - i).min(b.len());
        for j in 0..hi {
            let bj = b[j];
            if bj != 0 {
                c[i + j] = (c[i + j] + ai * bj) % p;
            }
        }
    }
    c
}

fn addv(a: &S, b: &S, p: u64) -> S {
    (0..a.len()).map(|i| addm(a[i], b[i], p)).collect()
}
fn subv(a: &S, b: &S, p: u64) -> S {
    (0..a.len()).map(|i| subm(a[i], b[i], p)).collect()
}
fn scal(a: &S, c: u64, p: u64) -> S {
    a.iter().map(|&x| mulm(x, c, p)).collect()
}

// 1/a, for a with invertible constant term.
fn inv(a: &S, n: usize, p: u64) -> S {
    let mut c = zero(n);
    let a0i = invm(a[0], p);
    c[0] = a0i;
    for k in 1..n {
        let mut acc = 0u64;
        let hi = k.min(a.len() - 1);
        for i in 1..=hi {
            if a[i] != 0 {
                acc = (acc + a[i] * c[k - i]) % p;
            }
        }
        c[k] = mulm(subm(0, acc, p), a0i, p);
    }
    c
}

fn deriv(a: &S, p: u64) -> S {
    let n = a.len();
    let mut c = zero(n);
    for k in 1..n {
        c[k - 1] = mulm(a[k], (k as u64) % p, p);
    }
    c
}
// theta = q d/dq
fn theta(a: &S, p: u64) -> S {
    let n = a.len();
    let mut c = zero(n);
    for k in 0..n {
        c[k] = mulm(a[k], (k as u64) % p, p);
    }
    c
}
// f(q^d)
fn subst_pow(a: &S, d: usize, n: usize) -> S {
    let mut c = zero(n);
    let mut k = 0usize;
    while k * d < n && k < a.len() {
        c[k * d] = a[k];
        k += 1;
    }
    c
}
// log f for f in 1 + q F_p[[q]]  (p > n is required and holds).
fn log_series(a: &S, n: usize, p: u64) -> S {
    let r = mul(&deriv(a, p), &inv(a, n, p), n, p); // (log f)'
    let mut c = zero(n);
    for k in 1..n {
        c[k] = mulm(r[k - 1], invm((k as u64) % p, p), p);
    }
    c
}

// ------------------------------------------------------------- the object ---

// 1/(q;q)_m: partitions into parts <= m.
fn inv_poch(m: usize, n: usize, p: u64) -> S {
    let mut c = zero(n);
    c[0] = 1 % p;
    for part in 1..=m {
        if part >= n {
            break;
        }
        for k in part..n {
            c[k] = addm(c[k], c[k - part], p);
        }
    }
    c
}

// g_k(q) = (-1)^k q^{k(k-1)} / (q;q)_{2k},  G(q,z) = sum_k g_k(q) z^k.
fn g_coeffs(n: usize, p: u64) -> Vec<S> {
    let mut out = Vec::new();
    let mut k = 0usize;
    loop {
        let v = k * k.saturating_sub(1);
        if k > 0 && v >= n {
            break;
        }
        let ip = inv_poch(2 * k, n, p);
        let mut s = zero(n);
        for j in 0..(n - v) {
            s[v + j] = ip[j];
        }
        if k % 2 == 1 {
            s = s.iter().map(|&x| subm(0, x, p)).collect();
        }
        out.push(s);
        k += 1;
    }
    out
}

fn eval_g(g: &[S], z: &S, n: usize, p: u64) -> S {
    let kmax = g.len() - 1;
    let mut acc = trunc(&g[kmax], n);
    for k in (0..kmax).rev() {
        acc = mul(&acc, z, n, p);
        acc = addv(&acc, &trunc(&g[k], n), p);
    }
    acc
}
fn eval_gz(g: &[S], z: &S, n: usize, p: u64) -> S {
    let kmax = g.len() - 1;
    let mut acc = scal(&trunc(&g[kmax], n), (kmax as u64) % p, p);
    for k in (1..kmax).rev() {
        acc = mul(&acc, z, n, p);
        acc = addv(&acc, &scal(&trunc(&g[k], n), (k as u64) % p, p), p);
    }
    acc
}

// u_1 = z_1 in 1 + q F_p[[q]], by Newton with doubling precision.
fn u1_series(n: usize, p: u64) -> S {
    let g = g_coeffs(n, p);
    let mut prec = 1usize;
    let mut z = one(1, p);
    while prec < n {
        let np = (2 * prec).min(n);
        z = trunc(&z, np);
        let gz = eval_g(&g, &z, np, p);
        let gzz = eval_gz(&g, &z, np, p);
        z = subv(&z, &mul(&gz, &inv(&gzz, np, p), np, p), p);
        prec = np;
    }
    let res = eval_g(&g, &z, n, p);
    assert!(
        res.iter().all(|&x| x == 0),
        "Newton residual nonzero: u_1 was not computed"
    );
    z
}

fn eisenstein(weight: u32, n: usize, p: u64) -> S {
    let mut c = one(n, p);
    let (pref, e) = match weight {
        2 => (subm(0, 24 % p, p), 1u64),
        4 => (240 % p, 3u64),
        _ => panic!("weight"),
    };
    for m in 1..n {
        let mut s = 0u64;
        let mut d = 1usize;
        while d * d <= m {
            if m % d == 0 {
                s = addm(s, powm(d as u64, e, p), p);
                let d2 = m / d;
                if d2 != d {
                    s = addm(s, powm(d2 as u64, e, p), p);
                }
            }
            d += 1;
        }
        c[m] = mulm(pref, s, p);
    }
    c
}

// ---------------------------------------------------------------- ranks -----

// Rank of the matrix whose COLUMNS are the given series truncated to `rows`
// coefficients.  Forward elimination only; rank is all that is wanted.
fn rank_of(cols: &[S], rows: usize, p: u64) -> usize {
    let nc = cols.len();
    let mut a: Vec<Vec<u64>> = (0..rows)
        .map(|r| (0..nc).map(|c| cols[c][r]).collect())
        .collect();
    let mut rk = 0usize;
    for c in 0..nc {
        let piv = match (rk..rows).find(|&r| a[r][c] != 0) {
            Some(x) => x,
            None => continue,
        };
        a.swap(rk, piv);
        let iv = invm(a[rk][c], p);
        for x in a[rk][c..].iter_mut() {
            *x = mulm(*x, iv, p);
        }
        let (head, tail) = a.split_at_mut(rk + 1);
        let pivrow = &head[rk];
        for row in tail.iter_mut() {
            let f = row[c];
            if f != 0 {
                for k in c..nc {
                    row[k] = subm(row[k], mulm(f, pivrow[k], p), p);
                }
            }
        }
        rk += 1;
        if rk == rows {
            break;
        }
    }
    rk
}

// q^i * base_j for i <= dq: the "polynomial coefficients of degree <= dq" block.
fn poly_cols(basis: &[S], dq: usize, n: usize) -> Vec<S> {
    let mut cols = Vec::new();
    for b in basis {
        for i in 0..=dq {
            let mut c = zero(n);
            if i < n {
                c[i..n].copy_from_slice(&b[..(n - i)]);
            }
            cols.push(c);
        }
    }
    cols
}

struct Task {
    name: String,
    basis: Vec<S>,
    dq: usize,
}

fn build_tasks(n: usize, p: u64) -> Vec<Task> {
    let u1 = u1_series(n, p);
    let u1q2 = subst_pow(&u1, 2, n);
    let u1q3 = subst_pow(&u1, 3, n);
    let u1q4 = subst_pow(&u1, 4, n);
    let th_u1 = theta(&u1, p);
    let pow_of = |f: &S, e: usize| -> S {
        let mut r = one(n, p);
        for _ in 0..e {
            r = mul(&r, f, n, p);
        }
        r
    };
    let mut tasks = Vec::new();

    // (a) algebraic relation P(q,u_1) = 0 of bidegree <= (6,5).
    {
        let basis: Vec<S> = (0..=5).map(|j| pow_of(&u1, j)).collect();
        tasks.push(Task {
            name: "alg   P(q,u1)  bideg (6,5)".into(),
            basis: basis.clone(), dq: 6,
        });
    }

    // (h) holonomy: sum_{i<=r} P_i(q) u_1^{(i)} = 0, deg P_i <= d.
    for &(r, d) in &[(4usize, 10usize), (5, 12), (6, 14), (8, 10)] {
        let mut ders = vec![u1.clone()];
        for _ in 0..r {
            ders.push(deriv(ders.last().unwrap(), p));
        }
        tasks.push(Task {
            name: format!("hol   order {r}, deg {d}"),
            basis: ders.clone(), dq: d,
        });
    }

    // (i) Mahler battery P(q, u1(q), u1(q^d)) = 0.
    for (d, other) in [(2usize, &u1q2), (3usize, &u1q3)] {
        for &(dq, a, b) in &[
            (490usize, 1usize, 1usize),
            (150, 2, 2),
            (100, 3, 3),
            (60, 4, 4),
            (40, 5, 5),
            (30, 6, 6),
            (24, 7, 7),
            (20, 8, 8),
        ] {
            let mut basis = Vec::new();
            for i in 0..=a {
                for j in 0..=b {
                    basis.push(mul(&pow_of(&u1, i), &pow_of(other, j), n, p));
                }
            }
            tasks.push(Task {
                name: format!("mah   P(q,u1,u1(q^{d}))  ({dq},{a},{b})"),
                basis: basis.clone(), dq: dq,
            });
        }
    }

    // (i) order-two system P(q, u1(q), u1(q^2), u1(q^4)) = 0.
    for &(dq, a) in &[(30usize, 2usize), (20, 3)] {
        let mut basis = Vec::new();
        for i in 0..=a {
            for j in 0..=a {
                for k in 0..=a {
                    basis.push(mul(
                        &mul(&pow_of(&u1, i), &pow_of(&u1q2, j), n, p),
                        &pow_of(&u1q4, k),
                        n,
                        p,
                    ));
                }
            }
        }
        tasks.push(Task {
            name: format!("sys   P(q,u1,u1(q^2),u1(q^4))  ({dq},{a},{a},{a})"),
            basis: basis.clone(), dq: dq,
        });
    }

    // (i) difference-differential mix P(q, u1, theta u1, u1(q^2)) = 0.
    for &(dq, a) in &[(60usize, 2usize), (40, 3), (30, 4)] {
        let mut basis = Vec::new();
        for i in 0..=a {
            for j in 0..=a {
                for k in 0..=a {
                    basis.push(mul(
                        &mul(&pow_of(&u1, i), &pow_of(&th_u1, j), n, p),
                        &pow_of(&u1q2, k),
                        n,
                        p,
                    ));
                }
            }
        }
        tasks.push(Task {
            name: format!("dmix  P(q,u1,th u1,u1(q^2))  ({dq},{a},{a},{a})"),
            basis: basis.clone(), dq: dq,
        });
    }

    // (i) Mahler relation for theta log u1 itself.
    let l1 = theta(&log_series(&u1, n, p), p);
    let l2 = theta(&log_series(&u1q2, n, p), p);
    for &(dq, a, b) in &[(150usize, 2usize, 2usize), (100, 3, 3), (60, 4, 4)] {
        let mut basis = Vec::new();
        for i in 0..=a {
            for j in 0..=b {
                basis.push(mul(&pow_of(&l1, i), &pow_of(&l2, j), n, p));
            }
        }
        tasks.push(Task {
            name: format!("mahL  P(q, th log u1, th log u1(q^2))  ({dq},{a},{b})"),
            basis: basis.clone(), dq: dq,
        });
    }

    // (i) quasi-modular coupling, SIX generators, E_4 included.
    {
        let e2 = eisenstein(2, n, p);
        let e2q2 = subst_pow(&e2, 2, n);
        let e4 = eisenstein(4, n, p);
        let six = vec![one(n, p), l1.clone(), l2.clone(), e2, e2q2, e4];
        tasks.push(Task {
            name: "qmod  {1,thlog u1,thlog u1(q^2),E2(q),E2(q^2),E4(q)} deg 399".into(),
            basis: six.clone(), dq: 399,
        });
        // and the five-generator basket without E_4, for comparison.
        let five = vec![
            one(n, p),
            l1.clone(),
            l2.clone(),
            eisenstein(2, n, p),
            subst_pow(&eisenstein(2, n, p), 2, n),
        ];
        tasks.push(Task {
            name: "qmod5 {1,thlog u1,thlog u1(q^2),E2(q),E2(q^2)} deg 399".into(),
            basis: five.clone(), dq: 399,
        });
    }

    // (i) log-linear relation.
    {
        let ll = vec![one(n, p), log_series(&u1, n, p), log_series(&u1q2, n, p)];
        tasks.push(Task {
            name: "logl  {1,log u1(q),log u1(q^2)} deg 665".into(),
            basis: ll.clone(), dq: 665,
        });
    }

    tasks
}

fn run(n: usize, p: u64) -> Vec<(String, usize, usize, usize)> {
    let tasks = build_tasks(n, p);
    let mut out = Vec::new();
    for t in tasks {
        let nc = t.basis.len() * (t.dq + 1);
        let rows = (nc + 64).min(n - 20);
        if rows <= nc {
            out.push((t.name, 0, nc, usize::MAX));
            continue;
        }
        let s = Instant::now();
        let cols = poly_cols(&t.basis, t.dq, n);
        let r = rank_of(&cols, rows, p);
        drop(cols);
        eprintln!("  {:<58} rank {r}/{nc}  [{:.1}s]", t.name, s.elapsed().as_secs_f64());
        out.push((t.name, rows, nc, r));
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(4000);

    println!("qcos_rank: exclusion sweeps for the Hahn-Exton zero curve u_1(q) = z_1(q)");
    println!("series order n = {n};  primes p1 = {P1}, p2 = {P2}");
    println!(
        "A relation over Q(q) may be scaled to a primitive integer one, which survives\n\
         reduction, so RANK = COLS at one prime already proves that no relation of that\n\
         profile exists over Q.  Both primes are run; a disagreement would be a bug.\n"
    );

    // Sanity certificate: the first coefficients of u_1, lifted to signed residues,
    // must be the integer sequence quoted in the paper.
    {
        let u = u1_series(64.min(n), P1);
        let lift: Vec<i64> = u[..25]
            .iter()
            .map(|&x| if x > P1 / 2 { x as i64 - P1 as i64 } else { x as i64 })
            .collect();
        let want: [i64; 25] = [
            1, -1, 0, -1, 1, -1, 2, -2, 4, -6, 8, -14, 21, -34, 56, -88, 148, -242, 398, -669,
            1109, -1867, 3145, -5293, 8987,
        ];
        assert_eq!(lift.as_slice(), want.as_slice(), "u_1 prefix mismatch");
        println!("u_1 prefix check (25 coefficients, signed lift mod p1): OK");
        println!("  {lift:?}\n");
    }

    let t0 = Instant::now();
    eprintln!("prime 1:");
    let r1 = run(n, P1);
    eprintln!("prime 2:");
    let r2 = run(n, P2);

    println!(
        "{:<58} {:>6} {:>6} {:>8} {:>8}  verdict",
        "relation family and profile", "rows", "cols", "rank p1", "rank p2"
    );
    let mut all_full = true;
    for (a, b) in r1.iter().zip(r2.iter()) {
        if a.3 == usize::MAX {
            println!("{:<58} SKIPPED: order {n} too small for {} columns", a.0, a.2);
            all_full = false;
            continue;
        }
        let full = a.3 == a.2 && b.3 == b.2;
        all_full &= full;
        println!(
            "{:<58} {:>6} {:>6} {:>8} {:>8}  {}",
            a.0,
            a.1,
            a.2,
            a.3,
            b.3,
            if full { "NO RELATION" } else { "RANK DEFICIT" }
        );
    }
    println!();
    println!(
        "VERDICT: {}",
        if all_full {
            "full column rank at both primes on every profile: no relation of any listed profile exists over Q."
        } else {
            "at least one profile is rank deficient or was skipped; see the table."
        }
    );
    println!("total {:.1}s", t0.elapsed().as_secs_f64());
}
