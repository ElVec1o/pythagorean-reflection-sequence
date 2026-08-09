// nodfinite: rank certificates for prop:no-dfinite of paper "extra".
//
// For each (k, m) on the search grid, a D-finite recurrence of order k with coefficient
// polynomials of degree m is a nonzero solution of the HOMOGENEOUS system
//
//     sum_{j=0..k} p_j(n) u_{n-j} = 0,    n = k..42,     p_j of degree <= m.
//
// Unknowns are the (k+1)(m+1) coefficients c_{j,t}; the matrix entry in row n and column
// (j,t) is n^t * u_{n-j}.  No nonzero solution exists exactly when the matrix has FULL
// COLUMN RANK.
//
// Certificate.  Exhibit `cols` row indices whose square submatrix M is invertible modulo a
// prime p, by giving M^{-1} mod p.  Verifying M^{-1} M = I (mod p) shows rank_{F_p}(A) = cols,
// and since reduction mod p can only drop rank, rank_Q(A) = cols as well.  So the kernel is
// trivial over Q and no such recurrence exists.  The implication runs the right way: a
// modular certificate PROVES the rational statement here, unlike a modular search, which
// would only be evidence.

const P: i64 = 2147483647; // 2^31 - 1, prime

const U: [i64; 43] = [
    1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574,
    11543, 17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236,
    1697179, 2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781, 43997388,
    65932461, 98849591, 147969934,
];

fn norm(a: i64) -> i64 { ((a % P) + P) % P }
fn mul(a: i64, b: i64) -> i64 { ((a as i128 * b as i128) % P as i128) as i64 }
fn powm(mut a: i64, mut e: i64) -> i64 {
    let mut r = 1i64; a = norm(a);
    while e > 0 { if e & 1 == 1 { r = mul(r, a); } a = mul(a, a); e >>= 1; }
    r
}
fn inv(a: i64) -> i64 { powm(a, P - 2) }

// Certify one (k, m) pair.  Returns the certificate line, or None if the coefficient matrix
// fails to reach full column rank modulo P.
fn certify(k: usize, m: usize) -> Option<String> {
    let nterms = U.len(); // 43
    {
        {
            let cols = (k + 1) * (m + 1);
            let eqs = nterms - k; // n = k..42
            if !(cols < eqs) {
                println!("k={} m={} NOT OVER-DETERMINED (cols {} >= eqs {})", k, m, cols, eqs);
                return None;
            }

            // A[i][c], row i <-> n = k+i, col c <-> (j,t)
            let mut a = vec![vec![0i64; cols]; eqs];
            for i in 0..eqs {
                let n = (k + i) as i64;
                for j in 0..=k {
                    let uv = norm(U[k + i - j]);
                    let mut nt = 1i64;
                    for t in 0..=m {
                        a[i][j * (m + 1) + t] = mul(nt, uv);
                        nt = mul(nt, n);
                    }
                }
            }

            // Gaussian elimination mod P on a copy, tracking which rows became pivots.
            let mut w = a.clone();
            let mut pivot_rows: Vec<usize> = Vec::new();
            let mut r = 0usize;
            for c in 0..cols {
                let mut sel = None;
                for rr in r..eqs { if w[rr][c] != 0 { sel = Some(rr); break; } }
                let s = match sel { Some(s) => s, None => continue };
                w.swap(r, s);
                // remember which ORIGINAL row this is: track by permutation
                pivot_rows.push(s.max(r)); // placeholder, fixed below
                let iv = inv(w[r][c]);
                for cc in 0..cols { w[r][cc] = mul(w[r][cc], iv); }
                for rr in 0..eqs {
                    if rr != r && w[rr][c] != 0 {
                        let f = w[rr][c];
                        for cc in 0..cols {
                            w[rr][cc] = norm(w[rr][cc] - mul(f, w[r][cc]));
                        }
                    }
                }
                r += 1;
                if r == cols { break; }
            }

            if r < cols {
                println!("k={} m={} FULL RANK NOT REACHED (rank {} < cols {})", k, m, r, cols);
                return None;
            }

            // Redo elimination tracking original row indices properly.
            let mut idx: Vec<usize> = (0..eqs).collect();
            let mut w2 = a.clone();
            let mut r2 = 0usize;
            let mut chosen: Vec<usize> = Vec::new();
            for c in 0..cols {
                let mut sel = None;
                for rr in r2..eqs { if w2[rr][c] != 0 { sel = Some(rr); break; } }
                let s = match sel { Some(s) => s, None => continue };
                w2.swap(r2, s); idx.swap(r2, s);
                chosen.push(idx[r2]);
                let iv = inv(w2[r2][c]);
                for cc in 0..cols { w2[r2][cc] = mul(w2[r2][cc], iv); }
                for rr in 0..eqs {
                    if rr != r2 && w2[rr][c] != 0 {
                        let f = w2[rr][c];
                        for cc in 0..cols { w2[rr][cc] = norm(w2[rr][cc] - mul(f, w2[r2][cc])); }
                    }
                }
                r2 += 1;
                if r2 == cols { break; }
            }

            // M = the chosen rows of A; compute M^{-1} mod P by Gauss-Jordan.
            let mut mm = vec![vec![0i64; cols]; cols];
            for (ri, &orig) in chosen.iter().enumerate() {
                for c in 0..cols { mm[ri][c] = a[orig][c]; }
            }
            let mut aug = mm.clone();
            let mut invm = vec![vec![0i64; cols]; cols];
            for i in 0..cols { invm[i][i] = 1; }
            for c in 0..cols {
                let mut sel = None;
                for rr in c..cols { if aug[rr][c] != 0 { sel = Some(rr); break; } }
                let s = sel.expect("submatrix singular, contradicting pivot selection");
                aug.swap(c, s); invm.swap(c, s);
                let iv = inv(aug[c][c]);
                for cc in 0..cols { aug[c][cc] = mul(aug[c][cc], iv); invm[c][cc] = mul(invm[c][cc], iv); }
                for rr in 0..cols {
                    if rr != c && aug[rr][c] != 0 {
                        let f = aug[rr][c];
                        for cc in 0..cols {
                            aug[rr][cc] = norm(aug[rr][cc] - mul(f, aug[c][cc]));
                            invm[rr][cc] = norm(invm[rr][cc] - mul(f, invm[c][cc]));
                        }
                    }
                }
            }

            // Self-check: invm * mm == I (mod P)
            for i in 0..cols {
                for j in 0..cols {
                    let mut s = 0i64;
                    for t in 0..cols { s = norm(s + mul(invm[i][t], mm[t][j])); }
                    let want = if i == j { 1 } else { 0 };
                    assert_eq!(s, want, "self-check failed at k={} m={}", k, m);
                }
            }

            let rows_s: Vec<String> = chosen.iter().map(|x| x.to_string()).collect();
            let inv_s: Vec<String> = invm.iter()
                .map(|row| format!("[{}]", row.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")))
                .collect();
            eprintln!("k={} m={} cols={:2} eqs={:2} full column rank certified", k, m, cols, eqs);
            Some(format!("({}, {}, [{}], [{}]),\n", k, m, rows_s.join(","), inv_s.join(",")))
        }
    }
}

// With no arguments: sweep the 52-pair grid of `prop:no-dfinite` (1 <= k <= 9, m <= 7,
// over-determined).  With arguments "k,m" ...: certify exactly those pairs, which is how the
// extra maximal cells of the narrowed holonomic box of `prop:finite-horizon`(ii) are produced.
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = String::new();
    let mut count = 0;
    let mut failures = 0;

    if args.is_empty() {
        for k in 1..=9usize {
            for m in 0..=7usize {
                let cols = (k + 1) * (m + 1);
                if !(cols < U.len() - k) { continue; }
                count += 1;
                match certify(k, m) {
                    Some(s) => out.push_str(&s),
                    None => failures += 1,
                }
            }
        }
    } else {
        for a in &args {
            let mut it = a.split(',');
            let k: usize = it.next().expect("pair").parse().expect("k");
            let m: usize = it.next().expect("pair").parse().expect("m");
            count += 1;
            match certify(k, m) {
                Some(s) => out.push_str(&s),
                None => failures += 1,
            }
        }
    }

    eprintln!("\npairs: {}   failures: {}", count, failures);
    print!("{}", out);
}
