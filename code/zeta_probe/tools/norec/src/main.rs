// norec: Farkas certificates that u_0..u_38 satisfies no linear recurrence of order <= 19.
//
// Paper "extra", prop:no-recurrence.  For each order k the claim is that the system
//
//     u_n = sum_{j=1..k} c_j u_{n-j},    n = k, ..., 38        (39 - k equations, k unknowns)
//
// has no rational solution.  Inconsistency of a linear system is certified by a Farkas
// witness: an integer vector w with w^T A = 0 and w^T b != 0.  If some rational c solved the
// system then w^T b = w^T A c = 0, a contradiction.  The witness is therefore a complete and
// self-contained proof, checkable by integer arithmetic alone, which is what lets Lean verify
// it in the kernel without redoing any linear algebra.
//
// Witnesses are found by exact rational Gaussian elimination on A^T (left null space of A),
// then cleared of denominators and reduced by the gcd of their entries.  All arithmetic is
// exact via GMP; nothing here is floating point.

use rug::{Integer, Rational};
use std::collections::HashSet;

const U: [i64; 39] = [
    1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574,
    11543, 17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236,
    1697179, 2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781,
];

const KMAX: usize = 19;

fn main() {
    let n_terms = U.len(); // 39
    let mut all_ok = true;
    let mut lines: Vec<String> = Vec::new();

    for k in 1..=KMAX {
        let rows = n_terms - k; // equations, n = k ..= 38

        // A[i][j] = u_{n-1-j} with n = k+i,  b[i] = u_n
        let a: Vec<Vec<Integer>> = (0..rows)
            .map(|i| {
                let n = k + i;
                (0..k).map(|j| Integer::from(U[n - 1 - j])).collect()
            })
            .collect();
        let b: Vec<Integer> = (0..rows).map(|i| Integer::from(U[k + i])).collect();

        // m = A^T, a k x rows matrix over the rationals; its null space is left-null(A).
        let mut m: Vec<Vec<Rational>> = (0..k)
            .map(|j| (0..rows).map(|i| Rational::from(a[i][j].clone())).collect())
            .collect();

        // Reduced row echelon form.
        let mut pivots: Vec<usize> = Vec::new();
        let mut row = 0usize;
        for col in 0..rows {
            if row >= k {
                break;
            }
            let mut sel: Option<usize> = None;
            for rr in row..k {
                if m[rr][col] != 0 {
                    sel = Some(rr);
                    break;
                }
            }
            let s = match sel {
                Some(s) => s,
                None => continue,
            };
            m.swap(row, s);
            let pv = m[row][col].clone();
            for c in 0..rows {
                let v = m[row][c].clone() / pv.clone();
                m[row][c] = v;
            }
            for rr in 0..k {
                if rr != row && m[rr][col] != 0 {
                    let f = m[rr][col].clone();
                    for c in 0..rows {
                        let d = m[row][c].clone() * f.clone();
                        m[rr][c] -= d;
                    }
                }
            }
            pivots.push(col);
            row += 1;
        }

        let pivset: HashSet<usize> = pivots.iter().cloned().collect();

        // Walk the free columns; each yields a null vector of A^T.  Take the first whose
        // pairing with b is nonzero.
        let mut found: Option<(Vec<Integer>, Integer)> = None;
        for f in 0..rows {
            if pivset.contains(&f) {
                continue;
            }
            let mut w: Vec<Rational> = vec![Rational::from(0); rows];
            w[f] = Rational::from(1);
            for (i, &p) in pivots.iter().enumerate() {
                w[p] = -m[i][f].clone();
            }

            // Clear denominators, then reduce by the gcd so entries stay as small as possible.
            let mut l = Integer::from(1);
            for x in &w {
                l = l.lcm(&Integer::from(x.denom()));
            }
            let mut wi: Vec<Integer> = w
                .iter()
                .map(|x| (Integer::from(x.numer()) * l.clone()) / Integer::from(x.denom()))
                .collect();
            let mut g = Integer::from(0);
            for x in &wi {
                g = g.gcd(x);
            }
            if g != 0 && g != 1 {
                wi = wi.iter().map(|x| Integer::from(x / &g)).collect();
            }

            // Verify the witness exactly: w^T A = 0.
            let mut ok = true;
            for j in 0..k {
                let mut s = Integer::from(0);
                for i in 0..rows {
                    s += Integer::from(&wi[i] * &a[i][j]);
                }
                if s != 0 {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            // And w^T b != 0.
            let mut sb = Integer::from(0);
            for i in 0..rows {
                sb += Integer::from(&wi[i] * &b[i]);
            }
            if sb != 0 {
                found = Some((wi, sb));
                break;
            }
        }

        match found {
            Some((wi, sb)) => {
                let maxdigits = wi.iter().map(|x| x.to_string().trim_start_matches('-').len()).max().unwrap_or(0);
                eprintln!(
                    "k={:2}  rows={:2}  rank={:2}  witness found, max entry {} digits, w.b has {} digits",
                    k, rows, pivots.len(), maxdigits, sb.to_string().trim_start_matches('-').len()
                );
                let ws: Vec<String> = wi.iter().map(|x| x.to_string()).collect();
                lines.push(format!("({}, [{}])", k, ws.join(", ")));
            }
            None => {
                all_ok = false;
                eprintln!("k={:2}  NO WITNESS -- the system is consistent, a recurrence exists", k);
            }
        }
    }

    if all_ok {
        eprintln!("\nAll {} orders certified inconsistent.", KMAX);
    } else {
        eprintln!("\nFAILED: some order admits a recurrence.");
    }

    // Emit the certificates for the Lean file, one per line: k followed by the witness.
    for l in &lines {
        println!("{}", l);
    }
}
