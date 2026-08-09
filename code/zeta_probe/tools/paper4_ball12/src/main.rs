// paper4_ball12 -- the depth-12 census of paper 4, Theorem `thm:census` and Remark
// `rem:twelve`.
//
// Regenerates, at each of three rational witness shapes:
//
//   * the growth sequence 1,3,6,12,24,48,96,192,384,768,1536,3039,6012 to depth 12;
//   * the 33 coincidences on the ball of radius 11, each between two words of length 11;
//   * the 132 further coincidences on the ball of radius 12, split as 66 + 66:
//         66 pairs of two length-12 words   (one-letter extensions of the 33),
//         66 pairs (length 12, length 10)   (the two splittings of each of the 33 relators);
//   * the count 6078 of distinct images of the 6144 reduced words of length 12, and the
//     fact that exactly 66 of those images lie at distance 10, whence the sphere 6012.
//
// WHY THE ARITHMETIC IS SOUND.  Everything is exact in F_p.  Reducing mod p can only
// IDENTIFY elements that are distinct over Q, never separate elements that are equal, so
// every count of distinct images printed here is a LOWER bound for the count over Q.  The
// matching upper bound is supplied by `verify_universal_relations.py`, which checks the 33
// and the 132 coincidences as identities of polynomials in Z[p,q].  Lower bound = upper
// bound, so the printed counts are the counts over Q.  Two independent primes are run.
//
// Rule 8: the ball of radius 12 has at most 1 + 3(2^12 - 1) = 12286 elements, so memory is
// a few megabytes and the whole run takes well under a second.
//
// Usage:  paper4_ball12 [prime_seed ...]
// Build:  cargo build --release

use std::collections::HashMap;

const DEPTH: usize = 12;

// ---------------------------------------------------------------- F_p arithmetic

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Fp(u64);

static mut P: u64 = 0;

#[inline]
fn p() -> u64 {
    unsafe { P }
}
#[inline]
fn add(a: Fp, b: Fp) -> Fp {
    let s = a.0 + b.0;
    Fp(if s >= p() { s - p() } else { s })
}
#[inline]
fn sub(a: Fp, b: Fp) -> Fp {
    Fp(if a.0 >= b.0 { a.0 - b.0 } else { a.0 + p() - b.0 })
}
#[inline]
fn mul(a: Fp, b: Fp) -> Fp {
    Fp(((a.0 as u128 * b.0 as u128) % p() as u128) as u64)
}
fn powm(a: Fp, mut e: u64) -> Fp {
    let mut r = Fp(1);
    let mut b = a;
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, b);
        }
        b = mul(b, b);
        e >>= 1;
    }
    r
}
fn inv(a: Fp) -> Fp {
    assert!(a.0 != 0, "inverse of zero");
    powm(a, p() - 2)
}
fn fp(x: i64) -> Fp {
    let m = p() as i64;
    Fp(((x % m + m) % m) as u64)
}

fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for q in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % q == 0 {
            return n == q;
        }
    }
    let mut d = n - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'outer: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = {
            let mut r: u128 = 1;
            let mut b = a as u128 % n as u128;
            let mut e = d;
            while e > 0 {
                if e & 1 == 1 {
                    r = r * b % n as u128;
                }
                b = b * b % n as u128;
                e >>= 1;
            }
            r as u64
        };
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 0..s - 1 {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

fn next_prime(start: u64) -> u64 {
    let mut c = start | 1;
    loop {
        if is_prime(c) {
            return c;
        }
        c += 2;
    }
}

// ---------------------------------------------------------------- affine maps

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Aff {
    m: [Fp; 4],
    t: [Fp; 2],
}

fn ident() -> Aff {
    Aff { m: [Fp(1), Fp(0), Fp(0), Fp(1)], t: [Fp(0), Fp(0)] }
}

/// f1 after f2.
fn compose(f1: &Aff, f2: &Aff) -> Aff {
    let m = [
        add(mul(f1.m[0], f2.m[0]), mul(f1.m[1], f2.m[2])),
        add(mul(f1.m[0], f2.m[1]), mul(f1.m[1], f2.m[3])),
        add(mul(f1.m[2], f2.m[0]), mul(f1.m[3], f2.m[2])),
        add(mul(f1.m[2], f2.m[1]), mul(f1.m[3], f2.m[3])),
    ];
    let t = [
        add(add(mul(f1.m[0], f2.t[0]), mul(f1.m[1], f2.t[1])), f1.t[0]),
        add(add(mul(f1.m[2], f2.t[0]), mul(f1.m[3], f2.t[1])), f1.t[1]),
    ];
    Aff { m, t }
}

/// Reflection in the line through `pt` with normal `v`.
fn reflection(pt: [Fp; 2], v: [Fp; 2]) -> Aff {
    let vv = add(mul(v[0], v[0]), mul(v[1], v[1]));
    assert!(vv.0 != 0, "degenerate normal (v.v = 0 in F_p)");
    let c = mul(fp(2), inv(vv));
    let m = [
        sub(Fp(1), mul(c, mul(v[0], v[0]))),
        sub(Fp(0), mul(c, mul(v[0], v[1]))),
        sub(Fp(0), mul(c, mul(v[1], v[0]))),
        sub(Fp(1), mul(c, mul(v[1], v[1]))),
    ];
    let pv = add(mul(pt[0], v[0]), mul(pt[1], v[1]));
    let k = mul(c, pv);
    Aff { m, t: [mul(k, v[0]), mul(k, v[1])] }
}

/// Triangle with vertices (0,0), (1,0), (P,Q).
fn gens_of(pn: i64, pd: i64, qn: i64, qd: i64) -> [Aff; 3] {
    let pp = mul(fp(pn), inv(fp(pd)));
    let qq = mul(fp(qn), inv(fp(qd)));
    let r0 = reflection([Fp(0), Fp(0)], [Fp(0), Fp(1)]);
    let r1 = reflection([Fp(0), Fp(0)], [qq, sub(Fp(0), pp)]);
    let r2 = reflection([Fp(1), Fp(0)], [qq, sub(Fp(1), pp)]);
    for r in [r0, r1, r2] {
        assert_eq!(compose(&r, &r), ident(), "a generator is not an involution");
    }
    [r0, r1, r2]
}

// ---------------------------------------------------------------- enumeration

/// All reduced words of length exactly `d`, in lexicographic order, with their images.
fn reduced_words(d: usize, gens: &[Aff; 3]) -> Vec<(Vec<u8>, Aff)> {
    let mut cur: Vec<(Vec<u8>, Aff)> = vec![(Vec::new(), ident())];
    for _ in 0..d {
        let mut next = Vec::with_capacity(cur.len() * 2 + 1);
        for (w, f) in &cur {
            let last = w.last().copied();
            for g in 0..3u8 {
                if Some(g) == last {
                    continue;
                }
                let mut w2 = w.clone();
                w2.push(g);
                next.push((w2, compose(f, &gens[g as usize])));
            }
        }
        cur = next;
    }
    cur
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seeds: Vec<u64> = if args.len() > 1 {
        args[1..].iter().map(|s| s.parse().unwrap()).collect()
    } else {
        vec![1_000_000_007, 2_305_843_009_213_693_951]
    };

    let witnesses: [(&str, i64, i64, i64, i64); 3] = [
        ("(1/3, 1/2)   acute", 1, 3, 1, 2),
        ("(2/7, 3/5)   acute", 2, 7, 3, 5),
        ("(-1/3, 1/2)  obtuse", -1, 3, 1, 2),
    ];

    for seed in seeds {
        let prime = next_prime(seed);
        unsafe {
            P = prime;
        }
        println!("================ p = {} ================", prime);

        for (name, pn, pd, qn, qd) in witnesses {
            let gens = gens_of(pn, pd, qn, qd);
            println!("\n--- witness {} ---", name);

            // ---- spheres of the word metric, by breadth-first search ----
            let mut dist: HashMap<Aff, usize> = HashMap::new();
            dist.insert(ident(), 0);
            let mut frontier = vec![ident()];
            let mut sphere = vec![1usize];
            for d in 1..=DEPTH {
                let mut next = Vec::new();
                for f in &frontier {
                    for g in gens.iter() {
                        let h = compose(f, g);
                        if !dist.contains_key(&h) {
                            dist.insert(h, d);
                            next.push(h);
                        }
                    }
                }
                sphere.push(next.len());
                frontier = next;
            }
            println!("  spheres 0..{}: {:?}", DEPTH, sphere);

            // ---- coincidences among reduced words, length by length ----
            for d in [11usize, 12] {
                let words = reduced_words(d, &gens);
                assert_eq!(words.len(), 3 * (1usize << (d - 1)), "reduced word count");
                let mut classes: HashMap<Aff, Vec<Vec<u8>>> = HashMap::new();
                for (w, f) in &words {
                    classes.entry(*f).or_default().push(w.clone());
                }
                let distinct = classes.len();
                let pairs_same: usize =
                    classes.values().map(|v| v.len() * (v.len() - 1) / 2).sum();
                // images that lie strictly inside the ball of radius d
                let mut shorter: HashMap<usize, usize> = HashMap::new();
                for f in classes.keys() {
                    let dd = *dist.get(f).expect("image outside the ball of radius 12");
                    if dd < d {
                        *shorter.entry(dd).or_insert(0) += 1;
                    }
                }
                let n_shorter: usize = shorter.values().sum();
                let mut sh: Vec<(usize, usize)> = shorter.into_iter().collect();
                sh.sort();
                println!(
                    "  length {}: {} reduced words -> {} distinct images; \
                     {} same-length coincidence pairs; {} images of smaller distance {:?}; \
                     sphere = {}",
                    d,
                    words.len(),
                    distinct,
                    pairs_same,
                    n_shorter,
                    sh,
                    distinct - n_shorter
                );

                if d == 12 {
                    // classify the 66 same-length pairs as one-letter extensions of the 33
                    let words11 = reduced_words(11, &gens);
                    let mut cls11: HashMap<Aff, Vec<Vec<u8>>> = HashMap::new();
                    for (w, f) in &words11 {
                        cls11.entry(*f).or_default().push(w.clone());
                    }
                    let pairs33: Vec<(Vec<u8>, Vec<u8>)> = {
                        let mut v = Vec::new();
                        for ws in cls11.values() {
                            if ws.len() == 2 {
                                let mut a = ws.clone();
                                a.sort();
                                v.push((a[0].clone(), a[1].clone()));
                            }
                            assert!(ws.len() <= 2, "a class of more than two length-11 words");
                        }
                        v.sort();
                        v
                    };
                    let mut left = 0usize;
                    let mut right = 0usize;
                    let mut other = 0usize;
                    for ws in classes.values() {
                        if ws.len() < 2 {
                            continue;
                        }
                        assert_eq!(ws.len(), 2, "a class of more than two length-12 words");
                        let (u, v) = (&ws[0], &ws[1]);
                        let suff_eq = u[11] == v[11]
                            && pairs33.iter().any(|(a, b)| {
                                (a[..] == u[..11] && b[..] == v[..11])
                                    || (b[..] == u[..11] && a[..] == v[..11])
                            });
                        let pref_eq = u[0] == v[0]
                            && pairs33.iter().any(|(a, b)| {
                                (a[..] == u[1..] && b[..] == v[1..])
                                    || (b[..] == u[1..] && a[..] == v[1..])
                            });
                        if suff_eq {
                            right += 1;
                        } else if pref_eq {
                            left += 1;
                        } else {
                            other += 1;
                        }
                    }
                    println!(
                        "    of the same-length pairs: {} are w.x = w'.x, {} are x.w = x.w', \
                         {} are neither",
                        right, left, other
                    );
                    println!(
                        "    coincidences beyond the ball of radius 11: {} same-length + \
                         {} with a shorter word = {}",
                        right + left + other,
                        n_shorter,
                        right + left + other + n_shorter
                    );
                    println!("    relators of the 33: length 11 + 11 = 22");
                }
            }
        }
        println!();
    }
}
