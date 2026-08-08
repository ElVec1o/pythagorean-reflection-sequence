// strat_ident -- the identification counts of paper 4, Section "The translation subgroup
// on a stratum", recomputed from the geometry.
//
// The paper states: "Within that window the numbers of identifications are 3255 for m=3,
// 476 for m=5, 14 for m=7, and none for m=9 and m=11; for m=3 moreover 76 generic
// translations become trivial."  Every one of those numbers is reproduced below, under the
// convention identifications = N - #classes and at the leg ratio 2:3.  What the paper does
// not say is that the counts are NOT constant along the stratum: at 1:3 the m=3 count is
// 3241 and the m=5 count is 302, and at 1:2 the m=9 count is 64 rather than 0.  The word
// "identifications" is ambiguous too: the excess N - #classes and the number of unordered
// colliding pairs differ by a factor of about 4.5 at m = 3.  Both are printed.
//
// METHOD.  Everything is exact in F_p with p prime, p = 1 mod 27720, so that F_p contains
// i = sqrt(-1) and a primitive 2m-th root of unity for every m <= 11 of interest; cos(pi/m)
// and sin(pi/m) are then honest field elements and the reflections are F_p-rational.
//
//   generic shape: vertices (0,0), (1,0), (P,Q) with P,Q rational.
//   stratum shape: apex angle exactly pi/m at the origin, between the x-axis and the ray at
//                  angle pi/m; the third side joins (a,0) to b*(cos pi/m, sin pi/m), so the
//                  ratio a:b is the one remaining degree of freedom.
//
// A word is a generic translation iff its generic linear part is the identity.  The linear
// part is a rotation through 2(A t0 + B t1 + C t2) for integers A,B,C determined by the word,
// so vanishing at a generic shape forces A=B=C=0 and the word is then a translation at EVERY
// shape.  Hence the map "generic translation -> stratum image" is well defined; the program
// asserts this rather than assuming it, by checking every representative.
//
// NOT COMPUTED HERE, DELIBERATELY.  The paper also splits the identifications into those
// "holding already in W_m" and those "new from the level relation".  That split cannot be
// computed from this data: W_m = D_m * C_2 is a quotient of the free product, but it is NOT
// a quotient of the generic group, so a generic translation has no well-defined image in
// W_m -- the image depends on which representative word is chosen.  Deciding the split needs
// the lamp-configuration model (wrapping n -> n mod m), not word images.
//
// Rule 8: the enumeration is a depth-first walk carrying one affine map per level, so memory
// is O(depth) plus the table of translations (a few thousand entries).  MAX_NODES caps it.

use std::collections::HashMap;

const MAX_DEPTH: usize = 18;
const MAX_NODES: u64 = 4_000_000; // 1 + 3(2^18 - 1) = 786430 expected

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

/// A prime p = 1 (mod 27720) near the requested size, plus a generator of F_p^*.
fn find_prime(start: u64) -> u64 {
    let step = 27720u64;
    let mut k = start / step;
    loop {
        let cand = k * step + 1;
        if cand > start && is_prime(cand) {
            return cand;
        }
        k += 1;
        assert!(k < start / step + 1_000_000, "no prime found");
    }
}

fn generator() -> Fp {
    // factor p-1 enough to test: p-1 = 27720 * t; trial-divide p-1
    let mut n = p() - 1;
    let mut fac: Vec<u64> = Vec::new();
    let mut d = 2u64;
    while d * d <= n {
        if n % d == 0 {
            fac.push(d);
            while n % d == 0 {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        fac.push(n);
    }
    for g in 2u64..1000 {
        let gg = Fp(g);
        if fac.iter().all(|&q| powm(gg, (p() - 1) / q).0 != 1) {
            return gg;
        }
    }
    panic!("no generator");
}

// ---------------------------------------------------------------- affine maps

/// x |-> M x + t, with M = [[m00,m01],[m10,m11]].
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

/// Reflection in the line through `pt` with normal `v` (v need not be a unit vector):
/// x |-> x - 2 ((x-pt).v / v.v) v.
fn reflection(pt: [Fp; 2], v: [Fp; 2]) -> Aff {
    let vv = add(mul(v[0], v[0]), mul(v[1], v[1]));
    assert!(vv.0 != 0, "degenerate normal (v.v = 0 in F_p)");
    let ivv = inv(vv);
    let two = fp(2);
    let c = mul(two, ivv);
    // M = I - c * v v^T
    let m = [
        sub(Fp(1), mul(c, mul(v[0], v[0]))),
        sub(Fp(0), mul(c, mul(v[0], v[1]))),
        sub(Fp(0), mul(c, mul(v[1], v[0]))),
        sub(Fp(1), mul(c, mul(v[1], v[1]))),
    ];
    // t = c (pt.v) v
    let pv = add(mul(pt[0], v[0]), mul(pt[1], v[1]));
    let k = mul(c, pv);
    Aff { m, t: [mul(k, v[0]), mul(k, v[1])] }
}

fn is_translation(f: &Aff) -> bool {
    f.m[0] == Fp(1) && f.m[1] == Fp(0) && f.m[2] == Fp(0) && f.m[3] == Fp(1)
}

// ---------------------------------------------------------------- the two shapes

/// Generic triangle: (0,0), (1,0), (P,Q).
fn generic_gens(pn: i64, pd: i64, qn: i64, qd: i64) -> [Aff; 3] {
    let pp = mul(fp(pn), inv(fp(pd)));
    let qq = mul(fp(qn), inv(fp(qd)));
    let r0 = reflection([Fp(0), Fp(0)], [Fp(0), Fp(1)]); // x-axis
    let r1 = reflection([Fp(0), Fp(0)], [qq, sub(Fp(0), pp)]); // through (0,0),(P,Q)
    let r2 = reflection([Fp(1), Fp(0)], [qq, sub(Fp(1), pp)]); // through (1,0),(P,Q)
    [r0, r1, r2]
}

/// Stratum triangle: apex angle pi/m at the origin between the x-axis and the ray at
/// angle pi/m; third side from (a,0) to b*(cos, sin).  Ratio a:b is the free parameter.
fn stratum_gens(m: u64, a: i64, b: i64, zeta2m: Fp, i_unit: Fp) -> [Aff; 3] {
    let _ = m;
    let z = zeta2m;
    let zi = inv(z);
    let two = fp(2);
    let c = mul(add(z, zi), inv(two)); // cos(pi/m)
    let s = mul(sub(z, zi), inv(mul(two, i_unit))); // sin(pi/m)
    let aa = fp(a);
    let bb = fp(b);
    let r0 = reflection([Fp(0), Fp(0)], [Fp(0), Fp(1)]); // x-axis
    let r1 = reflection([Fp(0), Fp(0)], [sub(Fp(0), s), c]); // ray at angle pi/m
    // third side through (a,0) and b(c,s): direction (bc-a, bs), normal (bs, a-bc)
    let bc = mul(bb, c);
    let bs = mul(bb, s);
    let r2 = reflection([aa, Fp(0)], [bs, sub(aa, bc)]);
    [r0, r1, r2]
}

// ---------------------------------------------------------------- enumeration

/// Depth-first over reduced words, recording for each generic translation its minimal
/// length and one representative word attaining it.
fn collect_translations(gens: &[Aff; 3]) -> (HashMap<[Fp; 2], (usize, Vec<u8>)>, u64) {
    let mut table: HashMap<[Fp; 2], (usize, Vec<u8>)> = HashMap::new();
    let mut nodes: u64 = 0;
    // stack of (current map, word, last letter)
    let mut stack: Vec<(Aff, Vec<u8>, i8)> = vec![(ident(), Vec::new(), -1)];
    while let Some((f, w, last)) = stack.pop() {
        nodes += 1;
        assert!(nodes <= MAX_NODES, "node cap exceeded (Rule 8)");
        if !w.is_empty() && is_translation(&f) {
            let key = f.t;
            let e = table.entry(key).or_insert((usize::MAX, Vec::new()));
            if w.len() < e.0 {
                *e = (w.len(), w.clone());
            }
        }
        if w.len() == MAX_DEPTH {
            continue;
        }
        for g in 0..3u8 {
            if g as i8 == last {
                continue;
            }
            let mut w2 = w.clone();
            w2.push(g);
            stack.push((compose(&f, &gens[g as usize]), w2, g as i8));
        }
    }
    (table, nodes)
}

fn eval_word(w: &[u8], gens: &[Aff; 3]) -> Aff {
    let mut f = ident();
    for &g in w {
        f = compose(&f, &gens[g as usize]);
    }
    f
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 { args[1].parse().unwrap() } else { 2_305_843_009_213_693_951 };
    let prime = find_prime(seed);
    unsafe {
        P = prime;
    }
    let g = generator();
    let i_unit = powm(g, (prime - 1) / 4); // sqrt(-1)
    assert_eq!(mul(i_unit, i_unit), fp(-1), "i^2 != -1");
    println!("p = {}   generator = {}   i = {}", prime, g.0, i_unit.0);

    for (pn, pd, qn, qd) in [(2i64, 7i64, 3i64, 5i64), (5, 11, 7, 13)] {
        println!("\n=== generic apex ({}/{}, {}/{}) ===", pn, pd, qn, qd);
        let ggens = generic_gens(pn, pd, qn, qd);
        let (table, nodes) = collect_translations(&ggens);
        println!("  reduced words visited: {}", nodes);

        // census by length
        let mut by_len = vec![0usize; MAX_DEPTH + 1];
        for (_, (l, _)) in table.iter() {
            by_len[*l] += 1;
        }
        let census: Vec<usize> = (0..=MAX_DEPTH).filter(|d| by_len[*d] > 0).map(|d| by_len[d]).collect();
        println!("  generic translation census by length: {:?}", census);
        println!("  total generic translations of length <= {}: {}", MAX_DEPTH, table.len());

        // representatives, sorted for determinism
        let mut reps: Vec<(usize, Vec<u8>)> = table.values().cloned().collect();
        reps.sort();

        for m in [3u64, 5, 7, 9, 11] {
            let zeta = powm(g, (prime - 1) / (2 * m));
            for (a, b) in [(1i64, 2i64), (1, 3), (2, 3)] {
                let sgens = stratum_gens(m, a, b, zeta, i_unit);
                // sanity: (r1 r0)^m must be the identity linear part on the stratum
                let mut rot = ident();
                for _ in 0..m {
                    rot = compose(&rot, &compose(&sgens[1], &sgens[0]));
                }
                assert!(is_translation(&rot), "apex rotation of order m failed, m={}", m);

                let mut classes: HashMap<[Fp; 2], usize> = HashMap::new();
                let mut trivial = 0usize;
                let mut nontrans = 0usize;
                for (_, w) in &reps {
                    let f = eval_word(w, &sgens);
                    if !is_translation(&f) {
                        nontrans += 1;
                        continue;
                    }
                    if f.t == [Fp(0), Fp(0)] {
                        trivial += 1;
                    }
                    *classes.entry(f.t).or_insert(0) += 1;
                }
                assert_eq!(nontrans, 0, "a generic translation lost translation-ness on the stratum");
                let n = reps.len();
                let excess = n - classes.len();
                let pairs: usize = classes.values().map(|&s| s * (s - 1) / 2).sum();
                let mut profile: Vec<(usize, usize)> = {
                    let mut h: HashMap<usize, usize> = HashMap::new();
                    for &s in classes.values() {
                        if s > 1 {
                            *h.entry(s).or_insert(0) += 1;
                        }
                    }
                    h.into_iter().collect()
                };
                profile.sort();
                println!(
                    "  m={:2} legs {}:{}   classes={:5}  excess={:5}  pairs={:6}  trivial={:3}  profile={:?}",
                    m, a, b, classes.len(), excess, pairs, trivial, profile
                );
            }
        }
    }
}
