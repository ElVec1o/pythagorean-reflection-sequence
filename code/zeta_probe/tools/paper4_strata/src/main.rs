// paper4_strata -- the stratum computations of paper 4, Section "Non-generic strata".
//
// Regenerates:
//
//   (A) the table of d*(m) and delta(m): the first depth at which the sphere of the stratum
//       group falls below the coefficient of the Coxeter reference series
//           W_m(t) = (1+t)(1+t+...+t^{m-1}) / (1 - t - t^2 - ... - t^m),
//       and the deficit there, for 2 <= m <= 12; together with the depth-12 deficit, which
//       the paper compares against the generic 132.
//
//   (B) the stratum translation census by word length to depth 18, at several rational leg
//       samples; this is the table of `prop:cylcensus` and, sample by sample, the
//       leg-dependence recorded in `rem:cylcensus-status` and `rem:samples`.
//
// SHAPES.  The stratum triangle has apex angle pi/m at the origin, between the x-axis and
// the ray at angle pi/m; the third side joins (a,0) to b*(cos pi/m, sin pi/m), so the leg
// ratio a:b is the one remaining degree of freedom.  The generic triangle has vertices
// (0,0), (1,0), (P,Q).
//
// ARITHMETIC.  Exact in F_p with p = 1 mod 55440, so that F_p contains a primitive 2m-th
// root of unity for every m <= 12 and a square root of -1; cos(pi/m) and sin(pi/m) are then
// honest field elements and every reflection is F_p-rational.  Note 55440 and not 27720:
// 16 does not divide 27720, so a prime chosen with the smaller step need not carry a
// primitive 16th root of unity, which is what m = 8 requires.  Primitivity is asserted, not
// assumed.  Reducing mod p can only identify elements that are distinct in characteristic
// zero, so every sphere count printed here is a lower bound for the true one and every
// deficit an upper bound.  Two independent primes are run.
//
// Rule 8: breadth-first search holds one HashSet of affine maps; the largest ball here is
// the generic one at depth 18, 786430 elements at 48 bytes each, so a few hundred MB at
// worst.  MAX_BALL caps it.
//
// Usage:  paper4_strata [prime_seed ...]
// Build:  cargo build --release

use std::collections::HashSet;

const MAX_BALL: usize = 6_000_000;

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

/// A prime p = 1 (mod 55440) above `start`.  55440 = 2^4 * 3^2 * 5 * 7 * 11 is divisible by
/// 2m for every m <= 12 and by 4.
fn find_prime(start: u64) -> u64 {
    let step = 55440u64;
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
    for g in 2u64..10000 {
        let gg = Fp(g);
        if fac.iter().all(|&q| powm(gg, (p() - 1) / q).0 != 1) {
            return gg;
        }
    }
    panic!("no generator");
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

fn is_translation(f: &Aff) -> bool {
    f.m[0] == Fp(1) && f.m[1] == Fp(0) && f.m[2] == Fp(0) && f.m[3] == Fp(1)
}

fn generic_gens(pn: i64, pd: i64, qn: i64, qd: i64) -> [Aff; 3] {
    let pp = mul(fp(pn), inv(fp(pd)));
    let qq = mul(fp(qn), inv(fp(qd)));
    let r0 = reflection([Fp(0), Fp(0)], [Fp(0), Fp(1)]);
    let r1 = reflection([Fp(0), Fp(0)], [qq, sub(Fp(0), pp)]);
    let r2 = reflection([Fp(1), Fp(0)], [qq, sub(Fp(1), pp)]);
    [r0, r1, r2]
}

fn stratum_gens(m: u64, a: i64, b: i64, zeta2m: Fp, i_unit: Fp) -> [Aff; 3] {
    let z = zeta2m;
    let zi = inv(z);
    let two = fp(2);
    let c = mul(add(z, zi), inv(two));
    let s = mul(sub(z, zi), inv(mul(two, i_unit)));
    let aa = fp(a);
    let bb = fp(b);
    let r0 = reflection([Fp(0), Fp(0)], [Fp(0), Fp(1)]);
    let r1 = reflection([Fp(0), Fp(0)], [sub(Fp(0), s), c]);
    let bc = mul(bb, c);
    let bs = mul(bb, s);
    let r2 = reflection([aa, Fp(0)], [bs, sub(aa, bc)]);
    // the apex rotation must have order exactly m
    let mut rot = ident();
    for _ in 0..m {
        rot = compose(&rot, &compose(&r1, &r0));
    }
    assert!(is_translation(&rot), "apex rotation of order m failed, m={}", m);
    if m > 1 {
        let mut rot1 = ident();
        for _ in 0..(m - 1) {
            rot1 = compose(&rot1, &compose(&r1, &r0));
        }
        assert!(!is_translation(&rot1), "apex rotation has order < m, m={}", m);
    }
    [r0, r1, r2]
}

// ---------------------------------------------------------------- breadth-first search

/// `(spheres, translations_by_length)` for the group generated by `gens`, to `depth`.
fn bfs(gens: &[Aff; 3], depth: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    let mut seen: HashSet<Aff> = HashSet::new();
    let id = ident();
    seen.insert(id);
    let mut frontier = vec![id];
    let mut spheres = vec![1usize];
    let mut trans = vec![0usize; depth + 1];
    for d in 1..=depth {
        let mut next = Vec::new();
        for f in &frontier {
            for g in gens.iter() {
                let h = compose(f, g);
                if seen.insert(h) {
                    if is_translation(&h) {
                        trans[d] += 1;
                    }
                    next.push(h);
                    if seen.len() > MAX_BALL {
                        return None;
                    }
                }
            }
        }
        spheres.push(next.len());
        frontier = next;
    }
    Some((spheres, trans))
}

/// Coefficients of `W_m(t) = (1+t)(1+t+...+t^{m-1}) / (1 - t - ... - t^m)` to `depth`.
fn coxeter_series(m: usize, depth: usize) -> Vec<u64> {
    let mut num = vec![0u64; depth + 1];
    for i in 0..m {
        if i <= depth {
            num[i] += 1;
        }
        if i + 1 <= depth {
            num[i + 1] += 1;
        }
    }
    let mut c = vec![0u64; depth + 1];
    for d in 0..=depth {
        let mut v = num[d];
        for k in 1..=m.min(d) {
            v += c[d - k];
        }
        c[d] = v;
    }
    c
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// `scan <m> <depth> <maxleg> [seed]`: the translation census at every coprime leg ratio
/// `a:b` with `1 <= a, b <= maxleg`, grouped into distinct profiles.  This is how the
/// leg-dependence claims of `rem:cylcensus-status` and `rem:samples` are measured.
fn scan(m: u64, depth: usize, maxleg: i64, seed: u64) {
    let prime = find_prime(seed);
    unsafe {
        P = prime;
    }
    let g = generator();
    let i_unit = powm(g, (prime - 1) / 4);
    assert_eq!(mul(i_unit, i_unit), fp(-1), "i^2 != -1");
    let zeta = powm(g, (prime - 1) / (2 * m));
    assert_eq!(powm(zeta, 2 * m), Fp(1), "zeta_2m is not a 2m-th root");
    assert_ne!(powm(zeta, m), Fp(1), "zeta_2m is not primitive");
    println!(
        "=== scan m={} depth={} legs up to {}  p={} ===",
        m, depth, maxleg, prime
    );
    let mut profiles: Vec<(Vec<usize>, Vec<(i64, i64)>)> = Vec::new();
    let mut count = 0usize;
    for a in 1..=maxleg {
        for b in 1..=maxleg {
            if gcd(a, b) != 1 {
                continue;
            }
            let sg = stratum_gens(m, a, b, zeta, i_unit);
            let (_, tr) = match bfs(&sg, depth) {
                Some(x) => x,
                None => continue,
            };
            let row: Vec<usize> = (6..=depth).step_by(2).map(|d| tr[d]).collect();
            count += 1;
            match profiles.iter_mut().find(|(r, _)| *r == row) {
                Some((_, ls)) => ls.push((a, b)),
                None => profiles.push((row, vec![(a, b)])),
            }
        }
    }
    profiles.sort_by_key(|(_, ls)| std::cmp::Reverse(ls.len()));
    println!("  {} coprime leg samples, {} distinct profiles", count, profiles.len());
    for (r, ls) in &profiles {
        let shown: Vec<(i64, i64)> = ls.iter().take(8).cloned().collect();
        println!(
            "    {:?}   {} samples, e.g. {:?}{}",
            r,
            ls.len(),
            shown,
            if ls.len() > 8 { " ..." } else { "" }
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "scan" {
        let m: u64 = args[2].parse().unwrap();
        let depth: usize = args[3].parse().unwrap();
        let maxleg: i64 = args[4].parse().unwrap();
        let seed: u64 = if args.len() > 5 { args[5].parse().unwrap() } else { 1_000_000_000 };
        scan(m, depth, maxleg, seed);
        return;
    }
    let seeds: Vec<u64> = if args.len() > 1 {
        args[1..].iter().map(|s| s.parse().unwrap()).collect()
    } else {
        vec![1_000_000_000, 2_305_843_009_213_000_000]
    };

    // leg samples a:b used throughout
    let legs: [(i64, i64); 6] = [(1, 1), (1, 2), (1, 3), (2, 3), (3, 4), (3, 5)];

    for seed in seeds {
        let prime = find_prime(seed);
        unsafe {
            P = prime;
        }
        let g = generator();
        let i_unit = powm(g, (prime - 1) / 4);
        assert_eq!(mul(i_unit, i_unit), fp(-1), "i^2 != -1");
        println!("================ p = {} ================", prime);

        // ---------------- (A) onset table -----------------------------------------
        const DA: usize = 14;
        println!("\n=== (A) onset d*(m) and deficit delta(m) against the Coxeter series ===");
        for (pn, pd, qn, qd) in [(2i64, 7i64, 3i64, 5i64), (1, 3, 1, 2)] {
            let gg = generic_gens(pn, pd, qn, qd);
            if let Some((sph, _)) = bfs(&gg, DA) {
                println!(
                    "  generic ({}/{}, {}/{}) spheres 1..{}: {:?}",
                    pn,
                    pd,
                    qn,
                    qd,
                    DA,
                    &sph[1..=DA]
                );
            }
        }
        println!("     legs a:b        d*   delta   deficit at depth 12   spheres 1..14");
        for m in 2u64..=12 {
            let w = coxeter_series(m as usize, DA);
            let zeta = powm(g, (prime - 1) / (2 * m));
            assert_eq!(powm(zeta, 2 * m), Fp(1), "zeta_2m is not a 2m-th root");
            assert_ne!(powm(zeta, m), Fp(1), "zeta_2m is not primitive");
            let mut best: Option<(usize, i64)> = None;
            for (a, b) in legs {
                if a == b && m == 2 {
                    continue; // apex pi/2 with equal legs is the isoceles right triangle
                }
                let sg = stratum_gens(m, a, b, zeta, i_unit);
                let (sph, _) = match bfs(&sg, DA) {
                    Some(x) => x,
                    None => {
                        println!("  m={:2} legs {}:{}  ball cap exceeded", m, a, b);
                        continue;
                    }
                };
                let dstar = (1..=DA).find(|&d| (sph[d] as u64) < w[d]);
                let delta = dstar.map(|d| w[d] as i64 - sph[d] as i64);
                let def12 = w[12] as i64 - sph[12] as i64;
                println!(
                    "  m={:2} legs {}:{}      {:?}   {:?}      {:5}            {:?}",
                    m,
                    a,
                    b,
                    dstar,
                    delta,
                    def12,
                    &sph[1..=DA]
                );
                if let (Some(d), Some(dl)) = (dstar, delta) {
                    // the stratum-generic onset is the latest one seen, with the least
                    // deficit there; special samples can only add relations
                    best = Some(match best {
                        None => (d, dl),
                        Some((bd, bdl)) => {
                            if d > bd || (d == bd && dl < bdl) {
                                (d, dl)
                            } else {
                                (bd, bdl)
                            }
                        }
                    });
                }
            }
            println!("  m={:2} STRATUM-GENERIC (latest onset over the samples): {:?}", m, best);
        }

        // ---------------- (B) translation census to depth 18 ----------------------
        const DB: usize = 18;
        println!("\n=== (B) translations by word length, depth {} ===", DB);
        for (pn, pd, qn, qd) in [(2i64, 7i64, 3i64, 5i64), (1, 3, 1, 2)] {
            let gg = generic_gens(pn, pd, qn, qd);
            if let Some((_, tr)) = bfs(&gg, DB) {
                let row: Vec<usize> = (6..=DB).step_by(2).map(|d| tr[d]).collect();
                let odd: usize = (1..=DB).step_by(2).map(|d| tr[d]).sum();
                println!(
                    "  generic ({}/{}, {}/{}): lengths 6,8,..,18 = {:?}   (odd lengths: {})",
                    pn, pd, qn, qd, row, odd
                );
            }
        }
        for m in [3u64, 4, 5, 6, 7, 9, 11, 12] {
            let zeta = powm(g, (prime - 1) / (2 * m));
            let mut profiles: Vec<(Vec<usize>, Vec<(i64, i64)>)> = Vec::new();
            for (a, b) in legs {
                let sg = stratum_gens(m, a, b, zeta, i_unit);
                let (_, tr) = match bfs(&sg, DB) {
                    Some(x) => x,
                    None => {
                        println!("  m={:2} legs {}:{}  ball cap exceeded", m, a, b);
                        continue;
                    }
                };
                let row: Vec<usize> = (6..=DB).step_by(2).map(|d| tr[d]).collect();
                println!("  m={:2} legs {}:{}   lengths 6,8,..,18 = {:?}", m, a, b, row);
                match profiles.iter_mut().find(|(r, _)| *r == row) {
                    Some((_, ls)) => ls.push((a, b)),
                    None => profiles.push((row, vec![(a, b)])),
                }
            }
            println!(
                "  m={:2} DISTINCT PROFILES over the {} samples: {}",
                m,
                legs.len(),
                profiles.len()
            );
            for (r, ls) in &profiles {
                println!("        {:?}   at legs {:?}", r, ls);
            }
        }
        println!();
    }
}
