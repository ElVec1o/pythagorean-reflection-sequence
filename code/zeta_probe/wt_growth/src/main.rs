// wt_growth -- sphere sizes u_d(T) of the right-triangle reflection group W_T
// in its three side reflections, for a hypotenuse whose doubled angle w = C + iS
// has minimal polynomial  c t^2 - e t + c  (so C = e/(2c)).  The (1,2) triangle
// is (c,e) = (5,-6); c = 2,3,4 give non-rational-leg "laboratory" shapes with
// the same algebraic structure (both extreme coefficients of mu non-units).
//
// Element encoding (exact linear part, translation mod p):
//   linear part  z -> sigma * w^m * conj^eps(z)  stored EXACTLY as (sigma, m, eps)
//   (faithful because w is not a root of unity and -1 is not a power of w);
//   translation  (x, y) reduced mod a prime p < 2^58 (5, 2c invertible; sqrt(4c^2-e^2) exists).
// Packed u128:  x << 70 | y << 12 | eps<<11 | sigmabit<<10 | (m+512).
// Reduction mod p can only IDENTIFY distinct elements (never separate equal ones),
// so every printed u_d is a LOWER bound for the true value; run at two primes.
//
// BFS: Cayley graph is bipartite (det = (-1)^length), so S_{d+1} = N(S_d) \ S_{d-1}.
// Only S_{d-1}, S_d kept (sorted Vec<u128>); S_{d+1} built bucket by bucket
// (bucket = top bits of key, so sorted order == bucket order).
//
// usage: wt_growth <c> <e> <dmax> <prime_index> <cap_mb> <outfile>

use rayon::prelude::*;
use std::io::Write;
use std::time::Instant;

#[repr(C)]
struct RUsage { tv: [i64; 4], rest: [i64; 14] }
extern "C" { fn getrusage(who: i32, r: *mut RUsage) -> i32; }
fn maxrss_mb() -> f64 {
    let mut r = RUsage { tv: [0; 4], rest: [0; 14] };
    unsafe { getrusage(0, &mut r); }
    r.rest[0] as f64 / (1024.0 * 1024.0) // macOS: bytes
}

fn mulm(a: u64, b: u64, p: u64) -> u64 { ((a as u128 * b as u128) % p as u128) as u64 }
fn powm(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1u64; a %= p;
    while e > 0 { if e & 1 == 1 { r = mulm(r, a, p); } a = mulm(a, a, p); e >>= 1; }
    r
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { if n % q == 0 { return n == q; } }
    let mut d = n - 1; let mut s = 0; while d % 2 == 0 { d /= 2; s += 1; }
    'w: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = powm(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s - 1 { x = mulm(x, x, n); if x == n - 1 { continue 'w; } }
        return false;
    }
    true
}
fn md(v: i64, p: u64) -> u64 { let r = v.rem_euclid(p as i64); r as u64 }

#[derive(Clone, Copy)]
struct Gen { sig: i32, m: i32, a: u64, b: u64, cc: u64, d: u64, tx: u64, ty: u64 }

const MASK58: u128 = (1u128 << 58) - 1;

#[inline]
fn unpack(k: u128) -> (i32, i32, u32, u64, u64) {
    let lab = (k & 0xFFF) as u32;
    let m = (lab & 0x3FF) as i32 - 512;
    let sig = if (lab >> 10) & 1 == 1 { -1 } else { 1 };
    let eps = (lab >> 11) & 1;
    let y = ((k >> 12) & MASK58) as u64;
    let x = ((k >> 70) & MASK58) as u64;
    (sig, m, eps, x, y)
}
#[inline]
fn pack(sig: i32, m: i32, eps: u32, x: u64, y: u64) -> u128 {
    let lab = ((eps as u128) << 11) | ((if sig < 0 { 1u128 } else { 0 }) << 10) | ((m + 512) as u128);
    ((x as u128) << 70) | ((y as u128) << 12) | lab
}
#[inline]
fn apply(g: &Gen, k: u128, p: u64) -> u128 {
    let (sig, m, eps, x, y) = unpack(k);
    // every generator is orientation-reversing: z -> sig_g w^{m_g} conj(z) + t_g
    let nsig = g.sig * sig;
    let nm = g.m - m;
    let neps = eps ^ 1;
    let nx = ((g.a as u128 * x as u128 + g.b as u128 * y as u128 + g.tx as u128) % p as u128) as u64;
    let ny = ((g.cc as u128 * x as u128 + g.d as u128 * y as u128 + g.ty as u128) % p as u128) as u64;
    pack(nsig, nm, neps, nx, ny)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 7 { eprintln!("usage: wt_growth <c> <e> <dmax> <prime_index> <cap_mb> <outfile>"); std::process::exit(2); }
    let c: i64 = a[1].parse().unwrap();
    let e: i64 = a[2].parse().unwrap();
    let dmax: usize = a[3].parse().unwrap();
    let pidx: usize = a[4].parse().unwrap();
    let cap_mb: f64 = a[5].parse().unwrap();
    let out = &a[6];
    let disc = 4 * c * c - e * e;
    assert!(disc > 0, "need |e| < 2c");
    assert!(dmax < 500);
    // prime p = 3 mod 4, p < 2^58, disc a QR, p coprime to 2c
    let mut p: u64 = (1u64 << 58) - 1;
    let mut found = 0usize;
    loop {
        p -= 1;
        if p % 4 != 3 || !is_prime(p) { continue; }
        if (2 * c as u64) % p == 0 { continue; }
        let dm = md(disc, p);
        if powm(dm, (p - 1) / 2, p) != 1 { continue; }
        if found == pidx { break; }
        found += 1;
    }
    let sq = powm(md(disc, p), (p + 1) / 4, p);
    assert_eq!(mulm(sq, sq, p), md(disc, p));
    let inv2c = powm(md(2 * c, p), p - 2, p);
    let cm = mulm(md(e, p), inv2c, p);            // C = e/(2c)
    let sm = (p - mulm(sq, inv2c, p)) % p;         // S = -sqrt(disc)/(2c)
    let one = 1u64;
    // R_x: (x,y)->(x,-y);  R_y: (x,-y)->(-x,y);  R_h: [[C,S],[S,-C]] + (1-C, -S)
    let gens = [
        Gen { sig: 1, m: 0, a: 1, b: 0, cc: 0, d: p - 1, tx: 0, ty: 0 },
        Gen { sig: -1, m: 0, a: p - 1, b: 0, cc: 0, d: 1, tx: 0, ty: 0 },
        Gen { sig: 1, m: 1, a: cm, b: sm, cc: sm, d: (p - cm) % p, tx: (one + p - cm) % p, ty: (p - sm) % p },
    ];
    let kb: u32 = 6; // 64 buckets
    let nb: u128 = 1 << kb;
    let bucket = |k: u128| -> u128 { k >> (128 - kb) };

    let mut f = std::fs::File::create(out).unwrap();
    writeln!(f, "# wt_growth c={} e={} p={} (index {}) dmax={}", c, e, p, pidx, dmax).unwrap();
    writeln!(f, "# d u_d translations_in_sphere samesphere_hits secs maxrss_mb").unwrap();
    println!("# c={} e={} p={}", c, e, p);
    let t0 = Instant::now();
    let mut prev: Vec<u128> = Vec::new();
    let mut cur: Vec<u128> = vec![pack(1, 0, 0, 0, 0)];
    writeln!(f, "0 1 1 0 0.0 {:.0}", maxrss_mb()).unwrap();
    let mut ratio = 3.0f64;
    let cap_bytes = cap_mb * 1024.0 * 1024.0;
    for d in 1..=dmax {
        let last = d == dmax;
        let est_next = (cur.len() as f64 * ratio.min(3.0) * 1.04) as usize + 1024;
        let bucket_buf = (3.0 * cur.len() as f64 / nb as f64 * 1.3) as usize + 1024;
        let proj = 16.0 * (prev.len() + cur.len() + if last { 0 } else { est_next } + 2 * bucket_buf) as f64;
        if proj > cap_bytes {
            println!("GUARD: projected {:.0} MB > cap {:.0} MB at d={}; stopping.", proj / 1048576.0, cap_mb, d);
            writeln!(f, "# GUARD stop at d={} projected {:.0} MB", d, proj / 1048576.0).unwrap();
            break;
        }
        let mut next: Vec<u128> = if last { Vec::new() } else { Vec::with_capacity(est_next) };
        let mut count: u64 = 0;
        let mut trans: u64 = 0;
        let mut hits: u64 = 0;
        for b in 0..nb {
            let mut cand: Vec<u128> = cur
                .par_iter()
                .flat_map_iter(|&h| gens.iter().map(move |g| apply(g, h, p)))
                .filter(|&k| bucket(k) == b)
                .collect();
            cand.par_sort_unstable();
            cand.dedup();
            let plo = prev.partition_point(|&k| bucket(k) < b);
            let phi = prev.partition_point(|&k| bucket(k) <= b);
            let clo = cur.partition_point(|&k| bucket(k) < b);
            let chi = cur.partition_point(|&k| bucket(k) <= b);
            let ps = &prev[plo..phi];
            let cs = &cur[clo..chi];
            let (mut i, mut j) = (0usize, 0usize);
            for &k in cand.iter() {
                while i < ps.len() && ps[i] < k { i += 1; }
                if i < ps.len() && ps[i] == k { continue; }
                while j < cs.len() && cs[j] < k { j += 1; }
                if j < cs.len() && cs[j] == k { hits += 1; continue; }
                count += 1;
                if (k & 0xFFF) as u32 == 512 { trans += 1; }
                if !last {
                    if next.len() == next.capacity() { next.reserve_exact(1 << 20); }
                    next.push(k);
                }
            }
        }
        let rss = maxrss_mb();
        let secs = t0.elapsed().as_secs_f64();
        println!("d={:3} u={:12} trans={:9} hits={} t={:.1}s rss={:.0}MB", d, count, trans, hits, secs, rss);
        writeln!(f, "{} {} {} {} {:.1} {:.0}", d, count, trans, hits, secs, rss).unwrap();
        f.flush().unwrap();
        if rss > cap_mb { println!("GUARD: maxrss {:.0} MB > cap; stopping.", rss); break; }
        if last { break; }
        ratio = next.len() as f64 / cur.len() as f64;
        prev = cur;
        cur = next;
    }
}
