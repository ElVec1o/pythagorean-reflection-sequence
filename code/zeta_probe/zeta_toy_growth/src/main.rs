// zeta_toy_growth -- sphere sizes of the toy group
//     H_f = M_f  x|_t  Z,   M_f = Z[t, 1/t] / (c t^2 - e t + c),
// in the generating set {a = translation by 1, r = the shift (multiplication by zeta)}.
// zeta = root of c t^2 - e t + c (|zeta| = 1 when |e| < 2c).
//   (1,2) triangle:  (c,e) = (5, 6)  -> zeta = (3+4i)/5   [task's convention]
//                    (c,e) = (5,-6)  -> zeta = (-3+4i)/5  [wt_growth's w]
//   pilot shape:     (c,e) = (2, 1)  -> zeta = (1+i sqrt15)/4
//
// Group law (x,k)(y,l) = (x + zeta^k y, k+l). Right multiplication:
//   a^{+-1}: (x,k) -> (x +- zeta^k, k);   r^{+-1}: (x,k) -> (x, k+-1).
//
// EXACT arithmetic, two independent encodings of x:
//   mode "basis": x = (A + B zeta)/c^s in the Q-basis (1, zeta), (A,B) in Z^2,
//                 s >= 0 minimal (canonical: never c|A and c|B with s>0).
//                 c zeta^2 = e zeta - c  gives the recursions for zeta^{+-k}.
//   mode "gauss": only for c = 5, e = +-6: x = (u + v i)/5^m, m minimal.
// All arithmetic is i128 with an explicit overflow check before storing in i64;
// the run aborts (never wraps) if a numerator leaves i64.
//
// BFS: S_{d+1} = N(S_d) \ (S_d u S_{d-1}) (valid in any Cayley graph with a
// symmetric generating set). Sets are sorted Vec<El>, keyed (bucket, ...);
// S_{d+1} is built bucket by bucket so the transient buffer is ~ 4|S_d|/64.
// Memory guard INSIDE the tool: projected bytes and measured maxrss vs cap_mb.
//
// usage: zeta_toy_growth <c> <e> <dmax> <cap_mb> <outfile> [basis|gauss] [fast [passes]]
//   ("basis fast" = Klein-orbit / u128 mode, see mod fast at the end)
// output per depth: d  u_d  (#elements of S_d with k=0)  (max |k|)  secs  maxrss_mb

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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct El { sk: u64, a: i64, b: i64 } // sk = bucket<<56 | s<<40 | (k+2^31)

const KOFF: i64 = 1 << 31;
const KB: u32 = 6;
const NB: u64 = 1 << KB;

#[inline]
fn mix(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}
#[inline]
fn mk(a: i128, b: i128, s: u32, k: i64) -> El {
    assert!(a >= i64::MIN as i128 && a <= i64::MAX as i128 && b >= i64::MIN as i128 && b <= i64::MAX as i128,
            "OVERFLOW: numerator leaves i64 (a={}, b={}, s={}, k={})", a, b, s, k);
    assert!(s < 256);
    let low = ((s as u64) << 40) | ((k + KOFF) as u64);
    let h = mix(mix(a as u64 ^ 0x9e3779b97f4a7c15) ^ (b as u64).rotate_left(17) ^ low.rotate_left(33));
    El { sk: ((h >> (64 - KB)) << 56) | low, a: a as i64, b: b as i64 }
}
#[inline]
fn un(x: &El) -> (i128, i128, u32, i64) {
    let s = ((x.sk >> 40) & 0xFF) as u32;
    let k = (x.sk & 0xFFFF_FFFF) as i64 - KOFF;
    (x.a as i128, x.b as i128, s, k)
}
#[inline]
fn bucket(x: &El) -> u64 { x.sk >> 56 }

// canonical reduction: divide numerators by q while both divisible and s>0
#[inline]
fn red(mut a: i128, mut b: i128, mut s: u32, q: i128) -> (i128, i128, u32) {
    while s > 0 && a % q == 0 && b % q == 0 { a /= q; b /= q; s -= 1; }
    (a, b, s)
}
#[inline]
fn pw(q: i128, n: u32) -> i128 {
    let mut r: i128 = 1;
    for _ in 0..n { r = r.checked_mul(q).expect("OVERFLOW in power"); }
    r
}

struct Ctx { q: i128, zp: Vec<(i128, i128, u32)>, zn: Vec<(i128, i128, u32)> } // zeta^k, k>=0 / k<=0
impl Ctx {
    fn zk(&self, k: i64) -> (i128, i128, u32) {
        if k >= 0 { self.zp[k as usize] } else { self.zn[(-k) as usize] }
    }
    // x + sg * zeta^k
    #[inline]
    fn add(&self, x: &El, sg: i128) -> El {
        let (a, b, s, k) = un(x);
        let (p, qq, t) = self.zk(k);
        let m = s.max(t);
        let fa = pw(self.q, m - s);
        let fb = pw(self.q, m - t);
        let na = a.checked_mul(fa).and_then(|v| v.checked_add(sg * p.checked_mul(fb)?)).expect("OVERFLOW add");
        let nb = b.checked_mul(fa).and_then(|v| v.checked_add(sg * qq.checked_mul(fb)?)).expect("OVERFLOW add");
        let (na, nb, m) = red(na, nb, m, self.q);
        mk(na, nb, m, k)
    }
    #[inline]
    fn shift(&self, x: &El, dk: i64) -> El {
        let (a, b, s, k) = un(x);
        mk(a, b, s, k + dk)
    }
}

fn main() {
    let av: Vec<String> = std::env::args().collect();
    if av.len() < 6 { eprintln!("usage: zeta_toy_growth <c> <e> <dmax> <cap_mb> <outfile> [basis|gauss]"); std::process::exit(2); }
    let c: i128 = av[1].parse().unwrap();
    let e: i128 = av[2].parse().unwrap();
    let dmax: usize = av[3].parse().unwrap();
    let cap_mb: f64 = av[4].parse().unwrap();
    let out = &av[5];
    let mode = if av.len() > 6 { av[6].clone() } else { "basis".to_string() };
    if !(av.len() > 6 && av[6] == "lin") { assert!(4 * c * c - e * e > 0, "need |e| < 2c"); }
    assert!(dmax < 200);
    let kmax = dmax + 2;
    let mut zp = Vec::new();
    let mut zn = Vec::new();
    let q: i128;
    if mode == "basis" {
        q = c;
        // zeta^k = (P + Q zeta)/c^s
        let (mut p, mut qq, mut s) = (1i128, 0i128, 0u32);
        for _ in 0..=kmax {
            zp.push((p, qq, s));
            // times zeta: c*(P+Q zeta) zeta = -cQ + (cP + eQ) zeta
            let np = -c * qq; let nq = c * p + e * qq;
            let r = red(np, nq, s + 1, c); p = r.0; qq = r.1; s = r.2;
        }
        let (mut p, mut qq, mut s) = (1i128, 0i128, 0u32);
        for _ in 0..=kmax {
            zn.push((p, qq, s));
            // times zeta^{-1} = e/c - zeta: c*(P+Q zeta)/zeta = (eP + cQ) - cP zeta
            let np = e * p + c * qq; let nq = -c * p;
            let r = red(np, nq, s + 1, c); p = r.0; qq = r.1; s = r.2;
        }
    } else if mode == "gauss" {
        assert!(c == 5 && (e == 6 || e == -6), "gauss mode only for (5,+-6)");
        q = 5;
        let re = e / 2; // zeta = (re + 4i)/5, re = +-3
        let (mut u, mut v, mut s) = (1i128, 0i128, 0u32);
        for _ in 0..=kmax {
            zp.push((u, v, s));
            let nu = u * re - v * 4; let nv = u * 4 + v * re;
            let r = red(nu, nv, s + 1, 5); u = r.0; v = r.1; s = r.2;
        }
        let (mut u, mut v, mut s) = (1i128, 0i128, 0u32);
        for _ in 0..=kmax {
            zn.push((u, v, s));
            let nu = u * re + v * 4; let nv = -u * 4 + v * re; // times conj(zeta)
            let r = red(nu, nv, s + 1, 5); u = r.0; v = r.1; s = r.2;
        }
    } else if mode == "lin" {
        // CONTROL family: degree-1 module M = Z[t,1/t]/(c t - e) = Z[1/ce], zeta = e/c,
        // H = Z[1/ce] x|_{e/c} Z  (c=1: BS(1,e); gcd(c,e)=1, c,e>1: metabelian BS(c,e) quotient).
        // x = A/(ce)^s, B = 0 throughout; the "basis" arithmetic with q = ce applies verbatim.
        // (the |e|<2c assertion is irrelevant here and was skipped for this mode)
        q = c * e;
        for k in 0..=kmax as u32 {
            zp.push(red(pw(e, 2 * k), 0, k, q)); // (e/c)^k = e^{2k}/(ce)^k
            zn.push(red(pw(c, 2 * k), 0, k, q)); // (c/e)^k = c^{2k}/(ce)^k
        }
    } else { panic!("mode must be basis, gauss or lin"); }
    let ctx = Ctx { q, zp, zn };
    if av.len() > 7 && av[7] == "fast" {
        assert!(mode == "basis");
        let passes: u32 = if av.len() > 8 { av[8].parse().unwrap() } else { 8 };
        fast::run(&ctx, c, e, dmax, cap_mb, out, passes);
        return;
    }

    let mut f = std::fs::File::create(out).unwrap();
    writeln!(f, "# zeta_toy_growth c={} e={} mode={} dmax={} (generators a=translation by 1, r=shift)", c, e, mode, dmax).unwrap();
    writeln!(f, "# d u_d k0_in_sphere max_abs_k secs maxrss_mb").unwrap();
    println!("# c={} e={} mode={}", c, e, mode);
    let t0 = Instant::now();
    let mut prev: Vec<El> = Vec::new();
    let mut cur: Vec<El> = vec![mk(0, 0, 0, 0)];
    writeln!(f, "0 1 1 0 0.0 {:.0}", maxrss_mb()).unwrap();
    let cap_bytes = cap_mb * 1024.0 * 1024.0;
    let esz = std::mem::size_of::<El>() as f64;
    let mut ratio = 3.0f64;
    for d in 1..=dmax {
        let last = d == dmax;
        let est_next = (cur.len() as f64 * ratio.min(3.0) * 1.05) as usize + 1024;
        let bucket_buf = (4.0 * cur.len() as f64 / NB as f64 * 1.3) as usize + 1024;
        let proj = esz * (prev.len() + cur.len() + if last { 0 } else { est_next } + 2 * bucket_buf) as f64;
        if proj > cap_bytes {
            println!("GUARD: projected {:.0} MB > cap {:.0} MB at d={}; stopping.", proj / 1048576.0, cap_mb, d);
            writeln!(f, "# GUARD stop at d={} projected {:.0} MB", d, proj / 1048576.0).unwrap();
            break;
        }
        let mut next: Vec<El> = if last { Vec::new() } else { Vec::with_capacity(est_next) };
        let (mut count, mut k0, mut kmx) = (0u64, 0u64, 0i64);
        for bk in 0..NB {
            let mut cand: Vec<El> = cur
                .par_iter()
                .flat_map_iter(|h| [ctx.add(h, 1), ctx.add(h, -1), ctx.shift(h, 1), ctx.shift(h, -1)].into_iter())
                .filter(|x| bucket(x) == bk)
                .collect();
            cand.par_sort_unstable();
            cand.dedup();
            let plo = prev.partition_point(|x| bucket(x) < bk);
            let phi = prev.partition_point(|x| bucket(x) <= bk);
            let clo = cur.partition_point(|x| bucket(x) < bk);
            let chi = cur.partition_point(|x| bucket(x) <= bk);
            let ps = &prev[plo..phi];
            let cs = &cur[clo..chi];
            let (mut i, mut j) = (0usize, 0usize);
            for x in cand.iter() {
                while i < ps.len() && ps[i] < *x { i += 1; }
                if i < ps.len() && ps[i] == *x { continue; }
                while j < cs.len() && cs[j] < *x { j += 1; }
                if j < cs.len() && cs[j] == *x { continue; }
                count += 1;
                let k = un(x).3;
                if k == 0 { k0 += 1; }
                if k.abs() > kmx { kmx = k.abs(); }
                if !last {
                    if next.len() == next.capacity() { next.reserve_exact(1 << 20); }
                    next.push(*x);
                }
            }
        }
        let rss = maxrss_mb();
        let secs = t0.elapsed().as_secs_f64();
        println!("d={:3} u={:12} k0={:10} kmax={} t={:.1}s rss={:.0}MB", d, count, k0, kmx, secs, rss);
        writeln!(f, "{} {} {} {} {:.1} {:.0}", d, count, k0, kmx, secs, rss).unwrap();
        f.flush().unwrap();
        if rss > cap_mb { println!("GUARD: maxrss {:.0} MB > cap; stopping.", rss); writeln!(f, "# GUARD rss stop").unwrap(); break; }
        if last { break; }
        ratio = next.len() as f64 / cur.len().max(1) as f64;
        prev = cur;
        cur = next;
    }
}

// ---------------------------------------------------------------------------
// fast mode: orbit representatives under the Klein group G = {id, nu, sigma, nu sigma}
// of automorphisms of H preserving {a^+-1, r^+-1}:
//   nu(x,k) = (-x, k)          (a <-> a^-1, r fixed)
//   sigma(x,k) = (conj x, -k)  (zeta -> zeta^-1 is a ring automorphism of M since
//                               c t^2 - e t + c is palindromic; r <-> r^-1, a fixed).
// Spheres are G-invariant and N(g(x)) = g(N(x)), so BFS on orbit representatives
// (min packed key over the orbit) is exact; u_d = sum of orbit sizes.
// Element packed EXACTLY and bijectively into u128:
//   raw = (A+2^56) << 71 | (B+2^56) << 14 | s << 8 | (k+128),  |A|,|B| < 2^56, s < 64, |k| < 128
//   key = MIX(raw), MIX an invertible permutation of u128 (xorshift, odd multiply, xorshift)
// so the top bits of key are pseudo-random buckets and sorting by key is exact.
mod fast {
    use super::*;
    const KM: u128 = 0x9e3779b97f4a7c15_f39cc0605cedc835u128 | 1;
    fn kinv() -> u128 { let mut x = KM; for _ in 0..8 { x = x.wrapping_mul(2u128.wrapping_sub(KM.wrapping_mul(x))); } assert_eq!(x.wrapping_mul(KM), 1); x }
    #[inline] fn xs(x: u128) -> u128 { x ^ (x >> 64) }
    #[inline] fn mixk(x: u128) -> u128 { xs(xs(x).wrapping_mul(KM)) }
    #[inline] fn unmix(y: u128, ki: u128) -> u128 { xs(xs(y).wrapping_mul(ki)) }
    const OFF: i128 = 1 << 56;
    #[inline]
    fn enc(a: i128, b: i128, s: u32, k: i64) -> u128 {
        assert!(a > -OFF && a < OFF && b > -OFF && b < OFF, "OVERFLOW: numerator >= 2^56 (a={}, b={}, s={}, k={})", a, b, s, k);
        assert!(s < 64 && k > -128 && k < 128, "OVERFLOW s/k");
        mixk(((a + OFF) as u128) << 71 | ((b + OFF) as u128) << 14 | (s as u128) << 8 | ((k + 128) as u128))
    }
    #[inline]
    fn dec(y: u128, ki: u128) -> (i128, i128, u32, i64) {
        let r = unmix(y, ki);
        let a = (r >> 71) as i128 - OFF;
        let b = ((r >> 14) & ((1u128 << 57) - 1)) as i128 - OFF;
        let s = ((r >> 8) & 63) as u32;
        let k = (r & 255) as i64 - 128;
        (a, b, s, k)
    }
    struct F<'a> { ctx: &'a Ctx, c: i128, e: i128, ki: u128 }
    impl<'a> F<'a> {
        // the four orbit images, packed
        #[inline]
        fn orbit(&self, a: i128, b: i128, s: u32, k: i64) -> [u128; 4] {
            // conj(A + B zeta)/c^s = A + B(e/c - zeta) = ((cA + eB) - cB zeta)/c^{s+1}
            let (ca, cb, cs) = red(self.c * a + self.e * b, -self.c * b, s + 1, self.c);
            [enc(a, b, s, k), enc(-a, -b, s, k), enc(ca, cb, cs, -k), enc(-ca, -cb, cs, -k)]
        }
        #[inline]
        fn canon(&self, a: i128, b: i128, s: u32, k: i64) -> u128 {
            let o = self.orbit(a, b, s, k);
            o[0].min(o[1]).min(o[2]).min(o[3])
        }
        #[inline]
        fn osize(&self, y: u128) -> (u64, i64) {
            let (a, b, s, k) = dec(y, self.ki);
            let mut o = self.orbit(a, b, s, k);
            o.sort_unstable();
            let mut n = 1u64;
            for i in 1..4 { if o[i] != o[i - 1] { n += 1; } }
            (n, k)
        }
        #[inline]
        fn nbrs(&self, y: u128) -> [u128; 4] {
            let (a, b, s, k) = dec(y, self.ki);
            let (p, qq, t) = self.ctx.zk(k);
            let m = s.max(t);
            let fa = pw(self.c, m - s);
            let fb = pw(self.c, m - t);
            let a1 = a.checked_mul(fa).expect("OVF"); let b1 = b.checked_mul(fa).expect("OVF");
            let p1 = p.checked_mul(fb).expect("OVF"); let q1 = qq.checked_mul(fb).expect("OVF");
            let (x1, y1, s1) = red(a1 + p1, b1 + q1, m, self.c);
            let (x2, y2, s2) = red(a1 - p1, b1 - q1, m, self.c);
            [self.canon(x1, y1, s1, k), self.canon(x2, y2, s2, k), self.canon(a, b, s, k + 1), self.canon(a, b, s, k - 1)]
        }
    }
    pub fn run(ctx: &Ctx, c: i128, e: i128, dmax: usize, cap_mb: f64, out: &str, passes: u32) {
        let ki = kinv();
        let fz = F { ctx, c, e, ki };
        // self-test of the packing
        for &(a, b, s, k) in &[(0i128, 0i128, 0u32, 0i64), (-5, 17, 3, -9), (OFF - 1, -(OFF - 1), 63, 127), (-(OFF - 1), OFF - 1, 0, -127)] {
            assert_eq!(dec(enc(a, b, s, k), ki), (a, b, s, k));
        }
        let pb = passes.trailing_zeros();
        assert!(passes.is_power_of_two() && pb <= 8);
        let pass_of = |y: u128| -> u32 { if pb == 0 { 0 } else { (y >> (128 - pb)) as u32 } };
        let mut f = std::fs::File::create(out).unwrap();
        writeln!(f, "# zeta_toy_growth FAST (Klein-orbit reps, u128 exact packing) c={} e={} dmax={} passes={}", c, e, dmax, passes).unwrap();
        writeln!(f, "# d u_d k0_in_sphere max_abs_k reps secs maxrss_mb").unwrap();
        println!("# FAST c={} e={}", c, e);
        let t0 = Instant::now();
        let mut prev: Vec<u128> = Vec::new();
        let mut cur: Vec<u128> = vec![fz.canon(0, 0, 0, 0)];
        writeln!(f, "0 1 1 0 1 0.0 {:.0}", maxrss_mb()).unwrap();
        let cap_bytes = cap_mb * 1024.0 * 1024.0;
        let mut ratio = 3.0f64;
        for d in 1..=dmax {
            let last = d == dmax;
            let est_next = (cur.len() as f64 * ratio.min(3.0) * 1.05) as usize + 1024;
            // transient per pass: rayon's unindexed collect + dedup + filter measured at
            // ~10x the raw candidate buffer (a d=21 run at 16 passes hit 3.0 GB against a
            // 1.4 GB projection with factor 2, and 2.35 GB with factor 8); use 12x.
            let buf = (4.0 * cur.len() as f64 / passes as f64) as usize + 1024;
            let proj = 16.0 * (prev.len() + cur.len() + if last { 0 } else { est_next } + 12 * buf) as f64;
            if proj > cap_bytes {
                println!("GUARD: projected {:.0} MB > cap {:.0} MB at d={}; stopping.", proj / 1048576.0, cap_mb, d);
                writeln!(f, "# GUARD stop at d={} projected {:.0} MB", d, proj / 1048576.0).unwrap();
                break;
            }
            let mut next: Vec<u128> = if last { Vec::new() } else { Vec::with_capacity(est_next) };
            let (mut count, mut k0, mut kmx, mut reps) = (0u64, 0u64, 0i64, 0u64);
            for ps_ in 0..passes {
                let mut cand: Vec<u128> = cur
                    .par_iter()
                    .flat_map_iter(|&h| fz.nbrs(h).into_iter())
                    .filter(|&y| pass_of(y) == ps_)
                    .collect();
                cand.par_sort_unstable();
                cand.dedup();
                let plo = prev.partition_point(|&y| pass_of(y) < ps_);
                let phi = prev.partition_point(|&y| pass_of(y) <= ps_);
                let clo = cur.partition_point(|&y| pass_of(y) < ps_);
                let chi = cur.partition_point(|&y| pass_of(y) <= ps_);
                let pv = &prev[plo..phi];
                let cv = &cur[clo..chi];
                // filter new ones in parallel via binary search
                let newv: Vec<u128> = cand.into_par_iter()
                    .filter(|y| pv.binary_search(y).is_err() && cv.binary_search(y).is_err())
                    .collect();
                let (cn, kn, km) = newv.par_iter().map(|&y| { let (n, k) = fz.osize(y); (n, if k == 0 { n } else { 0 }, k.abs()) })
                    .reduce(|| (0, 0, 0), |x, z| (x.0 + z.0, x.1 + z.1, x.2.max(z.2)));
                count += cn; k0 += kn; kmx = kmx.max(km); reps += newv.len() as u64;
                if !last { next.extend_from_slice(&newv); }
            }
            let rss = maxrss_mb();
            let secs = t0.elapsed().as_secs_f64();
            println!("d={:3} u={:14} k0={:12} kmax={} reps={} t={:.1}s rss={:.0}MB", d, count, k0, kmx, reps, secs, rss);
            writeln!(f, "{} {} {} {} {} {:.1} {:.0}", d, count, k0, kmx, reps, secs, rss).unwrap();
            f.flush().unwrap();
            if rss > cap_mb { println!("GUARD: maxrss {:.0} MB > cap; stopping.", rss); writeln!(f, "# GUARD rss stop").unwrap(); break; }
            if last { break; }
            ratio = next.len() as f64 / cur.len().max(1) as f64;
            prev = cur;
            cur = next;
        }
    }
}
