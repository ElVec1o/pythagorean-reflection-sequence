// wt_carry -- atom A2 (carry-window) for rational triangles W_T.
//
// Universal group W_univ in the lamp model (eps, dl, k, a_j) (paper1 thm:normal-form):
//   R_x: dl flip;  R_y: eps flip + dl flip;
//   R_h: dl=0 -> deposit +eps on edge k-1, k -= 1, dl=1;  dl=1 -> deposit -eps on edge k, k += 1, dl=0.
// W_T = W_univ / { A -> A + 2 mu_T f }, mu_T = c t^2 - e t + c   (B1, PROVED).
// Two lifts are equal in W_T  <=>  same (eps,dl,k) and A(zeta) = A'(zeta)   (Gauss; mu primitive).
// A(zeta) is computed EXACTLY in Z[1/c][zeta] as (X + Y zeta) / c^S with i128 numerators.
//
// BFS of the universal ball to radius D gives ell_univ exactly (ground truth).  For every
// W_T element g whose fiber meets the ball, ell_T(g) = min over the fiber's ball elements
// (an optimal lift has ell_univ = ell_T(g) <= ell_univ(any lift in ball) <= D).
// So: W_T spheres are exact to D, and for EVERY universal h of length <= D the optimal carry
//   f with  A_{h*} = A_h + 2 mu f  is found exactly.
//
// usage: wt_carry <c> <e> <D> <cap_mb> <outprefix>
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::time::Instant;

#[repr(C)]
struct RUsage { tv: [i64; 4], rest: [i64; 14] }
extern "C" { fn getrusage(who: i32, r: *mut RUsage) -> i32; }
fn maxrss_mb() -> f64 {
    let mut r = RUsage { tv: [0; 4], rest: [0; 14] };
    unsafe { getrusage(0, &mut r); }
    r.rest[0] as f64 / (1024.0 * 1024.0)
}

// packed element: [eps, dl, k, lo, a_lo .. a_hi]  (trimmed; empty lamps -> lo = 0)
type P = Box<[i8]>;

#[derive(Clone, Debug)]
struct E { eps: i32, dl: i32, k: i32, lo: i32, a: Vec<i32> }

fn dec(p: &[i8]) -> E {
    E { eps: p[0] as i32, dl: p[1] as i32, k: p[2] as i32, lo: p[3] as i32,
        a: p[4..].iter().map(|&x| x as i32).collect() }
}
fn enc(e: &E) -> P {
    let mut s = 0; let mut t = e.a.len();
    while s < t && e.a[s] == 0 { s += 1; }
    while t > s && e.a[t - 1] == 0 { t -= 1; }
    let lo = if s < t { e.lo + s as i32 } else { 0 };
    let mut v = vec![e.eps as i8, e.dl as i8, e.k as i8, lo as i8];
    for j in s..t { assert!(e.a[j].abs() < 127); v.push(e.a[j] as i8); }
    v.into_boxed_slice()
}
fn add_lamp(e: &mut E, j: i32, d: i32) {
    if e.a.is_empty() { e.lo = j; e.a.push(d); return; }
    while j < e.lo { e.a.insert(0, 0); e.lo -= 1; }
    while j >= e.lo + e.a.len() as i32 { e.a.push(0); }
    e.a[(j - e.lo) as usize] += d;
}
fn nbrs(p: &[i8]) -> [P; 3] {
    let e = dec(p);
    let mut x = e.clone(); x.dl = 1 - x.dl;
    let mut y = e.clone(); y.dl = 1 - y.dl; y.eps = -y.eps;
    let mut h = e.clone();
    if e.dl == 0 { add_lamp(&mut h, e.k - 1, e.eps); h.k -= 1; h.dl = 1; }
    else { add_lamp(&mut h, e.k, -e.eps); h.k += 1; h.dl = 0; }
    [enc(&x), enc(&y), enc(&h)]
}

// ---- closed form ell_univ = closed_lr + 2 cutset (Lean: metricAll / wordLength_eq_lRTrue_add_two_cTrue)
fn ftrav(k: i32, j: i32) -> i32 {
    if k > 0 && j >= 0 && j < k { 1 } else if k < 0 && j >= k && j < 0 { -1 } else { 0 }
}
fn dep(e: &E, j: i32) -> i32 {
    let i = j - e.lo; if i < 0 || i >= e.a.len() as i32 { 0 } else { e.a[i as usize] }
}
fn span(e: &E) -> (i32, i32) {
    let (mut lo, mut hi) = (0.min(e.k), 0.max(e.k));
    for (i, &v) in e.a.iter().enumerate() { if v != 0 { let j = e.lo + i as i32; lo = lo.min(j); hi = hi.max(j + 1); } }
    (lo, hi)
}
fn abphi(e: &E, s: i32) -> (i32, i32, i32) {
    let (mut al, mut be, mut phi) = (dep(e, s - 1), dep(e, s), ftrav(e.k, s - 1));
    if s == 0 { al -= 1; phi += 1; }
    if s == e.k { if e.dl == 0 { al += e.eps; phi -= 1; } else { be -= e.eps; } }
    (al, be, phi)
}
fn ell_univ(e: &E) -> i64 {
    let (lo, hi) = span(e);
    let mut t: i64 = 0;
    for j in lo..hi { let m = dep(e, j).abs().max(ftrav(e.k, j).abs()); t += if m == 0 { 2 } else { m } as i64; }
    for s in lo..=hi { let (a, b, p) = abphi(e, s); t += a.abs().max(b.abs()).max(p.abs()) as i64; }
    for s in lo..=hi {
        let interior = s > lo && s < hi;
        let bs = !interior && e.k == 0 && e.dl == 0 && s == 0 && lo == 0 && hi > 0;
        if !(interior || bs) { continue; }
        let (a, b, p) = abphi(e, s);
        if a == 0 && b == 0 && p == 0 { t += 2; }
    }
    t
}

// ---- exact zeta arithmetic: zeta^2 = (e zeta - c)/c.  value = (X + Y zeta)/c^S
struct Zeta { c: i128, s: u32, pw: HashMap<i32, (i128, i128)> }
impl Zeta {
    fn new(c: i64, e: i64, s: u32, jmax: i32) -> Zeta {
        let c = c as i128; let e = e as i128;
        let one = c.pow(s);
        let mut pw = HashMap::new();
        pw.insert(0, (one, 0));
        // times zeta: (X + Y z) z = X z + Y (e z - c)/c = -Y + (X + e Y / c) z
        let (mut x, mut y) = (one, 0i128);
        for j in 1..=jmax { assert!(y % c == 0); let nx = -y; let ny = x + e * y / c; x = nx; y = ny; pw.insert(j, (x, y)); }
        // z^{-1} = (e/c) - z :  (X + Y z)(e/c - z) = eX/c - X z + eY z/c - Y(e z - c)/c = (eX/c + Y) - X z
        let (mut x, mut y) = (one, 0i128);
        for j in 1..=jmax { assert!((e * x) % c == 0); let nx = e * x / c + y; let ny = -x; x = nx; y = ny; pw.insert(-j, (x, y)); }
        Zeta { c, s, pw }
    }
    fn eval(&self, e: &E) -> (i128, i128) {
        let (mut x, mut y) = (0i128, 0i128);
        for (i, &v) in e.a.iter().enumerate() {
            if v == 0 { continue; }
            let (px, py) = self.pw[&(e.lo + i as i32)];
            x += v as i128 * px; y += v as i128 * py;
        }
        (x, y)
    }
}

// f with  B = A + 2 mu f  (Laurent), by division from the low end; None if not divisible.
fn carry(a: &E, b: &E, c: i32, ee: i32) -> Option<(i32, Vec<i32>)> {
    let lo = a.lo.min(b.lo);
    let hi = (a.lo + a.a.len() as i32).max(b.lo + b.a.len() as i32);
    let mut d: Vec<i64> = (lo..hi).map(|j| (dep(b, j) - dep(a, j)) as i64).collect();
    if d.iter().all(|&x| x == 0) { return Some((0, vec![])); }
    // 2mu = [2c, -2e, 2c] at offsets 0,1,2
    let m = [2 * c as i64, -2 * ee as i64, 2 * c as i64];
    let n = d.len();
    if n < 3 { return None; }
    let mut f = vec![0i64; n - 2];
    for i in 0..n - 2 {
        if d[i] % m[0] != 0 { return None; }
        let q = d[i] / m[0]; f[i] = q;
        for t in 0..3 { d[i + t] -= q * m[t]; }
    }
    if d.iter().any(|&x| x != 0) { return None; }
    let mut s = 0; let mut t = f.len();
    while s < t && f[s] == 0 { s += 1; }
    while t > s && f[t - 1] == 0 { t -= 1; }
    Some((lo + s as i32, f[s..t].iter().map(|&x| x as i32).collect()))
}

fn hull(e: &E) -> Option<(i32, i32)> {
    let nz: Vec<i32> = e.a.iter().enumerate().filter(|(_, &v)| v != 0).map(|(i, _)| e.lo + i as i32).collect();
    if nz.is_empty() { None } else { Some((nz[0], *nz.last().unwrap())) }
}


// ---- exact W_T length by min-plus DP over carries f (the transfer structure of atom A3).
// ell_T(h) = min_f ell_univ(A + 2 mu f), f supported in [J0, J1-2], |f_j| <= F.
// State after edge j-1: (phase, f_{j-1}, f_{j-2}, a'_{j-1}); phase 0 = span not started,
// 1 = site j inside span with lo < j (or just started), 2 = span ended.
// Exact for the closed form (span/gap/cut/shield terms handled by guessing lo, hi; any
// over-guess only adds cost, so the min is the true closed form).
fn site_ab(k: i32, dl: i32, eps: i32, s: i32, am1: i32, a0: i32) -> (i32, i32, i32) {
    let (mut al, mut be, mut phi) = (am1, a0, ftrav(k, s - 1));
    if s == 0 { al -= 1; phi += 1; }
    if s == k { if dl == 0 { al += eps; phi -= 1; } else { be -= eps; } }
    (al, be, phi)
}
fn edge_cost(k: i32, j: i32, a: i32) -> i64 { let m = a.abs().max(ftrav(k, j).abs()); if m == 0 { 2 } else { m as i64 } }

fn ell_t_dp(h: &E, c: i32, ee: i32, fmax: i32, w: i32) -> (i64, i32, Vec<i32>) { ell_t_dp_r(h, c, ee, fmax, w, None) }
fn ell_t_dp_r(h: &E, c: i32, ee: i32, fmax: i32, w: i32, fr: Option<(i32, i32)>) -> (i64, i32, Vec<i32>) {
    let ub = ell_univ(h);
    let (sl, sh) = span(h);
    let j0 = sl - w; let j1 = sh + w;           // steps; a' supported on edges [sl-w, sh-1+w]
    let lof = 0.min(h.k); let hif = 0.max(h.k); // forced sites
    let (m0, m1, m2) = (2 * c, -2 * ee, 2 * c);
    type K = (u8, i32, i32, i32);
    let mut cur: HashMap<K, (i64, usize)> = HashMap::new();
    cur.insert((0, 0, 0, 0), (0, usize::MAX));
    let mut hist: Vec<Vec<(K, i64, usize, i32)>> = Vec::new(); // per step: (key, cost, prev idx, fj)
    let mut prev_keys: Vec<K> = vec![(0, 0, 0, 0)];
    let mut prev_index: HashMap<K, usize> = HashMap::new(); prev_index.insert((0, 0, 0, 0), 0);
    hist.push(vec![((0, 0, 0, 0), 0, usize::MAX, 0)]);
    for j in j0..=j1 {
        let mut nxt: HashMap<K, (i64, usize, i32)> = HashMap::new();
        let frange = if j <= j1 - 3 && fr.map_or(true, |(a, b)| a <= j && j <= b) { fmax } else { 0 };
        for (pi, key) in prev_keys.iter().enumerate() {
            let (ph, f1, f2, am1) = *key;
            let base = cur[key].0;
            for fj in -frange..=frange {
                let aj = dep(h, j) + m0 * fj + m1 * f1 + m2 * f2;
                let mut push = |nk: K, cst: i64| {
                    if cst > ub { return; }
                    let e = nxt.entry(nk).or_insert((i64::MAX, 0, 0));
                    if cst < e.0 { *e = (cst, pi, fj); }
                };
                let (al, be, phi) = site_ab(h.k, h.dl, h.eps, j, am1, aj);
                let sc = al.abs().max(be.abs()).max(phi.abs()) as i64;
                let zero = al == 0 && be == 0 && phi == 0;
                match ph {
                    2 => { if aj == 0 && j > hif { push((2, fj, f1, aj), base); } }
                    0 => {
                        if aj == 0 && j < lof { push((0, fj, f1, aj), base); }
                        if j <= lof {
                            // start span at lo = j (am1 must be 0: guaranteed in phase 0)
                            let shield = j == 0 && h.k == 0 && h.dl == 0 && zero;
                            push((1, fj, f1, aj), base + sc + edge_cost(h.k, j, aj) + if shield { 2 } else { 0 });
                            if aj == 0 && j >= hif { push((2, fj, f1, aj), base + sc); }
                        }
                    }
                    _ => {
                        push((1, fj, f1, aj), base + sc + edge_cost(h.k, j, aj) + if zero { 2 } else { 0 });
                        if aj == 0 && j >= hif { push((2, fj, f1, aj), base + sc); }
                    }
                }
            }
        }
        let mut keys: Vec<K> = Vec::with_capacity(nxt.len());
        let mut step: Vec<(K, i64, usize, i32)> = Vec::with_capacity(nxt.len());
        cur = HashMap::new();
        for (k2, (cst, pi, fj)) in nxt.into_iter() {
            cur.insert(k2, (cst, keys.len()));
            keys.push(k2); step.push((k2, cst, pi, fj));
        }
        hist.push(step);
        prev_keys = keys;
        let _ = &prev_index;
    }
    // final: must be in phase 2 (window margin makes this reachable)
    let mut best = (i64::MAX, usize::MAX);
    for (i, (k2, cst, _, _)) in hist.last().unwrap().iter().enumerate() { if k2.0 == 2 && *cst < best.0 { best = (*cst, i); } }
    assert!(best.1 != usize::MAX, "no feasible end state; enlarge window");
    // traceback f
    let mut f = vec![0i32; (j1 - j0 + 1) as usize];
    let mut idx = best.1;
    for st in (1..hist.len()).rev() {
        let (_, _, pi, fj) = hist[st][idx];
        f[st - 1] = fj; idx = pi;
    }
    let mut s0 = 0; let mut t0 = f.len();
    while s0 < t0 && f[s0] == 0 { s0 += 1; }
    while t0 > s0 && f[t0 - 1] == 0 { t0 -= 1; }
    (best.0, j0 + s0 as i32, f[s0..t0].to_vec())
}

fn apply_carry(h: &E, lo: i32, f: &[i32], c: i32, ee: i32) -> E {
    let mut o = h.clone();
    for (i, &x) in f.iter().enumerate() {
        let j = lo + i as i32;
        add_lamp(&mut o, j, 2 * c * x); add_lamp(&mut o, j + 1, -2 * ee * x); add_lamp(&mut o, j + 2, 2 * c * x);
    }
    dec(&enc(&o))
}

fn probe_mode(c: i32, ee: i32, fmax: i32, w: i32) {
    use std::io::BufRead;
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let t = line.trim(); if t.is_empty() || t.starts_with('#') { println!("{}", t); continue; }
        let v: Vec<i32> = t.split_whitespace().map(|x| x.parse().unwrap()).collect();
        let h = E { eps: v[0], dl: v[1], k: v[2], lo: v[3], a: v[4..].to_vec() };
        let lu = ell_univ(&h);
        let t1 = Instant::now();
        let (lt, flo, f) = ell_t_dp(&h, c, ee, fmax, w);
        let hs = apply_carry(&h, flo, &f, c, ee);
        let lchk = ell_univ(&hs);
        let fm = f.iter().map(|x| x.abs()).max().unwrap_or(0);
        println!("h: eps={} dl={} k={} lo={} a={:?} | univ={} T={} (chk {}) | f lo={} len={} max|f|={} {:?} | h* lo={} a={:?} | {:.2}s",
            h.eps, h.dl, h.k, h.lo, h.a, lu, lt, lchk, flo, f.len(), fm, f, hs.lo, hs.a, t1.elapsed().as_secs_f64());
    }
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
           fn range(&mut self, lo: i32, hi: i32) -> i32 { lo + (self.next() % ((hi - lo + 1) as u64)) as i32 } }
// random universal elements (normal form: a_j = ftrav(k,j) mod 2) and window sensitivity of ell_T
fn rand_mode(c: i32, ee: i32, n: usize, seed: u64, spanmax: i32, magmax: i32, fmax: i32) {
    let mut rng = Rng(seed | 1);
    let ws = [0, 1, 2, 3, 4, 6, 8, 12];
    let mut stab_hist: HashMap<i32, u64> = HashMap::new();
    let mut gain_hist: HashMap<i64, u64> = HashMap::new();
    let mut impw_hist: HashMap<i32, u64> = HashMap::new();
    let mut worst: Vec<String> = Vec::new();
    for it in 0..n {
        let k = rng.range(-spanmax / 2, spanmax / 2);
        let lo = rng.range(-spanmax, 0);
        let len = rng.range(1, spanmax) as usize;
        let mut a = vec![0i32; len];
        for (i, x) in a.iter_mut().enumerate() {
            let j = lo + i as i32; let par = ftrav(k, j).abs();
            let r = if rng.next() % 3 == 0 { 0 } else { rng.range(-magmax, magmax) };
            *x = if (r - par).rem_euclid(2) == 0 { r } else { r + if r >= 0 { 1 } else { -1 } };
        }
        let h = dec(&enc(&E { eps: if rng.next() % 2 == 0 { 1 } else { -1 }, dl: (rng.next() % 2) as i32, k, lo, a }));
        let lu = ell_univ(&h);
        let vals: Vec<(i64, i32, Vec<i32>)> = ws.iter().map(|&w| ell_t_dp(&h, c, ee, fmax, w)).collect();
        let best = vals.last().unwrap().0;
        let stab = ws.iter().zip(vals.iter()).find(|(_, v)| v.0 == best).map(|(w, _)| *w).unwrap();
        *stab_hist.entry(stab).or_insert(0) += 1;
        *gain_hist.entry(lu - best).or_insert(0) += 1;
        let fm = vals.last().unwrap().2.iter().map(|x| x.abs()).max().unwrap_or(0);
        if best < lu {
            let (sl, sh) = span(&h);
            let mut iw = -1;
            'ww: for wdt in 1..=10 {
                for p0 in (sl - 6)..=(sh + 2) {
                    let (v, _, _) = ell_t_dp_r(&h, c, ee, fmax, 8, Some((p0, p0 + wdt - 1)));
                    if v < lu { iw = wdt; break 'ww; }
                }
            }
            *impw_hist.entry(iw).or_insert(0) += 1;
            if iw < 0 || iw >= 6 { worst.push(format!("IMPW={} univ={} T={} h: eps={} dl={} k={} lo={} a={:?}", iw, lu, best, h.eps, h.dl, h.k, h.lo, h.a)); }
        }
        if stab >= 4 || fm >= fmax - 1 {
            worst.push(format!("it={} stab_w={} univ={} T={} vals={:?} h: eps={} dl={} k={} lo={} a={:?} | f lo={} {:?}",
                it, stab, lu, best, vals.iter().map(|v| v.0).collect::<Vec<_>>(), h.eps, h.dl, h.k, h.lo, h.a, vals.last().unwrap().1, vals.last().unwrap().2));
        }
    }
    let mut v: Vec<_> = stab_hist.into_iter().collect(); v.sort();
    println!("window W at which ell_T stabilises (vs W=12): {:?}", v);
    let mut v: Vec<_> = gain_hist.into_iter().collect(); v.sort();
    println!("gain ell_univ - ell_T: {:?}", v);
    let mut v: Vec<_> = impw_hist.into_iter().collect(); v.sort();
    println!("min width of an improving carry (|f|<=fmax; -1 = none <=10): {:?}", v);
    for w in worst.iter().take(40) { println!("{}", w); }
}

// scaling of optimal carries with profile length: random elements, span exactly L
fn scale_mode(c: i32, ee: i32, n: usize, seed: u64, magmax: i32, fmax: i32) {
    let mut rng = Rng(seed | 1);
    println!("# L  n  mean_gain  mean(max|f|)  max(max|f|)  mean(supp f / span h)  max(supp f/span h)  mean(|V|max/2c)  frac_hit_F");
    for &l in &[4i32, 8, 12, 16, 20, 24] {
        let (mut sg, mut sf, mut mf, mut sr, mut mr, mut sv, mut hit) = (0f64, 0f64, 0i32, 0f64, 0f64, 0f64, 0u32);
        for _ in 0..n {
            let k = rng.range(-l / 2, l / 2);
            let lo = -rng.range(0, l / 2);
            let mut a = vec![0i32; l as usize];
            for (i, x) in a.iter_mut().enumerate() {
                let j = lo + i as i32; let par = ftrav(k, j).abs();
                let r = rng.range(-magmax, magmax);
                *x = if (r - par).rem_euclid(2) == 0 { r } else { r + if r >= 0 { 1 } else { -1 } };
            }
            let h = dec(&enc(&E { eps: 1, dl: (rng.next() % 2) as i32, k, lo, a }));
            let lu = ell_univ(&h);
            let (lt, flo, f) = ell_t_dp(&h, c, ee, fmax, 3);
            let (sl, sh) = span(&h);
            let fm = f.iter().map(|x| x.abs()).max().unwrap_or(0);
            if fm >= fmax { hit += 1; }
            // prefix discrepancy |V_j| max over j, via the exact identity |f_{j-1} - conj(z) f_j|
            let re = ee as f64 / (2.0 * c as f64);
            let mut vmax = 0f64;
            for i in 0..=f.len() { let x = if i >= 1 { f[i - 1] } else { 0 } as f64; let y = if i < f.len() { f[i] } else { 0 } as f64;
                vmax = vmax.max((x * x + y * y - 2.0 * re * x * y).sqrt()); }
            let _ = flo;
            sg += (lu - lt) as f64; sf += fm as f64; mf = mf.max(fm);
            let r = f.len() as f64 / (sh - sl) as f64; sr += r; if r > mr { mr = r; } sv += vmax;
        }
        let nn = n as f64;
        println!("{:3} {:4} {:9.2} {:9.3} {:4} {:9.3} {:7.3} {:9.3} {:.3}", l, n, sg / nn, sf / nn, mf, sr / nn, mr, sv / nn, hit as f64 / nn);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 8 && args[3] == "scale" {
        scale_mode(args[1].parse().unwrap(), args[2].parse().unwrap(), args[4].parse().unwrap(), args[5].parse().unwrap(),
                   args[6].parse().unwrap(), args[7].parse().unwrap());
        return;
    }
    if args.len() >= 9 && args[3] == "rand" {
        rand_mode(args[1].parse().unwrap(), args[2].parse().unwrap(), args[4].parse().unwrap(), args[5].parse().unwrap(),
                  args[6].parse().unwrap(), args[7].parse().unwrap(), args[8].parse().unwrap());
        return;
    }
    if args.len() >= 6 && args[3] == "probe" {
        probe_mode(args[1].parse().unwrap(), args[2].parse().unwrap(), args[4].parse().unwrap(), args[5].parse().unwrap());
        return;
    }
    if args.len() < 6 { eprintln!("usage: wt_carry <c> <e> <D> <cap_mb> <outprefix>"); std::process::exit(2); }
    let c: i64 = args[1].parse().unwrap();
    let ee: i64 = args[2].parse().unwrap();
    let dmax: usize = args[3].parse().unwrap();
    let cap: f64 = args[4].parse().unwrap();
    let pre = &args[5];
    let t0 = Instant::now();
    // ---------- universal BFS
    let id: P = enc(&E { eps: 1, dl: 0, k: 0, lo: 0, a: vec![] });
    let mut seen: HashSet<P> = HashSet::new();
    seen.insert(id.clone());
    let mut layers: Vec<Vec<P>> = vec![vec![id]];
    for d in 1..=dmax {
        let mut nx: Vec<P> = Vec::new();
        for p in &layers[d - 1] {
            for q in nbrs(p).into_iter() { if !seen.contains(&q) { seen.insert(q.clone()); nx.push(q); } }
        }
        let rss = maxrss_mb();
        eprintln!("[bfs] d={:2} univ={:9} total={:10} {:.1}s rss={:.0}MB", d, nx.len(), seen.len(), t0.elapsed().as_secs_f64(), rss);
        layers.push(nx);
        if rss > cap { eprintln!("GUARD: rss {:.0} > cap {:.0}; abort", rss, cap); std::process::exit(3); }
    }
    drop(seen);
    // ---------- closed-form check + key computation
    let jm = dmax as i32 + 4; let zt = Zeta::new(c, ee, jm as u32 + 1, jm);
    let mut rows: Vec<((i8, i8, i8, i128, i128), u8, u32, u32)> = Vec::new(); // key, len, layer, idx
    let mut cf_bad = 0u64;
    for (d, l) in layers.iter().enumerate() {
        for (i, p) in l.iter().enumerate() {
            let e = dec(p);
            if ell_univ(&e) != d as i64 { cf_bad += 1; }
            let (x, y) = zt.eval(&e);
            rows.push(((p[0], p[1], p[2], x, y), d as u8, d as u32, i as u32));
        }
    }
    eprintln!("[key] closed-form mismatches on ball: {}", cf_bad);
    rows.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
    let _ = zt.c; let _ = zt.s;
    // ---------- per-fiber analysis
    let mut ut = vec![0u64; dmax + 1];
    let mut nopt_hist: HashMap<usize, u64> = HashMap::new();
    // carry stats for non-optimal lifts h (ell_univ(h) > ell_T)
    // over[w] = # h whose BEST optimal lift (min overhang) sticks out of hull(A_h) by w
    let mut over_best: HashMap<i32, u64> = HashMap::new();
    let mut impw: HashMap<(i32, i32), u64> = HashMap::new();
    let mut over_all: HashMap<i32, u64> = HashMap::new();
    let mut fmax_best: HashMap<i32, u64> = HashMap::new();
    let mut ratio_worst: f64 = 0.0;
    let mut nonopt = 0u64; let mut pure_nonopt = 0u64;
    let mut ex = std::fs::File::create(format!("{}_examples.txt", pre)).unwrap();
    let mut shown: HashMap<(i32, i32), u32> = HashMap::new();
    // per-depth table: at depth d (ell_univ(h)=d), # nonopt h, max overhang (best), max |f|
    let mut per_d: Vec<(u64, i32, i32, i32, i32)> = vec![(0, 0, 0, 0, 0); dmax + 1];
    // fiber structure: number of ball-lifts per g, by ell_T
    let dpchk: Option<(i32, i32)> = std::env::var("DPCHECK").ok().map(|v| { let q: Vec<i32> = v.split(',').map(|x| x.parse().unwrap()).collect(); (q[0], q[1]) });
    let (mut dp_n, mut dp_bad) = (0u64, 0u64);
    let mut i = 0;
    while i < rows.len() {
        let mut j = i; while j < rows.len() && rows[j].0 == rows[i].0 { j += 1; }
        let lt = rows[i].1 as usize;
        ut[lt] += 1;
        if let Some((fm, ww)) = dpchk {
            for r in &rows[i..j] {
                let h = dec(&layers[r.2 as usize][r.3 as usize]);
                let (v, _, _) = ell_t_dp(&h, c as i32, ee as i32, fm, ww);
                dp_n += 1;
                if v != lt as i64 { dp_bad += 1; if dp_bad <= 5 { eprintln!("DP MISMATCH h={:?} dp={} bfs={}", h, v, lt); } }
            }
        }
        let opts: Vec<E> = rows[i..j].iter().filter(|r| r.1 as usize == lt).map(|r| dec(&layers[r.2 as usize][r.3 as usize])).collect();
        *nopt_hist.entry(opts.len()).or_insert(0) += 1;
        for r in &rows[i..j] {
            if r.1 as usize == lt { continue; }
            nonopt += 1;
            let h = dec(&layers[r.2 as usize][r.3 as usize]);
            { let (sl, sh) = span(&h); if (sl..sh).all(|jj| dep(&h, jj).abs() == ftrav(h.k, jj).abs()) { pure_nonopt += 1; } }
            // window = span(h): lamps + travel interval + origin, as edge indices [hl, hh]
            let (sl, sh) = span(&h); let (hl, hh) = (sl, sh - 1);
            let mut best: Option<(i32, i32, i32, (i32, Vec<i32>), E)> = None; // (overhang, fmax, fl1)
            for o in &opts {
                let (fl, f) = carry(&h, o, c as i32, ee as i32).expect("fiber elements must differ by 2mu f");
                let ofl = if f.is_empty() { 0 } else { (hl - fl).max(0) + ((fl + f.len() as i32 + 1) - hh).max(0) };
                let fm = f.iter().map(|x| x.abs()).max().unwrap_or(0);
                let f1: i32 = f.iter().map(|x| x.abs()).sum();
                *over_all.entry(ofl).or_insert(0) += 1;
                let cand = (ofl, fm, f1, (fl, f), o.clone());
                if best.as_ref().map_or(true, |b| (cand.0, cand.2) < (b.0, b.2)) { best = Some(cand); }
            }
            let b = best.unwrap();
            let mut iw = i32::MAX; let mut iwf = 0;
            for r2 in &rows[i..j] {
                if r2.1 >= r.1 { continue; }
                let o2 = dec(&layers[r2.2 as usize][r2.3 as usize]);
                let (_, f2) = carry(&h, &o2, c as i32, ee as i32).unwrap();
                let wd = f2.len() as i32; let fm2 = f2.iter().map(|x| x.abs()).max().unwrap_or(0);
                if wd < iw || (wd == iw && fm2 < iwf) { iw = wd; iwf = fm2; }
            }
            *impw.entry((iw, iwf)).or_insert(0) += 1;
            if iw >= 9 && r.1 as i32 - lt as i32 == 2 { let cnt = shown.entry((-1, iw)).or_insert(0); if *cnt < 6 { *cnt += 1;
                writeln!(ex, "IMPW={} | h: len={} eps={} dl={} k={} lo={} a={:?} | ell_T={}", iw, r.1, h.eps, h.dl, h.k, h.lo, h.a, lt).unwrap(); } }
            *over_best.entry(b.0).or_insert(0) += 1;
            *fmax_best.entry(b.1).or_insert(0) += 1;
            let amax = h.a.iter().map(|x| x.abs()).max().unwrap_or(1).max(1);
            ratio_worst = ratio_worst.max(b.1 as f64 / amax as f64);
            let pd = &mut per_d[r.1 as usize];
            pd.0 += 1; pd.4 = pd.4.max(iw); pd.1 = pd.1.max(b.0); pd.2 = pd.2.max(b.1); pd.3 = pd.3.max(r.1 as i32 - lt as i32);
            let cnt = shown.entry((r.1 as i32, b.0)).or_insert(0);
            if *cnt < 2 && b.0 >= pd.1 {
                *cnt += 1;
                writeln!(ex, "overhang={} fmax={} | h: len={} eps={} dl={} k={} lo={} a={:?} | h*: len={} lo={} a={:?} | f: lo={} {:?}",
                    b.0, b.1, r.1, h.eps, h.dl, h.k, h.lo, h.a, lt, b.4.lo, b.4.a, (b.3).0, (b.3).1).unwrap();
            }
        }
        i = j;
    }
    let mut out = std::fs::File::create(format!("{}_summary.txt", pre)).unwrap();
    writeln!(out, "# wt_carry c={} e={} D={}  closed-form mismatches={}  time={:.1}s rss={:.0}MB", c, ee, dmax, cf_bad, t0.elapsed().as_secs_f64(), maxrss_mb()).unwrap();
    writeln!(out, "# W_T spheres (exact for d<=D):").unwrap();
    for d in 0..=dmax { writeln!(out, "uT {} {} univ {}", d, ut[d], layers[d].len()).unwrap(); }
    writeln!(out, "# per univ depth d: #h non-optimal, max best-overhang, max |f| (best), max (ell_univ(h)-ell_T), max min-improving-width").unwrap();
    for d in 0..=dmax { let p = per_d[d]; writeln!(out, "nd {} {} {} {} {} {}", d, p.0, p.1, p.2, p.3, p.4).unwrap(); }
    let mut v: Vec<_> = over_best.into_iter().collect(); v.sort();
    writeln!(out, "# overhang of best optimal lift beyond span(h): {:?}", v).unwrap();
    let mut v2: Vec<_> = impw.iter().map(|(a, b)| (*a, *b)).collect(); v2.sort();
    writeln!(out, "# min-width improving carry (width, max|f| at that width) -> count: {:?}", v2).unwrap();
    let mut v: Vec<_> = over_all.into_iter().collect(); v.sort();
    writeln!(out, "# overhang over all optimal lifts: {:?}", v).unwrap();
    let mut v: Vec<_> = fmax_best.into_iter().collect(); v.sort();
    writeln!(out, "# max|f| of best carry: {:?}", v).unwrap();
    writeln!(out, "# pure-travel (|a_j|=|ftrav|, no off-spine lamps) non-optimal lifts in ball: {}", pure_nonopt).unwrap();
    writeln!(out, "# worst max|f| / max|a_h| = {:.3}; nonopt lifts = {}", ratio_worst, nonopt).unwrap();
    let mut v: Vec<_> = nopt_hist.into_iter().collect(); v.sort();
    writeln!(out, "# #optimal lifts per W_T element: {:?}", v).unwrap();
    writeln!(out, "# DP check (DPCHECK={:?}): {} elements, {} mismatches", dpchk, dp_n, dp_bad).unwrap();
    eprintln!("DP check: {} elements, {} mismatches", dp_n, dp_bad);
    eprintln!("done {:.1}s rss={:.0}MB", t0.elapsed().as_secs_f64(), maxrss_mb());
}
