// u_modp: compute (u_n mod p) for the A396406 TRUE geodesic growth series, to high n,
// for the orthogonal (Christol/automaticity) transcendence route.
//
// Faithful Rust port of the VALIDATED polynomial-time catalytic engine
//   code/zeta_probe/route_b/true_gf.py  (+ fast_relaxed3.py deposits/boundary_site_cost/site_cost,
//   + c_formula.py shield_right/shield_left), with the 1-D collapse: U(x)=W(x,x^2), true_len =
//   relaxed_len + 2*cycles, so we fold +2-per-cycle straight into the length and reduce counts mod p.
// Self-validates against the 43 known u_n (b396406_depth42.txt) for n=0..42 before trusting new terms.
//
// BUILD:  cargo build --release
// RUN:    ./target/release/u_modp N P [WORKDIR]
//   e.g.  ./target/release/u_modp 110 3          (k=3 kernel test; ~minutes)
//         ./target/release/u_modp 250 3 work250  (k=4 kernel test)
// Resumable (atomic checkpoint per k), prints per-k ETA. Writes u_mod{P}_N{N}.txt (space-separated).
// Analyze the kernel with the Python:  python3 kernel_modp.py analyze u_mod3_N110.txt 3

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::time::Instant;
use std::io::Write;

// ---- fast dep-free hasher for i32 / (i32,i32) keys ----
#[derive(Default)]
struct FastHasher(u64);
impl Hasher for FastHasher {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, bytes: &[u8]) { for &b in bytes { self.0 = (self.0 ^ b as u64).wrapping_mul(0x100000001b3); } }
    fn write_i32(&mut self, i: i32) { self.0 = (self.0 ^ (i as u32 as u64)).wrapping_mul(0x9E3779B97F4A7C15); }
}
type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
fn fmap<K, V>() -> FastMap<K, V> { FastMap::default() }

type Poly = FastMap<i32, u64>; // true_len -> count mod p

// ---------------- elementary helpers (ports of the Python) ----------------
#[inline] fn f_of(j: i32, k: i32) -> i32 { if 0 <= j && j < k { 1 } else if k <= j && j < 0 { -1 } else { 0 } }
#[inline] fn sgn(x: i32) -> i32 { if x > 0 { 1 } else if x < 0 { -1 } else { 0 } }
#[inline] fn edge_updn(f: i32, m: i32) -> (i32, i32) { ((m + f) / 2, (m - f) / 2) } // m>=|f| => both non-neg even
#[inline] fn cross(aj: i32, fj: i32) -> i32 { if aj == 0 && fj == 0 { 2 } else { aj.abs().max(fj.abs()) } }

fn site_cost(arr: &[i32; 4], dep: &[i32; 4]) -> Option<i32> {
    if arr[0] + arr[1] + arr[2] + arr[3] != dep[0] + dep[1] + dep[2] + dep[3] { return None; }
    let a0 = arr[0] - arr[0].min(dep[0]); let d0 = dep[0] - arr[0].min(dep[0]);
    let a1 = arr[1] - arr[1].min(dep[1]); let d1 = dep[1] - arr[1].min(dep[1]);
    let a2 = arr[2] - arr[2].min(dep[2]);
    let a3 = arr[3] - arr[3].min(dep[3]);
    let al = a0 + a1; let ar = a2 + a3; let dl = d0 + d1;
    let mut x = al.min(ar - dl + al);
    let lo = al - dl;
    if x < lo { x = lo; }
    if x < 0 { x = 0; }
    let y = dl - al + x;
    Some(2 * al + 2 * ar - x - y)
}

fn shield_right(k: i32, e: i32, dl: i32, b: i32) -> i32 {
    if k == 0 { return if e == 1 && dl == 0 { 0 } else { 1 }; }
    if b.abs() >= 3 { return 1; }
    let s = sgn(b);
    if k > 0 { return if dl == 1 { 1 } else if s == e { 1 } else { 0 }; }
    if s == -1 { 1 } else { 0 }
}
fn shield_left(k: i32, e: i32, dl: i32, b: i32) -> i32 {
    if k >= 0 { return 1; }
    if b.abs() >= 3 { return 1; }
    if dl == 0 { 1 } else if e == sgn(b) { 0 } else { 1 }
}

fn deposits(f: i32, cap: i32) -> Vec<i32> {
    let par = f & 1; // -1&1=1, 0&1=0, 1&1=1  (matches Python)
    let mut a = if par != 0 { 1 } else { 2 };
    let mut out = Vec::new();
    while a <= cap { out.push(a); out.push(-a); a += 2; }
    out
}

// boundary_site_cost with memoization
type BKey = (i32, i32, i32, i32, bool, bool, i32, i32);
fn boundary_site_cost(memo: &mut HashMap<BKey, Option<i32>>, al_: i32, fl: i32, ar_: i32, fr: i32, is0: bool, isk: bool, eps: i32, delta: i32) -> Option<i32> {
    let key = (al_, fl, ar_, fr, is0, isk, eps, delta);
    if let Some(v) = memo.get(&key) { return *v; }
    let mut best: Option<i32> = None;
    for laml in 0..3 {
        let mut ml = al_.abs().max(fl.abs()) + 2 * laml;
        if (ml - fl).rem_euclid(2) == 1 || (ml == 0 && fl != 0) { ml += 1; }
        let (ul, dnl) = edge_updn(fl, ml);
        for pul in 0..=ul {
            let tl = al_ + dnl - ul + 2 * pul;
            if tl.rem_euclid(2) == 1 { continue; }
            let pdl = tl.div_euclid(2);
            if pdl < 0 || pdl > dnl { continue; }
            for lamr in 0..3 {
                let mut mr = ar_.abs().max(fr.abs()) + 2 * lamr;
                if (mr - fr).rem_euclid(2) == 1 || (mr == 0 && fr != 0) { mr += 1; }
                let (ur, dnr) = edge_updn(fr, mr);
                for pur in 0..=ur {
                    let tr = ar_ + dnr - ur + 2 * pur;
                    if tr.rem_euclid(2) == 1 { continue; }
                    let pdr = tr.div_euclid(2);
                    if pdr < 0 || pdr > dnr { continue; }
                    let mut arr = [pul, ul - pul, pdr, dnr - pdr];
                    let mut dep = [pdl, dnl - pdl, pur, ur - pur];
                    if is0 { arr[0] += 1; }
                    if isk { let s = if delta == 1 { 2 } else { 0 }; dep[(s + if eps == 1 { 0 } else { 1 }) as usize] += 1; }
                    if arr.iter().sum::<i32>() != dep.iter().sum::<i32>() { continue; }
                    if let Some(c) = site_cost(&arr, &dep) {
                        if best.is_none() || c < best.unwrap() { best = Some(c); }
                    }
                }
            }
        }
    }
    memo.insert(key, best);
    best
}

// padd with 1-D collapse + mod p: tgt[d + dx + 2*dc] += src[d]  (mod p), drop zeros
#[inline]
fn padd(tgt: &mut Poly, src: &Poly, dx: i32, dc: i32, p: u64) {
    let shift = dx + 2 * dc;
    for (&d, &cnt) in src.iter() {
        let key = d + shift;
        let e = tgt.entry(key).or_insert(0);
        *e = (*e + cnt) % p;
        if *e == 0 { tgt.remove(&key); }
    }
}

// one (eps,delta,k) slice -> out: true_len -> count mod p
fn slice_gf(memo: &mut HashMap<BKey, Option<i32>>, eps: i32, delta: i32, k: i32, n: i32, cap: i32, p: u64) -> Poly {
    let k0 = 0.min(k); let k1 = 0.max(k);
    let m = n + 1;
    let jlo = k0 - m; let jhi = k1 + m;
    let mut out: Poly = fmap();
    let mut add_out = |out: &mut Poly, idx: i32, cnt: u64| { let e = out.entry(idx).or_insert(0); *e = (*e + cnt) % p; if *e == 0 { out.remove(&idx); } };
    if k == 0 {
        if let Some(bc) = boundary_site_cost(memo, 0, 0, 0, 0, true, true, eps, delta) {
            if bc <= n { add_out(&mut out, bc, 1); }
        }
    }
    // states: 'pre' poly + 'in' states keyed by (aprev, pend)
    let mut pre: Option<Poly> = Some({ let mut h: Poly = fmap(); h.insert(0, 1); h });
    let mut ins: FastMap<(i32, i32), Poly> = fmap();

    for j in jlo..jhi {
        let fj = f_of(j, k);
        let site_is0 = j == 0; let site_isk = j == k; let site_virtual = site_is0 || site_isk;
        let fl = f_of(j - 1, k);
        let mut npre: Option<Poly> = None;
        let mut nins: FastMap<(i32, i32), Poly> = fmap();

        // ---- 'pre' state ----
        if let Some(poly) = pre.as_ref() {
            if fj == 0 && j < k0 {
                let np = npre.get_or_insert_with(fmap);
                padd(np, poly, 0, 0, p);
            }
            if j <= k0 {
                for aj in deposits(fj, cap) {
                    let cr = cross(aj, fj);
                    let sc = if site_virtual {
                        match boundary_site_cost(memo, 0, 0, aj, fj, site_is0, site_isk, eps, delta) { Some(v) => v, None => continue }
                    } else { aj.abs() };
                    let add = cr + sc;
                    let tgt = nins.entry((aj, 0)).or_insert_with(fmap);
                    padd(tgt, poly, add, 0, p);
                }
                if site_virtual && fj == 0 && j <= k0 {
                    let aj = 0;
                    let cr = cross(aj, fj);
                    if let Some(sc) = boundary_site_cost(memo, 0, 0, aj, fj, site_is0, site_isk, eps, delta) {
                        let add = cr + sc;
                        let dc0 = if j == k1 { 1 - shield_right(k, eps, delta, 0) } else { 0 };
                        let tgt = nins.entry((aj, 0)).or_insert_with(fmap);
                        padd(tgt, poly, add, dc0, p);
                    }
                }
            }
        }
        // ---- 'in' states ----
        for (&(aprev, pend), poly) in ins.iter() {
            let mut cand = deposits(fj, cap);
            if fj == 0 { cand.insert(0, 0); }
            let prev_was_gap = aprev == 0 && fl == 0;
            for aj in cand {
                let cr = cross(aj, fj);
                let is_gap = aj == 0 && fj == 0;
                let sc = if site_virtual {
                    match boundary_site_cost(memo, aprev, fl, aj, fj, site_is0, site_isk, eps, delta) { Some(v) => v, None => continue }
                } else { aprev.abs().max(aj.abs()) };
                let mut dc;
                if site_virtual {
                    dc = 0;
                    if is_gap && j == k1 { dc = 1 - shield_right(k, eps, delta, aprev); }
                    if j == k0 && k < 0 && prev_was_gap { dc += 1 - shield_left(k, eps, delta, aj); }
                } else {
                    dc = if is_gap && prev_was_gap { 1 } else { 0 };
                }
                let mut newpend = pend;
                if k == 0 && delta == 0 && j == 0 && aprev != 0 && aprev.rem_euclid(2) == 0 && aj == 0 {
                    newpend = if eps == 1 { -1 } else if aprev == 2 { 1 } else { 0 };
                }
                if pend != 0 && j >= 1 && !is_gap && prev_was_gap { dc += pend; newpend = 0; }
                let add = cr + sc;
                let tgt = nins.entry((aj, newpend)).or_insert_with(fmap);
                padd(tgt, poly, add, dc, p);
            }
        }
        pre = npre.filter(|h| !h.is_empty());
        ins = nins.into_iter().filter(|(_, v)| !v.is_empty()).collect();

        // ---- right-boundary accumulation ----
        let sr = j + 1;
        if sr >= k1 {
            let site_is0r = sr == 0; let site_iskr = sr == k; let site_virtualr = site_is0r || site_iskr;
            for (&(aprev, _pend), poly) in ins.iter() {
                let active_right = aprev != 0 || fj != 0;
                if !active_right && !site_virtualr { continue; }
                let sc = if site_virtualr {
                    match boundary_site_cost(memo, aprev, fj, 0, 0, site_is0r, site_iskr, eps, delta) { Some(v) => v, None => continue }
                } else { aprev.abs() };
                for (&d, &cnt) in poly.iter() {
                    let nd = d + sc;
                    if nd <= n { add_out(&mut out, nd, cnt); }
                }
            }
        }
        if pre.is_none() && ins.is_empty() { break; }
    }
    out
}

fn known_u() -> Vec<u64> {
    vec![1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,
         62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,
         13031206,19574659,29338781,43997388,65932461,98849591,147969934]
}

fn ckpt_path(work: &str, n: i32, p: u64) -> String { format!("{}/ckpt_N{}_P{}.txt", work, n, p) }

fn save_ckpt(work: &str, n: i32, p: u64, done: &Vec<i32>, u: &Vec<u64>) {
    let path = ckpt_path(work, n, p);
    let tmp = format!("{}.tmp", path);
    let mut s = String::new();
    s.push_str(&format!("{} {}\n", n, p));
    s.push_str(&done.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "));
    s.push('\n');
    s.push_str(&u.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "));
    s.push('\n');
    std::fs::write(&tmp, s).unwrap();
    std::fs::rename(&tmp, &path).unwrap(); // atomic
}

fn load_ckpt(work: &str, n: i32, p: u64) -> Option<(Vec<i32>, Vec<u64>)> {
    let path = ckpt_path(work, n, p);
    let s = std::fs::read_to_string(&path).ok()?;
    let mut lines = s.lines();
    let hdr: Vec<i64> = lines.next()?.split_whitespace().map(|x| x.parse().unwrap()).collect();
    if hdr[0] != n as i64 || hdr[1] != p as i64 { return None; }
    let done: Vec<i32> = lines.next()?.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    let u: Vec<u64> = lines.next()?.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    if u.len() != (n as usize + 1) { return None; }
    Some((done, u))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 { eprintln!("usage: u_modp N P [WORKDIR]"); std::process::exit(1); }
    let n: i32 = args[1].parse().unwrap();
    let p: u64 = args[2].parse().unwrap();
    let work = if args.len() > 3 { args[3].clone() } else { ".".to_string() };
    std::fs::create_dir_all(&work).ok();
    let cap = n / 3 + 2;
    let kmax = n / 2 + 1;

    let mut u = vec![0u64; n as usize + 1];
    let mut done: Vec<i32> = Vec::new();
    if let Some((d, uu)) = load_ckpt(&work, n, p) {
        done = d; u = uu;
        println!("# resumed: {}/{} k-values done", done.len(), 2 * kmax + 1);
    }
    let done_set: std::collections::HashSet<i32> = done.iter().cloned().collect();
    let mut todo: Vec<i32> = (-kmax..=kmax).filter(|k| !done_set.contains(k)).collect();
    todo.sort_by_key(|k| -(k.abs())); // expensive (high |k|) first: better load balance + monotone ETA
    println!("# u_n mod {} for n=0..{}  (cap={}, kmax={}, {} k-slices remaining)", p, n, cap, kmax, todo.len());

    // independent k-slices -> parallelize over cores in waves (atomic checkpoint per wave)
    let nthreads = std::env::var("THREADS").ok().and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4));
    println!("# using {} threads", nthreads);
    let t0 = Instant::now();
    let total = todo.len();
    let mut pos = 0;
    while pos < total {
        let end = (pos + nthreads).min(total);
        let wave: Vec<i32> = todo[pos..end].to_vec();
        let partials: Vec<Vec<u64>> = std::thread::scope(|s| {
            let handles: Vec<_> = wave.iter().map(|&k| {
                s.spawn(move || {
                    let mut memo: HashMap<BKey, Option<i32>> = HashMap::new();
                    let mut pu = vec![0u64; n as usize + 1];
                    for &eps in &[1, -1] {
                        for &delta in &[0, 1] {
                            let out = slice_gf(&mut memo, eps, delta, k, n, cap, p);
                            for (&t, &cnt) in out.iter() {
                                if t >= 0 && t <= n { let idx = t as usize; pu[idx] = (pu[idx] + cnt) % p; }
                            }
                        }
                    }
                    pu
                })
            }).collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        for pu in &partials { for i in 0..=(n as usize) { u[i] = (u[i] + pu[i]) % p; } }
        for &k in &wave { done.push(k); }
        save_ckpt(&work, n, p, &done, &u);
        pos = end;
        let el = t0.elapsed().as_secs_f64();
        let frac = pos as f64 / total as f64;
        let eta = if frac > 0.0 { el / frac * (1.0 - frac) } else { 0.0 };
        println!("  {}/{} k-slices done  elapsed {:6.0}s  ETA {:6.0}s (~{:.1}m)", pos, total, el, eta, eta / 60.0);
        std::io::stdout().flush().ok();
    }

    // validate vs 43 known
    let kn = known_u();
    let mut bad = Vec::new();
    for nn in 0..=(n as usize).min(kn.len() - 1) {
        if u[nn] != kn[nn] % p { bad.push(nn); }
    }
    if bad.is_empty() { println!("# validation vs 43 known u_n mod {}: OK", p); }
    else { println!("# validation vs 43 known u_n mod {}: MISMATCH at {:?}", p, bad); }

    let out_path = format!("{}/u_mod{}_N{}.txt", work, p, n);
    let s = u.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    std::fs::write(&out_path, s).unwrap();
    println!("# wrote {}", out_path);
    println!("# analyze the kernel with:  python3 kernel_modp.py analyze {} {}", out_path, p);
}
