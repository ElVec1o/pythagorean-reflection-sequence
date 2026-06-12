// certify38 — uniform-in-T universality certificate at depth D (default 38).
//
// WHAT IT PROVES (if all checks pass):
//   n_T > D for EVERY right triangle with positive unequal rational legs,
//   i.e. the orbit-growth sequence of every such triangle equals the generic
//   (symbolic) sequence through depth D.  In particular, for D = 38, the
//   published OEIS A396406 terms a(31)..a(38) (computed from the (3,4)
//   triangle alone) are certified to be the generic terms.
//
// METHOD:
//   Pass 1: exact symbolic BFS over the triangle-independent normal form
//     (eps, delta, k, P), P an integer Laurent polynomial; layer counts are
//     compared against the published A396406 values.
//   Pass 2: by the effective theorem (Gauss's lemma on the shape's minimal
//     polynomial mu_T = c t^2 - e t + c), a deviation at depth <= D forces
//     c_T <= 2D.  The finitely many candidate rotation numbers zeta with
//     c <= 2D are each checked by evaluating the ENTIRE symbolic ball at
//     zeta modulo a 31-bit prime q == 1 (mod 4).  Distinct mod q implies
//     distinct in Q(i), so a full-count result is an exact certificate.
//     Any deficit is re-checked with a second independent prime.
//
// CRASH SAFETY: BFS layers are checkpointed to ./certify38_state/ball.bin
//   (+ layers.txt); completed candidates are recorded in results.txt.
//   Re-running the same command resumes where it left off.
//
// Usage:  cargo run --release            (depth 38)
//         cargo run --release -- 20      (smaller depth, for testing)

use std::collections::HashSet;
use std::fs::{self, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::time::Instant;

const PUBLISHED: [u64; 39] = [
    1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574, 11543,
    17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236, 1697179,
    2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781,
];

#[derive(Clone)]
struct Elem {
    eps: i8,
    delta: u8,
    k: i16,
    p: Vec<(i16, i16)>, // sorted by exponent ascending; no zero coeffs
}

fn merge_add(a: &[(i16, i16)], b: &[(i16, i16)]) -> Vec<(i16, i16)> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i].0 < b[j].0) {
            out.push(a[i]);
            i += 1;
        } else if i >= a.len() || b[j].0 < a[i].0 {
            out.push(b[j]);
            j += 1;
        } else {
            let c = a[i].1 + b[j].1;
            if c != 0 {
                out.push((a[i].0, c));
            }
            i += 1;
            j += 1;
        }
    }
    out
}

// compose: (g o h), i.e. apply h first.  General law:
//   delta_g = 0:  (eg*eh, dh,   kg+kh, eg*t^kg*Ph        + Pg)
//   delta_g = 1:  (eg*eh, 1-dh, kg-kh, eg*t^kg*Ph(t^-1)  + Pg)
fn compose(g: &Elem, h: &Elem) -> Elem {
    let eps = g.eps * h.eps;
    if g.delta == 0 {
        let terms: Vec<(i16, i16)> = h
            .p
            .iter()
            .map(|&(e, c)| (e + g.k, (g.eps as i16) * c))
            .collect();
        Elem {
            eps,
            delta: h.delta,
            k: g.k + h.k,
            p: merge_add(&terms, &g.p),
        }
    } else {
        let terms: Vec<(i16, i16)> = h
            .p
            .iter()
            .rev()
            .map(|&(e, c)| (g.k - e, (g.eps as i16) * c))
            .collect();
        Elem {
            eps,
            delta: 1 - h.delta,
            k: g.k - h.k,
            p: merge_add(&terms, &g.p),
        }
    }
}

const OFF: i16 = 120; // exponent/k offset for byte encoding (|k|,|e| <= D <= 60 safe)

fn encode(e: &Elem, buf: &mut Vec<u8>) {
    buf.clear();
    buf.push(if e.eps > 0 { 1 } else { 0 });
    buf.push(e.delta);
    buf.push((e.k + OFF) as u8);
    buf.push(e.p.len() as u8);
    for &(ex, c) in &e.p {
        buf.push((ex + OFF) as u8);
        let cb = c.to_le_bytes();
        buf.push(cb[0]);
        buf.push(cb[1]);
    }
}

fn decode(buf: &[u8], pos: &mut usize) -> Elem {
    let eps = if buf[*pos] == 1 { 1i8 } else { -1i8 };
    let delta = buf[*pos + 1];
    let k = buf[*pos + 2] as i16 - OFF;
    let n = buf[*pos + 3] as usize;
    let mut p = Vec::with_capacity(n);
    let mut q = *pos + 4;
    for _ in 0..n {
        let ex = buf[q] as i16 - OFF;
        let c = i16::from_le_bytes([buf[q + 1], buf[q + 2]]);
        p.push((ex, c));
        q += 3;
    }
    *pos = q;
    Elem { eps, delta, k, p }
}

fn rec_len(buf: &[u8], pos: usize) -> usize {
    4 + 3 * (buf[pos + 3] as usize)
}

// ---------- modular arithmetic ----------
fn pow_mod(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
    b %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % m;
        }
        b = b * b % m;
        e >>= 1;
    }
    r
}
fn is_prime(n: u64) -> bool {
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    'outer: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 0..r - 1 {
            x = x * x % n;
            if x == n - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}
fn sqrt_m1(q: u64) -> u64 {
    for z in 2..1000u64 {
        let i = pow_mod(z, (q - 1) / 4, q);
        if i * i % q == q - 1 {
            return i;
        }
    }
    panic!("no sqrt(-1) mod {}", q);
}
fn inv_mod(a: u64, q: u64) -> u64 {
    pow_mod(a, q - 2, q)
}
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

struct Logger {
    f: std::fs::File,
}
impl Logger {
    fn new(path: &str) -> Logger {
        Logger {
            f: OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .unwrap(),
        }
    }
    fn log(&mut self, s: &str) {
        println!("{}", s);
        let _ = writeln!(self.f, "{}", s);
        let _ = self.f.flush();
    }
}

fn inverse(g: &Elem) -> Elem {
    if g.delta == 0 {
        // (eps,0,-k, -eps * t^{-k} P)
        let p: Vec<(i16, i16)> = g.p.iter().map(|&(e, c)| (e - g.k, -(g.eps as i16) * c)).collect();
        let mut p = p; p.sort();
        Elem { eps: g.eps, delta: 0, k: -g.k, p }
    } else {
        // (eps,1,k, P') with P'(t) = -eps * t^{k} P(t^{-1})
        let p: Vec<(i16, i16)> = g.p.iter().map(|&(e, c)| (g.k - e, -(g.eps as i16) * c)).collect();
        let mut p = p; p.sort();
        Elem { eps: g.eps, delta: 1, k: g.k, p }
    }
}

fn ldist() {
    // usage: certify38 ldist D c e   -- exact length of the shortest kernel
    // element 2(t-1) mu t^{j0} (j0 in -2..=0) via meet-in-the-middle over
    // the radius-D ball: L = min_g d(g) + d(g^{-1} w).
    let t0 = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let d_max: u32 = args[2].parse().unwrap();
    let c: i32 = args[3].parse().unwrap();
    let e: i32 = args[4].parse().unwrap();
    // BFS with distances in RAM
    let gens = [
        Elem { eps: 1, delta: 1, k: 0, p: vec![] },
        Elem { eps: -1, delta: 1, k: 0, p: vec![] },
        Elem { eps: 1, delta: 1, k: -1, p: vec![(-1, -1), (0, 1)] },
    ];
    let mut dist: std::collections::HashMap<Box<[u8]>, u8> = std::collections::HashMap::new();
    let ident = Elem { eps: 1, delta: 0, k: 0, p: vec![] };
    let mut buf = Vec::new();
    encode(&ident, &mut buf);
    dist.insert(buf.clone().into_boxed_slice(), 0);
    let mut frontier = vec![ident];
    for d in 0..d_max {
        let mut nxt = Vec::new();
        for el in &frontier {
            for g in &gens {
                let ne = compose(g, el);
                encode(&ne, &mut buf);
                if !dist.contains_key(buf.as_slice()) {
                    dist.insert(buf.clone().into_boxed_slice(), (d + 1) as u8);
                    nxt.push(ne);
                }
            }
        }
        frontier = nxt;
        if d % 5 == 4 {
            eprintln!("[{:6.1}s] bfs layer {} done, ball {}", t0.elapsed().as_secs_f64(), d + 1, dist.len());
        }
    }
    eprintln!("[{:6.1}s] ball({}) = {}", t0.elapsed().as_secs_f64(), d_max, dist.len());
    // kernel elements: P_w = 2(t-1) mu t^{j0},  mu = c t^2 - e t + c
    let mut best = u32::MAX;
    let mut bestj = 99;
    let mut bestf = "";
    // f = 1:   2(t-1)mu        ;  f = 1+t:  2(t^2-1)mu
    let fams: [(&str, Vec<(i16, i32)>); 2] = [
        ("1", vec![(3, c), (2, -(e + c)), (1, c + e), (0, -c)]),
        ("1+t", vec![(4, c), (3, -e), (2, 0), (1, e), (0, -c)]),
    ];
    for (fname, coeffs) in &fams {
    for j0 in -4i16..=0 {
        let mut p: Vec<(i16, i16)> = coeffs
            .iter()
            .filter(|&&(_, v)| v != 0)
            .map(|&(ex, v)| (ex + j0, (2 * v) as i16))
            .collect();
        let _ = fname;
        p.sort();
        let w = Elem { eps: 1, delta: 0, k: 0, p };
        // L = min over g in ball of d(g) + d(g^{-1} w)
        let mut lmin = u32::MAX;
        for (key, &dg) in &dist {
            let mut pos = 0usize;
            let g = decode(key, &mut pos);
            let h = compose(&inverse(&g), &w);
            encode(&h, &mut buf);
            if let Some(&dh) = dist.get(buf.as_slice()) {
                let l = dg as u32 + dh as u32;
                if l < lmin {
                    lmin = l;
                }
            }
        }
        eprintln!("[{:6.1}s] f={} j0={}: L = {:?}", t0.elapsed().as_secs_f64(), fname, j0, if lmin == u32::MAX { None } else { Some(lmin) });
        if lmin < best { best = lmin; bestj = j0; bestf = fname; }
    }
    }
    if best == u32::MAX {
        println!("shape (c={}, e={}): kernel element NOT factorable within ball({}) — L > {}", c, e, d_max, 2 * d_max);
    } else {
        println!("shape (c={}, e={}): L = {} (f={}, j0={})  =>  n_T = {}", c, e, best, bestf, bestj, (best + 1) / 2);
    }
}

fn main() {
    {
        let args: Vec<String> = std::env::args().collect();
        if args.get(1).map(|s| s.as_str()) == Some("ldist") {
            ldist();
            return;
        }
    }
    let t0 = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let depth: usize = if args.len() > 1 {
        args[1].parse().expect("depth must be an integer")
    } else {
        38
    };
    assert!(depth <= 60, "encoding supports depth <= 60");
    let bound = 2 * depth as u64; // c_T <= 2d at any deviation depth <= d

    let state = "certify38_state";
    fs::create_dir_all(state).unwrap();
    let ball_path = format!("{}/ball_d{}.bin", state, depth);
    let layers_path = format!("{}/layers_d{}.txt", state, depth);
    let results_path = format!("{}/results_d{}.txt", state, depth);
    let mut lg = Logger::new(&format!("certify{}.log", depth));

    lg.log(&format!(
        "=== certify38 ===  depth {}  candidate bound c <= {}  (started)",
        depth, bound
    ));

    // ---------- resume info ----------
    let mut done_layers: Vec<(usize, u64, u64)> = Vec::new(); // (d, count, end_offset)
    if let Ok(txt) = fs::read_to_string(&layers_path) {
        for line in txt.lines() {
            let v: Vec<&str> = line.split_whitespace().collect();
            if v.len() == 3 {
                done_layers.push((
                    v[0].parse().unwrap(),
                    v[1].parse().unwrap(),
                    v[2].parse().unwrap(),
                ));
            }
        }
    }

    // ---------- Pass 1: symbolic BFS with checkpointing ----------
    let gens = [
        Elem { eps: 1, delta: 1, k: 0, p: vec![] },
        Elem { eps: -1, delta: 1, k: 0, p: vec![] },
        Elem { eps: 1, delta: 1, k: -1, p: vec![(-1, -1), (0, 1)] },
    ];

    let mut ball: Vec<u8>; // flat records, layers in order
    let mut counts: Vec<u64>;
    {
        let mut seen: HashSet<Box<[u8]>> = HashSet::with_capacity(1 << 20);
        let mut frontier_off: Vec<(usize, usize)>; // (pos,len) into ball
        let mut buf = Vec::new();

        if !done_layers.is_empty() {
            // resume: load ball.bin up to last completed offset, rebuild seen
            let (last_d, _, end_off) = *done_layers.last().unwrap();
            lg.log(&format!(
                "[resume] found {} completed layers (through depth {}), rebuilding state...",
                done_layers.len(),
                last_d
            ));
            let mut f = fs::File::open(&ball_path).expect("ball.bin missing for resume");
            ball = Vec::with_capacity(end_off as usize);
            f.take(end_off).read_to_end(&mut ball).unwrap();
            // rebuild seen + last frontier offsets
            let last_start = if done_layers.len() >= 2 {
                done_layers[done_layers.len() - 2].2 as usize
            } else {
                0
            };
            frontier_off = Vec::new();
            let mut pos = 0usize;
            while pos < ball.len() {
                let l = rec_len(&ball, pos);
                seen.insert(ball[pos..pos + l].to_vec().into_boxed_slice());
                if pos >= last_start {
                    frontier_off.push((pos, l));
                }
                pos += l;
            }
            counts = done_layers.iter().map(|x| x.1).collect();
            lg.log(&format!(
                "[resume] {} elements restored, frontier {}, {:.1}s",
                seen.len(),
                frontier_off.len(),
                t0.elapsed().as_secs_f64()
            ));
        } else {
            // fresh start
            let _ = fs::remove_file(&ball_path);
            let _ = fs::remove_file(&layers_path);
            let _ = fs::remove_file(&results_path);
            ball = Vec::new();
            let ident = Elem { eps: 1, delta: 0, k: 0, p: vec![] };
            encode(&ident, &mut buf);
            seen.insert(buf.clone().into_boxed_slice());
            frontier_off = vec![(0, buf.len())];
            ball.extend_from_slice(&buf);
            counts = vec![1];
            let mut lf = OpenOptions::new()
                .create(true)
                .append(true)
                .open(&layers_path)
                .unwrap();
            writeln!(lf, "0 1 {}", ball.len()).unwrap();
            let mut bf = OpenOptions::new()
                .create(true)
                .write(true)
                .open(&ball_path)
                .unwrap();
            bf.write_all(&ball).unwrap();
        }

        // expand layers
        for d in counts.len()..=depth {
            let mut next_off: Vec<(usize, usize)> = Vec::new();
            let layer_start = ball.len();
            for &(pos, len) in &frontier_off {
                let mut p = pos;
                let _ = len;
                let h = decode(&ball, &mut p);
                for g in &gens {
                    let ne = compose(g, &h);
                    encode(&ne, &mut buf);
                    if !seen.contains(buf.as_slice()) {
                        seen.insert(buf.clone().into_boxed_slice());
                        let at = ball.len();
                        ball.extend_from_slice(&buf);
                        next_off.push((at, buf.len()));
                    }
                }
            }
            let cnt = next_off.len() as u64;
            counts.push(cnt);
            // checkpoint: append new layer bytes + record
            let mut bf = OpenOptions::new().append(true).open(&ball_path).unwrap();
            bf.write_all(&ball[layer_start..]).unwrap();
            bf.flush().unwrap();
            let mut lf = OpenOptions::new().append(true).open(&layers_path).unwrap();
            writeln!(lf, "{} {} {}", d, cnt, ball.len()).unwrap();
            let pubv = if d < PUBLISHED.len() { PUBLISHED[d] as i64 } else { -1 };
            let status = if pubv < 0 {
                "(no published value)".to_string()
            } else if pubv as u64 == cnt {
                "OK".to_string()
            } else {
                format!("*** MISMATCH vs published {} ***", pubv)
            };
            lg.log(&format!(
                "[bfs] layer {:2}: {:>10}  {}  [{:.1}s, ball {}]",
                d,
                cnt,
                status,
                t0.elapsed().as_secs_f64(),
                seen.len()
            ));
            frontier_off = next_off;
        }
        lg.log(&format!(
            "[bfs] done. ball = {} elements, {} MB flat, {:.1}s",
            seen.len(),
            ball.len() / 1_000_000,
            t0.elapsed().as_secs_f64()
        ));
        // seen dropped here (frees RAM before pass 2)
    }

    let nball: u64 = counts.iter().sum();

    // published-vs-generic comparison summary
    let mut mismatches: Vec<String> = Vec::new();
    for d in 0..=depth.min(PUBLISHED.len() - 1) {
        if counts[d] != PUBLISHED[d] {
            mismatches.push(format!(
                "depth {}: generic {} vs published {}",
                d, counts[d], PUBLISHED[d]
            ));
        }
    }

    // ---------- Pass 2: candidate evaluation ----------
    // candidates: coprime x>y>=1, c = (x^2+y^2)/2 if both odd else x^2+y^2, 5 <= c <= bound
    let mut cands: Vec<(u64, u64, u64)> = Vec::new();
    let lim = 2 * bound;
    let mut x = 2u64;
    while x * x <= lim {
        for y in 1..x {
            let s = x * x + y * y;
            if s > lim {
                break;
            }
            if gcd(x, y) != 1 {
                continue;
            }
            let c = if x % 2 == 1 && y % 2 == 1 { s / 2 } else { s };
            if c >= 5 && c <= bound {
                cands.push((x, y, c));
            }
        }
        x += 1;
    }
    cands.sort_by_key(|t| t.2);
    lg.log(&format!(
        "[eval] {} candidate rotation numbers with c <= {}",
        cands.len(),
        bound
    ));

    let mut done_cands: HashSet<(u64, u64)> = HashSet::new();
    let mut prior_fail = 0u64;
    if let Ok(txt) = fs::read_to_string(&results_path) {
        for line in txt.lines() {
            let v: Vec<&str> = line.split_whitespace().collect();
            if v.len() >= 4 {
                done_cands.insert((v[0].parse().unwrap(), v[1].parse().unwrap()));
                if v[3] != "CLEAN" {
                    prior_fail += 1;
                }
            }
        }
        if !done_cands.is_empty() {
            lg.log(&format!(
                "[resume] {} candidates already checked, skipping them",
                done_cands.len()
            ));
        }
    }

    // four independent primes == 1 (mod 4); CLEAN under ANY single prime is exact.
    let primes: [u64; 4] = [2_000_000_033, 1_900_000_097, 1_800_000_049, 1_700_000_009];
    for &q in &primes {
        assert!(is_prime(q) && q % 4 == 1, "bad prime {}", q);
    }

    // returns (distinct_count, collision_pairs as element-offset pairs)
    let eval_candidate = |xx: u64, yy: u64, q: u64, ball: &[u8], keys: &mut Vec<u128>, offs: &[u32]| -> (u64, Vec<(u32, u32)>) {
        let iq = sqrt_m1(q);
        let num = (xx + yy * iq) % q;
        let den = (xx + q - yy * iq % q) % q;
        let z = num * inv_mod(den, q) % q;
        let zin = inv_mod(z, q);
        // power table for exponents -OFF..=OFF
        let n_pow = 2 * OFF as usize + 1;
        let mut pw = vec![0u64; n_pow];
        let mut cur = pow_mod(zin, OFF as u64, q);
        for e in 0..n_pow {
            pw[e] = cur;
            cur = cur * z % q;
        }
        keys.clear();
        let mut pos = 0usize;
        let mut idx: u32 = 0;
        while pos < ball.len() {
            let eps = ball[pos];
            let delta = ball[pos + 1];
            let kk = ball[pos + 2];
            let n = ball[pos + 3] as usize;
            let mut v: u64 = 0;
            let mut p = pos + 4;
            for _ in 0..n {
                let ei = ball[p] as usize; // already offset by OFF
                let c = i16::from_le_bytes([ball[p + 1], ball[p + 2]]) as i64;
                let cm = (c.rem_euclid(q as i64)) as u64;
                v = (v + cm * pw[ei]) % q;
                p += 3;
            }
            let cls: u64 = ((kk as u64) << 2) | ((delta as u64) << 1) | (eps as u64);
            // pack: [cls:10][value:31] in high 64, element index in low 32
            keys.push((((cls as u128) << 96) | ((v as u128) << 32)) | idx as u128);
            pos = p;
            idx += 1;
        }
        keys.sort_unstable();
        let mut distinct = 1u64;
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        let mut g_start = 0usize;
        for i in 1..=keys.len() {
            if i == keys.len() || (keys[i] >> 32) != (keys[i - 1] >> 32) {
                let glen = i - g_start;
                if glen > 1 && pairs.len() < 2_000_000 {
                    for a in g_start..i {
                        for b in (a + 1)..i {
                            let ia = (keys[a] & 0xffff_ffff) as u32;
                            let ib = (keys[b] & 0xffff_ffff) as u32;
                            pairs.push((ia.min(ib).min(offs.len() as u32 - 1), ia.max(ib)));
                        }
                    }
                }
                g_start = i;
            }
            if i < keys.len() && (keys[i] >> 32) != (keys[i - 1] >> 32) {
                distinct += 1;
            }
        }
        (distinct, pairs)
    };

    let ball_bytes = fs::read(&ball_path).unwrap();
    // element index -> record offset (for pair export)
    let mut offs: Vec<u32> = Vec::with_capacity(nball as usize);
    {
        let mut pos = 0usize;
        while pos < ball_bytes.len() {
            offs.push(pos as u32);
            pos += rec_len(&ball_bytes, pos);
        }
    }
    let mut keys: Vec<u128> = Vec::with_capacity(nball as usize);

    let mut n_fail = prior_fail;
    let mut exported: Vec<String> = Vec::new();
    let todo: Vec<(u64, u64, u64)> = cands
        .iter()
        .filter(|(x, y, _)| !done_cands.contains(&(*x, *y)))
        .cloned()
        .collect();
    for (idx, (xx, yy, c)) in todo.iter().enumerate() {
        let (d1, p1) = eval_candidate(*xx, *yy, primes[0], &ball_bytes, &mut keys, &offs);
        let mut verdict = String::from("CLEAN");
        let mut deficit = nball - d1;
        if d1 != nball {
            // intersect collision pairs across the remaining primes:
            // a TRUE collision pair collides modulo EVERY prime.
            let mut surv: HashSet<(u32, u32)> = p1.into_iter().collect();
            for &q in &primes[1..] {
                if surv.is_empty() {
                    break;
                }
                let (_, pq) = eval_candidate(*xx, *yy, q, &ball_bytes, &mut keys, &offs);
                let pq: HashSet<(u32, u32)> = pq.into_iter().collect();
                surv.retain(|p| pq.contains(p));
            }
            if surv.is_empty() {
                verdict = String::from("CLEAN"); // modular accidents only
                deficit = 0;
            } else {
                // export surviving pairs for exact verification in Q(i)
                let fname = format!("{}/pairs_d{}_{}_{}.txt", state, depth, xx, yy);
                let mut pf = BufWriter::new(fs::File::create(&fname).unwrap());
                writeln!(pf, "# x={} y={} c={} pairs={}", xx, yy, c, surv.len()).unwrap();
                let dump = |o: u32, pf: &mut BufWriter<fs::File>| {
                    let mut p = o as usize;
                    let e = decode(&ball_bytes, &mut p);
                    write!(pf, "{} {} {} {}", e.eps, e.delta, e.k, e.p.len()).unwrap();
                    for (ex, cc) in e.p {
                        write!(pf, " {} {}", ex, cc).unwrap();
                    }
                };
                for (a, b) in &surv {
                    dump(offs[*a as usize], &mut pf);
                    write!(pf, " | ").unwrap();
                    dump(offs[*b as usize], &mut pf);
                    writeln!(pf).unwrap();
                }
                verdict = format!("SUSPECT({} pairs -> {})", surv.len(), fname);
                deficit = surv.len() as u64;
                exported.push(fname);
                n_fail += 1;
            }
        }
        let mut rf = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&results_path)
            .unwrap();
        writeln!(rf, "{} {} {} {} deficit={}", xx, yy, c, verdict, deficit).unwrap();
        lg.log(&format!(
            "[eval {:>3}/{}] legs ({},{})  c={:<3}  {}  deficit={}  [{:.1}s]",
            idx + 1 + done_cands.len(),
            cands.len(),
            xx,
            yy,
            c,
            verdict,
            deficit,
            t0.elapsed().as_secs_f64()
        ));
    }

    // ---------- final verdict ----------
    let mut out = String::new();
    out.push_str("==================== FINAL RESULT (paste this back) ====================\n");
    out.push_str(&format!(
        "certify38  depth={}  ball={}  candidates={}  runtime={:.0}s\n",
        depth,
        nball,
        cands.len(),
        t0.elapsed().as_secs_f64()
    ));
    if mismatches.is_empty() {
        out.push_str(&format!(
            "GENERIC LAYER COUNTS: match published A396406 a(0)..a({}) exactly.\n",
            depth.min(PUBLISHED.len() - 1)
        ));
    } else {
        out.push_str("GENERIC LAYER COUNTS: *** MISMATCH vs published A396406 ***\n");
        for m in &mismatches {
            out.push_str(&format!("  {}\n", m));
        }
    }
    if n_fail == 0 {
        out.push_str(&format!(
            "CANDIDATES: all clean. CERTIFIED: n_T > {} for every unequal-leg rational\n\
             triangle (c <= {} checked exhaustively; c > {} excluded by the effective\n\
             theorem c_T <= 2d).",
            depth, bound, bound
        ));
        if depth >= 38 && mismatches.is_empty() {
            out.push_str(
                "\nCONSEQUENCE: published A396406 terms a(31)..a(38) ARE the generic terms.",
            );
        }
    } else {
        out.push_str(&format!(
            "CANDIDATES: {} shape(s) have pairs colliding mod ALL {} primes — see {}.\n\
             Run the exact checker on each exported pairs file for the final word:\n\
                 python3 ../exact_check.py certify38_state/pairs_d{}_X_Y.txt\n\
             (a pair confirmed there is an exact deviation; refuted pairs are\n\
             modular accidents).",
            n_fail,
            primes.len(),
            results_path,
            depth
        ));
        for f in &exported {
            out.push_str(&format!("\n  exported: {}", f));
        }
    }
    out.push_str("\n=========================================================================");
    lg.log(&out);
    fs::write(format!("certify{}_final.txt", depth), &out).unwrap();
}
