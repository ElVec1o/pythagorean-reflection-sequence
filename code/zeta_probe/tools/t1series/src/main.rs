// t1series -- high-precision extraction of t1 = P12/Se at the travel poles q_m,
// and Taylor-coefficient / radius analysis of the series  t1/tau = sum_k c_k tau^k.
//
// GOAL (Option 2): the U-transcendence gate s<1 reduces to the t1 series being CONVERGENT
// (radius > tau_1 = 0.0905) rather than asymptotic.  If the c_k are bounded (geometric),
// s(tau)=(q/p)t1 is a convergent series with s->1/4, and s<1 follows by SUMMING it -- no
// steepest-descent error term anywhere.  This tool produces the c_k to high precision so the
// growth |c_k|^{1/k} (hence the radius) can be read off, and the rationals identified.
//
// TWO MODES:
//   COMPUTE (default):  t1series PREC_DIGITS M_MAX        e.g.  t1series 1200 35
//       computes t1(q_m) for m=1..M_MAX via the STABLE transfer-matrix cocycle,
//       appends "m tau P12 Se t1" (full precision) to  t1_p{PREC}.txt
//       * progress + ETA to stderr, * resumable (skips already-done m), * scalar (NO OOM)
//   ANALYZE:            t1series analyze PREC_DIGITS M_FIT [FILE]   e.g.  t1series analyze 1200 28
//       reads the data file, Vandermonde-solves for c_0..c_{M_FIT-1} (degree M_FIT-1 fit on
//       the first M_FIT poles), prints each c_k (45 digits) and |c_k|^{1/k}; rational-ID on host.
//
// Build:  cd t1series && cargo build --release
// Run:    ./target/release/t1series 1200 35   2> progress.log     # then:
//         ./target/release/t1series analyze 1200 28

use rug::{ops::Pow, Float};
use std::collections::HashSet;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader, Write};
use std::time::Instant;

#[inline]
fn mul(a: &Float, b: &Float) -> Float { Float::with_val(a.prec(), a * b) }
#[inline]
fn add(a: &Float, b: &Float) -> Float { Float::with_val(a.prec(), a + b) }
#[inline]
fn sub(a: &Float, b: &Float) -> Float { Float::with_val(a.prec(), a - b) }
#[inline]
fn divf(a: &Float, b: &Float) -> Float { Float::with_val(a.prec(), a / b) }
#[inline]
fn powu(q: &Float, n: u32) -> Float { Float::with_val(q.prec(), q.pow(n)) }

fn aq(k: u32, q: &Float, one: &Float, two: &Float) -> Float {
    divf(&mul(two, q), &sub(one, &powu(q, k + 1)))
}
fn cq(k: u32, q: &Float, one: &Float, two: &Float) -> Float {
    let a = divf(&mul(two, &powu(q, k + 3)), &sub(one, &powu(q, k + 2)));
    let b = divf(&mul(two, &powu(q, k + 2)), &sub(one, &powu(q, k + 1)));
    sub(&a, &b)
}
fn sigma_travel(q: &Float, one: &Float, two: &Float, eps: &Float) -> Float {
    let p = q.prec();
    let mut tot = Float::with_val(p, 0);
    let mut prod = Float::with_val(p, 1);
    let mut j: u32 = 0;
    loop {
        let k = 1 + 2 * j;
        tot = add(&tot, &mul(&aq(k, q, one, two), &prod));
        prod = mul(&prod, &cq(k, q, one, two));
        if j > 40 && prod.clone().abs() < *eps { break; }
        j += 1;
        if j > 5_000_000 { break; }
    }
    tot
}
fn find_pole(seed: f64, prec: u32, one: &Float, two: &Float, eps: &Float, tol: &Float) -> Float {
    let mut q0 = Float::with_val(prec, seed);
    let mut q1 = Float::with_val(prec, seed * (1.0 + 1e-5));
    let mut f0 = sub(&sigma_travel(&q0, one, two, eps), one);
    let mut f1 = sub(&sigma_travel(&q1, one, two, eps), one);
    for _ in 0..200 {
        let df = sub(&f1, &f0);
        if df.clone().abs() < *eps { break; }
        let step = divf(&mul(&f1, &sub(&q1, &q0)), &df);
        let q2 = sub(&q1, &step);
        let conv = sub(&q2, &q1).abs() < *tol;
        q0 = q1; f0 = f1; q1 = q2;
        f1 = sub(&sigma_travel(&q1, one, two, eps), one);
        if conv { break; }
    }
    q1
}
fn cocycle(q: &Float, n_iter: u64, one: &Float, two: &Float) -> (Float, Float) {
    let p = q.prec();
    let mut x = Float::with_val(p, 0);
    let mut y = Float::with_val(p, 1);
    let mut xx = Float::with_val(p, 1);
    let mut yy = Float::with_val(p, 0);
    let mut qn = Float::with_val(p, 1);
    for _ in 1..=n_iter {
        qn = mul(&qn, q);
        let q2n = mul(&qn, &qn);
        let q3n = mul(&q2n, &qn);
        let amp = add(one, &mul(two, &q2n));
        let amm = sub(one, &mul(two, &q2n));
        let tqn = mul(two, &qn);
        let tq3n = mul(two, &q3n);
        let nx = sub(&mul(&x, &amp), &mul(&y, &tqn));
        let ny = add(&mul(&x, &tq3n), &mul(&y, &amm));
        let nxx = sub(&mul(&xx, &amp), &mul(&yy, &tqn));
        let nyy = add(&mul(&xx, &tq3n), &mul(&yy, &amm));
        x = nx; y = ny; xx = nxx; yy = nyy;
    }
    (yy, y) // P12 = Y, Se = y
}

fn data_path(prec_digits: u32) -> String { format!("t1_p{}.txt", prec_digits) }

fn run_compute(prec_digits: u32, m_max: u32) {
    let prec: u32 = (prec_digits as f64 * 3.3219 + 24.0) as u32;
    let out_digits = prec_digits as usize;
    let one = Float::with_val(prec, 1);
    let two = Float::with_val(prec, 2);
    let eps = Float::with_val(prec, Float::parse(format!("1e-{}", prec_digits + 6)).unwrap());
    let tol = Float::with_val(prec, Float::parse(format!("1e-{}", prec_digits - 4)).unwrap());
    let pi = Float::with_val(prec, rug::float::Constant::Pi);

    let path = data_path(prec_digits);
    let mut done: HashSet<u32> = HashSet::new();
    if let Ok(f) = std::fs::File::open(&path) {
        for line in BufReader::new(f).lines().flatten() {
            if let Some(tok) = line.split_whitespace().next() {
                if let Ok(m) = tok.parse::<u32>() { done.insert(m); }
            }
        }
    }
    let mut out = OpenOptions::new().create(true).append(true).open(&path).unwrap();
    eprintln!("# COMPUTE: prec={} digits ({} bits), M={}, file={}, {} already done",
              prec_digits, prec, m_max, path, done.len());

    let start = Instant::now();
    let mut computed = 0u32;
    let todo: Vec<u32> = (1..=m_max).filter(|m| !done.contains(m)).collect();
    let total = todo.len() as u32;

    for m in todo {
        let wf = (m as f64 + 0.5) * std::f64::consts::PI;
        let tauf = 2.0 / (wf * wf);
        let seed = (-tauf).exp();
        let q = find_pole(seed, prec, &one, &two, &eps, &tol);
        let tau = Float::with_val(prec, -q.clone().ln());
        let w = Float::with_val(prec, (Float::with_val(prec, &two / &tau)).sqrt());
        let target = Float::with_val(prec, (m as f64 + 0.5) * &pi);
        if sub(&w, &target).abs() > Float::with_val(prec, 0.5) {
            eprintln!("  m={}: WARNING wrong root; skipping", m);
            continue;
        }
        let qf = q.to_f64();
        let n_iter = (0.80 * (prec_digits as f64 + 6.0) / (1.0 - qf)).ceil() as u64;
        let (p12, se) = cocycle(&q, n_iter, &one, &two);
        let t1 = divf(&p12, &se);
        let ratio = divf(&t1, &tau).to_f64();
        let ok = (ratio - 0.25).abs() < 0.05;
        writeln!(out, "{} {} {} {} {}", m,
            tau.to_string_radix(10, Some(out_digits)),
            p12.to_string_radix(10, Some(out_digits)),
            se.to_string_radix(10, Some(out_digits)),
            t1.to_string_radix(10, Some(out_digits))).unwrap();
        out.flush().unwrap();
        computed += 1;
        let elapsed = start.elapsed().as_secs_f64();
        let per = elapsed / computed as f64;
        let eta = per * (total - computed) as f64;
        eprintln!("  m={:<3} tau={:.3e} N={:<9} t1/tau={:.10} {}  [{}/{}]  {:.1}s/pole  ETA {:.0}s ({:.1}h)",
            m, tau.to_f64(), n_iter, ratio,
            if ok { "OK" } else { "*** SANITY FAIL ***" },
            computed, total, per, eta, eta / 3600.0);
    }
    eprintln!("# done. {} poles in {} ({:.0}s). Now run:  t1series analyze {} {}",
              computed, path, start.elapsed().as_secs_f64(), prec_digits, m_max.min(30));
}

// Gaussian elimination with partial pivoting: solve A x = b.
fn solve(mut a: Vec<Vec<Float>>, mut b: Vec<Float>, prec: u32) -> Vec<Float> {
    let n = b.len();
    for col in 0..n {
        let mut piv = col;
        for r in (col + 1)..n {
            if a[r][col].clone().abs() > a[piv][col].clone().abs() { piv = r; }
        }
        a.swap(col, piv); b.swap(col, piv);
        let d = a[col][col].clone();
        for r in (col + 1)..n {
            let f = Float::with_val(prec, &a[r][col] / &d);
            for c in col..n {
                let t = Float::with_val(prec, &f * &a[col][c]);
                a[r][c] = Float::with_val(prec, &a[r][c] - &t);
            }
            let t = Float::with_val(prec, &f * &b[col]);
            b[r] = Float::with_val(prec, &b[r] - &t);
        }
    }
    let mut x = vec![Float::with_val(prec, 0); n];
    for i in (0..n).rev() {
        let mut s = b[i].clone();
        for j in (i + 1)..n {
            let t = Float::with_val(prec, &a[i][j] * &x[j]);
            s = Float::with_val(prec, &s - &t);
        }
        x[i] = Float::with_val(prec, &s / &a[i][i]);
    }
    x
}

fn run_analyze(prec_digits: u32, m_fit: usize, file: &str) {
    let prec: u32 = (prec_digits as f64 * 3.3219 + 64.0) as u32;
    let mut rows: Vec<(u32, Float, Float)> = Vec::new();
    let f = match std::fs::File::open(file) {
        Ok(f) => f,
        Err(_) => { eprintln!("cannot open {}", file); return; }
    };
    for line in BufReader::new(f).lines().flatten() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        if toks.len() >= 5 {
            if let Ok(m) = toks[0].parse::<u32>() {
                if let (Ok(pt), Ok(p1)) = (Float::parse(toks[1]), Float::parse(toks[4])) {
                    rows.push((m, Float::with_val(prec, pt), Float::with_val(prec, p1)));
                }
            }
        }
    }
    rows.sort_by_key(|r| r.0);
    if rows.len() < m_fit {
        eprintln!("# only {} poles in {}, need {} for a degree-{} fit -- compute more.",
                  rows.len(), file, m_fit, m_fit.saturating_sub(1));
        return;
    }
    let n = m_fit;
    let taus: Vec<Float> = rows[..n].iter().map(|r| r.1.clone()).collect();
    let vals: Vec<Float> = rows[..n].iter().map(|r| divf(&r.2, &r.1)).collect();
    let mut a = vec![vec![Float::with_val(prec, 0); n]; n];
    for i in 0..n {
        let mut p = Float::with_val(prec, 1);
        for j in 0..n { a[i][j] = p.clone(); p = mul(&p, &taus[i]); }
    }
    let c = solve(a, vals, prec);
    println!("# t1/tau = sum_k c_k tau^k   (fit: first {} poles, tau in [{:.2e},{:.2e}], prec {} digits)",
             n, taus[n - 1].to_f64(), taus[0].to_f64(), prec_digits);
    println!("# known: c0=1/4, c1=3/16, c2=13/96, c3=13/256, c4=-629/7680");
    let mut maxgrow = 0.0f64;
    for k in 0..n {
        let ck = &c[k];
        let grow = if k >= 1 {
            let lc = Float::with_val(prec, ck.clone().abs().ln());
            Float::with_val(prec, &lc / k as f64).exp().to_f64()
        } else { 0.0 };
        if k >= 3 && k + 4 <= n && grow > maxgrow { maxgrow = grow; }
        println!("c[{:>2}] = {}   |c|^(1/k) = {:.5}", k, ck.to_string_radix(10, Some(45)), grow);
    }
    println!("# trimmed limsup |c_k|^(1/k) ~ {:.4}  =>  radius ~ {:.4}  (need > tau_1=0.0905 for convergence)",
             maxgrow, if maxgrow > 0.0 { 1.0 / maxgrow } else { 0.0 });
    println!("# rational-ID each c_k on the host (continued fraction / PSLQ); send the c_k list back.");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("analyze") {
        let prec_digits: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1000);
        let m_fit: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(20);
        let file = args.get(4).cloned().unwrap_or_else(|| data_path(prec_digits));
        run_analyze(prec_digits, m_fit, &file);
    } else {
        let prec_digits: u32 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1200);
        let m_max: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(35);
        run_compute(prec_digits, m_max);
    }
}
