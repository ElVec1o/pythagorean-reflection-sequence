// U-gate / THE-BOUND verifier for the A396406 transcendence proof.
//
// For each travel pole m it computes, at ADAPTIVE precision:
//   * the pole tau_m  (Newton on  Sigma_1^T(tau) = 1)
//   * THE BOUND constant  boundC = |Y3(1/q) - (3/sqrt2) tau^{3/2} sin w| / tau^{5/2}
//        -> closing U needs this to stay BOUNDED in m (numerically ~3.71).
//   * the gate margin      gmarg  = (1-q)/q - t1,  t1 = P12/Se   (must be > 0)
//   * the residual         R/tau^{5/2}  (= P12 - E, the assembly residual; ~0.258)
//
// Output is appended to a CSV (resumable). Progress + ETA printed each pole.
//
// Build (from THIS space-free dir, NOT the "XXXXX MATH PROOF" path):
//     cd /Users/vico/Documents/elvec1o/u5b_gate && cargo build --release
// Run:
//     ./target/release/u5b_gate --max 400 --out gate.csv
//     ./target/release/u5b_gate --max 4000 --out bound.csv --bound-only   # fast, large m
// Resume: just re-run the same command; already-computed m are skipped.

use rug::ops::Pow;
use rug::Float;
use std::env;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader, Write};
use std::time::Instant;

macro_rules! f {
    ($p:expr, $e:expr) => {
        Float::with_val($p, $e)
    };
}
fn fexp(x: &Float, p: u32) -> Float { Float::with_val(p, x.exp_ref()) }
fn fsin(x: &Float, p: u32) -> Float { Float::with_val(p, x.sin_ref()) }
fn fcos(x: &Float, p: u32) -> Float { Float::with_val(p, x.cos_ref()) }
fn fsqrt(x: &Float, p: u32) -> Float { Float::with_val(p, x.sqrt_ref()) }
fn fabs(x: &Float, p: u32) -> Float { Float::with_val(p, x.abs_ref()) }
fn pi(p: u32) -> Float { Float::with_val(p, rug::float::Constant::Pi) }

// Sigma_1^T(q) = sum_k 2q a^k q^{k^2+2k} / [ (q^2;q^2)_{k+1} (q^3;q^2)_k ],  a = -2(1-q)
fn sigt(q: &Float, p: u32) -> Float {
    let one = f!(p, 1.0);
    let q2 = f!(p, q * q);
    let q3 = f!(p, &q2 * q);
    let a = f!(p, -2.0 * f!(p, &one - q));
    let twoq = f!(p, 2.0 * q);
    let thr = f!(p, f!(p, 2.0).pow(-(p as i32) + 30));
    let mut s = f!(p, 0.0);
    let mut ak = f!(p, 1.0);          // a^k
    let mut qk = f!(p, 1.0);          // q^{k^2+2k}
    let mut poch2 = f!(p, &one - &q2);// (q^2;q^2)_{k+1}, k=0 -> (1-q^2)
    let mut poch3 = f!(p, 1.0);       // (q^3;q^2)_k, k=0 -> 1
    let mut q2k = f!(p, 1.0);         // q^{2k}
    let mut maxt = f!(p, 0.0);
    let mut k: u64 = 0;
    loop {
        let mut term = f!(p, &twoq * &ak);
        term *= &qk;
        let den = f!(p, &poch2 * &poch3);
        term /= &den;
        s += &term;
        let at = fabs(&term, p);
        if at > maxt { maxt = at.clone(); }
        if k > 3 && at < f!(p, &maxt * &thr) { break; }
        ak *= &a;
        let q2kq3 = f!(p, &q2k * &q3); // q^{2k+3}
        qk *= &q2kq3;
        let q2kq4 = f!(p, &q2kq3 * q); // q^{2k+4}
        poch2 *= f!(p, &one - &q2kq4);
        poch3 *= f!(p, &one - &q2kq3);
        q2k *= &q2;
        k += 1;
        if k > 60_000_000 { break; }
    }
    s
}

// Y3(x) = sum_k d_k x^{2k+3},  d_k = b^k q^{k^2+3k} / [ (q^2;q^2)_k (q^5;q^2)_k ],  b=-2(1-q)
// returns (sum, max|term|) so the caller can detect cancellation.
fn y3(x: &Float, q: &Float, p: u32) -> (Float, Float) {
    let one = f!(p, 1.0);
    let q2 = f!(p, q * q);
    let q4 = f!(p, &q2 * &q2);
    let q5 = f!(p, &q4 * q);
    let b = f!(p, -2.0 * f!(p, &one - q));
    let x2 = f!(p, x * x);
    let thr = f!(p, f!(p, 2.0).pow(-(p as i32) + 30));
    let mut s = f!(p, 0.0);
    let mut bk = f!(p, 1.0);          // b^k
    let mut qk3 = f!(p, 1.0);         // q^{k^2+3k}
    let mut p2 = f!(p, 1.0);          // (q^2;q^2)_k
    let mut p5 = f!(p, 1.0);          // (q^5;q^2)_k
    let mut x2k3 = f!(p, f!(p, x * &x2)); // x^3 = x*x^2
    let mut q2k = f!(p, 1.0);         // q^{2k}
    let mut maxt = f!(p, 0.0);
    let mut k: u64 = 0;
    loop {
        let mut term = f!(p, &bk * &qk3);
        term *= &x2k3;
        let den = f!(p, &p2 * &p5);
        term /= &den;
        s += &term;
        let at = fabs(&term, p);
        if at > maxt { maxt = at.clone(); }
        if k > 3 && at < f!(p, &maxt * &thr) { break; }
        bk *= &b;
        let q2kq4 = f!(p, &q2k * &q4);     // q^{2k+4}
        qk3 *= &q2kq4;
        let q2kq2 = f!(p, &q2k * &q2);     // q^{2k+2}
        p2 *= f!(p, &one - &q2kq2);
        let q2kq5 = f!(p, &q2k * &q5);     // q^{2k+5}
        p5 *= f!(p, &one - &q2kq5);
        x2k3 *= &x2;
        q2k *= &q2;
        k += 1;
        if k > 60_000_000 { break; }
    }
    (s, maxt)
}

fn sigt_w(w: &Float, p: u32) -> Float {
    let tau = f!(p, 2.0 / f!(p, w * w));
    let q = fexp(&f!(p, -&tau), p);
    sigt(&q, p)
}

// Newton on g(w) = Sigma_1^T(2/w^2) - 1, landing on the m-th travel pole.
fn find_pole(m: u64, p: u32) -> Float {
    let pi_ = pi(p);
    let mut w = f!(p, f!(p, m as f64 + 0.5) * &pi_);
    let tau0 = f!(p, 2.0 / f!(p, &w * &w));
    w -= f!(p, f!(p, (2.0f64).sqrt() / 36.0) * fsqrt(&tau0, p));
    let hrel = f!(p, f!(p, 10.0).pow(-((p as i32) / 12)));
    let h = f!(p, &w * &hrel);
    let tol = f!(p, f!(p, 10.0).pow(-((p as i32) / 4)));
    for _ in 0..60 {
        let g = f!(p, sigt_w(&w, p) - 1.0);
        let wp = f!(p, &w + &h);
        let wm = f!(p, &w - &h);
        let gp = f!(p, f!(p, sigt_w(&wp, p) - sigt_w(&wm, p)) / f!(p, 2.0 * &h));
        if gp == 0.0 { break; }
        let dw = f!(p, &g / &gp);
        w -= &dw;
        if fabs(&dw, p) < f!(p, &w * &tol) { break; }
    }
    w
}

fn log2_ratio(num: &Float, den: &Float, p: u32) -> f64 {
    // log2(|num|/|den|), guarded
    let r = f!(p, fabs(num, p) / f!(p, fabs(den, p) + f!(p, f!(p, 10.0).pow(-(p as i32)))));
    let l = Float::with_val(p, r.ln_ref());
    (l.to_f64()) / std::f64::consts::LN_2
}

fn fmt_eta(secs: f64) -> String {
    if secs < 90.0 { format!("{:.0}s", secs) }
    else if secs < 5400.0 { format!("{:.1}m", secs / 60.0) }
    else { format!("{:.1}h", secs / 3600.0) }
}

// Neville polynomial extrapolation of the points (x_i, y_i) evaluated at x=0.
fn neville_at_zero(pts: &[(Float, Float)], p: u32) -> Float {
    let n = pts.len();
    let mut col: Vec<Float> = pts.iter().map(|(_, y)| Float::with_val(p, y)).collect();
    let xs: Vec<Float> = pts.iter().map(|(x, _)| Float::with_val(p, x)).collect();
    for k in 1..n {
        for i in (k..n).rev() {
            // evaluate at x=0:  P[i] = (x[i]*P[i-1] - x[i-k]*P[i]) / (x[i] - x[i-k])
            let num = Float::with_val(p, Float::with_val(p, &xs[i] * &col[i - 1]) - Float::with_val(p, &xs[i - k] * &col[i]));
            let den = Float::with_val(p, &xs[i] - &xs[i - k]);
            col[i] = Float::with_val(p, &num / &den);
        }
    }
    col[n - 1].clone()
}
// number of digits two extrapolants agree to
fn stable_digits(a: &Float, b: &Float, p: u32) -> usize {
    let diff = Float::with_val(p, Float::with_val(p, a - b).abs());
    if diff == 0.0 { return 200; }
    let l = Float::with_val(p, diff.ln_ref()).to_f64() / std::f64::consts::LN_10;
    (-l).max(0.0) as usize
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut maxm: u64 = 400;
    let mut out = String::from("gate.csv");
    let mut bound_only = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--max" => { maxm = args[i + 1].parse().unwrap(); i += 2; }
            "--out" => { out = args[i + 1].clone(); i += 2; }
            "--bound-only" => { bound_only = true; i += 1; }
            _ => { i += 1; }
        }
    }

    // resume: collect already-done m
    let mut done: std::collections::HashSet<u64> = std::collections::HashSet::new();
    if let Ok(file) = std::fs::File::open(&out) {
        for line in BufReader::new(file).lines().flatten() {
            if let Some(c) = line.split(',').next() {
                if let Ok(v) = c.parse::<u64>() { done.insert(v); }
            }
        }
    }
    let mut fh = OpenOptions::new().create(true).append(true).open(&out).unwrap();
    if done.is_empty() {
        writeln!(fh, "m,tau,t1_over_tau,gatemargin_over_tau,boundC,R_over_tau25,abs_sinw,prec_bits,r25_hp,sinw_hp,tau_hp").unwrap();
        fh.flush().unwrap();
    }

    let sqrt2 = (2.0f64).sqrt();
    let start = Instant::now();
    let mut done_this_run: u64 = 0;
    let total_todo = (1..=maxm).filter(|m| !done.contains(m)).count() as u64;

    println!("# U-gate verifier: m=1..{}  out={}  mode={}",
        maxm, out, if bound_only { "BOUND-ONLY (fast)" } else { "FULL (gate+bound)" });
    println!("# closing U needs boundC BOUNDED in m (~3.71) and gatemargin>0 at every pole.");
    println!("# {:>4} {:>11} {:>10} {:>12} {:>9} {:>9} {:>7} {:>6} {:>8}",
        "m", "tau", "t1/tau", "gatemarg/t", "boundC", "R/t^2.5", "|sinw|", "prec", "ETA");

    let mut accum: Vec<(Float, Float)> = Vec::new(); // (tau, |c2|) for in-Rust Neville extraction of s1,s2,s3,s4
    for m in 1..=maxm {
        if done.contains(&m) { continue; }
        // adaptive precision: bound is well-conditioned; Y3(1) (gate) loses ~1.5m digits.
        let base_digits = if bound_only { 90.0 + 0.7 * (m as f64) } else { 70.0 + 1.6 * (m as f64) };
        let mut prec: u32 = 200 + (base_digits * 3.33) as u32;

        let (mut tau, mut q, mut w);
        let (mut y3q, mut maxtq);
        let mut y3_1 = f!(prec, 0.0);
        loop {
            w = find_pole(m, prec);
            tau = f!(prec, 2.0 / f!(prec, &w * &w));
            q = fexp(&f!(prec, -&tau), prec);
            let r = y3(&f!(prec, 1.0 / &q), &q, prec); // Y3(1/q): well-conditioned
            y3q = r.0; maxtq = r.1;
            let mut canc = log2_ratio(&maxtq, &y3q, prec); // cancellation bits in the bound series
            if !bound_only {
                let r1 = y3(&f!(prec, 1.0), &q, prec); // Y3(1): catastrophic near the pole
                y3_1 = r1.0;
                let c1 = log2_ratio(&r1.1, &y3_1, prec);
                if c1 > canc { canc = c1; }
            }
            if (canc as i64) + 640 < (prec as i64) { break; } // ~190-digit clean margin (for deep s1 mining)
            prec = ((canc as u32) + 760).max(prec + 256); // bump and redo
        }

        // THE BOUND
        let t32 = f!(prec, fsqrt(&f!(prec, tau.clone().pow(3u32)), prec)); // tau^{3/2}
        let t52 = f!(prec, &t32 * &tau);                                   // tau^{5/2}
        let sinw = fsin(&w, prec);
        let lead = f!(prec, f!(prec, 3.0 / sqrt2) * f!(prec, &t32 * &sinw));
        let boundc = f!(prec, fabs(&f!(prec, &y3q - &lead), prec) / &t52);
        let abs_sinw = fabs(&sinw, prec);

        // GATE (full mode only)
        let (t1_over_tau, gmarg_over_tau, r_over_t25);
        let r25_hp: String;
        let c2_acc: Float;
        if !bound_only {
            let q3 = f!(prec, q.clone().pow(3u32));
            let one_m_q3 = f!(prec, 1.0 - &q3);
            let p12 = f!(prec, f!(prec, 2.0 * &q3) / &one_m_q3 * &y3_1);
            let inv_q3 = f!(prec, 1.0 / &q3);
            let se = f!(prec, f!(prec, f!(prec, 3.0 * &y3_1) - &y3q) / f!(prec, 1.0 - &inv_q3));
            let t1 = f!(prec, &p12 / &se);
            let one_m_q_over_q = f!(prec, f!(prec, 1.0 - &q) / &q);
            let gmarg = f!(prec, &one_m_q_over_q - &t1);
            // residual R = P12 - E,  E = 0.5 (w-W)^2 sin w sin(w-W),  W=w e^{-tau/2}
            let cap_w = f!(prec, &w * fexp(&f!(prec, -&f!(prec, &tau / 2.0)), prec));
            let dwW = f!(prec, &w - &cap_w);
            let ee = f!(prec, f!(prec, f!(prec, 0.5 * f!(prec, &dwW * &dwW)) * &sinw) * fsin(&dwW, prec));
            let rr = f!(prec, &p12 - &ee);
            t1_over_tau = f!(prec, &t1 / &tau).to_f64();
            gmarg_over_tau = f!(prec, &gmarg / &tau).to_f64();
            r_over_t25 = f!(prec, &rr / &t52).to_f64();
            r25_hp = f!(prec, &rr / &t52).to_string_radix(10, Some(190));
            c2_acc = fabs(&f!(prec, f!(prec, &rr / &t52) / &abs_sinw), prec); // |R/(tau^{5/2} sin w)|
        } else {
            t1_over_tau = f64::NAN; gmarg_over_tau = f64::NAN; r_over_t25 = f64::NAN;
            r25_hp = "nan".to_string();
            c2_acc = f!(prec, 0.0);
        }

        done_this_run += 1;
        let elapsed = start.elapsed().as_secs_f64();
        let rate = done_this_run as f64 / elapsed;
        let remaining = (total_todo - done_this_run) as f64;
        let eta = if rate > 0.0 { remaining / rate } else { 0.0 };

        let tau_f = tau.to_f64();
        let boundc_f = boundc.to_f64();
        let sinw_f = abs_sinw.to_f64();
        println!("{:>6} {:>11.3e} {:>10.5} {:>12.5} {:>9.4} {:>9.4} {:>7.4} {:>6} {:>8}",
            m, tau_f, t1_over_tau, gmarg_over_tau, boundc_f, r_over_t25, sinw_f, prec, fmt_eta(eta));
        let _ = std::io::stdout().flush();

        // gate sanity alarm
        if !bound_only && gmarg_over_tau <= 0.0 {
            println!("  !!!! GATE VIOLATION at m={} (gatemargin<=0) — INVESTIGATE", m);
        }
        if boundc_f > 50.0 || boundc_f.is_nan() {
            println!("  !!!! boundC unexpectedly large/NaN at m={} — INVESTIGATE", m);
        }

        writeln!(fh, "{},{:.18e},{:.12},{:.12},{:.10},{:.10},{:.10},{},{},{},{}",
            m, tau_f, t1_over_tau, gmarg_over_tau, boundc_f, r_over_t25, sinw_f, prec,
            r25_hp, abs_sinw.to_string_radix(10, Some(190)), tau.to_string_radix(10, Some(190))).unwrap();
        fh.flush().unwrap();
        if !bound_only { accum.push((f!(5000, &tau), f!(5000, &c2_acc))); }
    }
    println!("# done. {} poles this run in {}.", done_this_run, fmt_eta(start.elapsed().as_secs_f64()));

    // === in-Rust Neville extraction:  c2 = R/(tau^{5/2} sin w) = C + s1 tau + s2 tau^2 + s3 tau^3 + ... ===
    if !bound_only && accum.len() >= 12 {
        let ep: u32 = 5000;
        accum.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap()); // ascending tau (deepest first)
        let cc = Float::with_val(ep, Float::with_val(ep, 1891.0 * fsqrt(&Float::with_val(ep, 2.0), ep)) / 10368.0);
        let nuse = accum.len().min(120);
        let mut svals: Vec<Float> = Vec::new();
        let path = format!("{}.scoeffs.txt", out);
        let mut sf = std::fs::File::create(&path).unwrap();
        writeln!(sf, "# c2 = R/(tau^5/2 sin w) = C + s1 tau + s2 tau^2 + ... ; Neville over {} deepest poles", nuse).unwrap();
        writeln!(sf, "C {}", cc.to_string_radix(10, Some(185))).unwrap();
        println!("# === COEFFICIENT EXTRACTION (in-Rust Neville, {} deepest poles) ===", nuse);
        println!("# C  = 1891*sqrt2/10368 = {}", cc.to_string_radix(10, Some(60)));
        for k in 1..=16usize {
            // points (tau, (c2 - C - sum_{j<k} s_j tau^j) / tau^k)
            let g: Vec<(Float, Float)> = accum.iter().map(|(t, c)| {
                let tt = Float::with_val(ep, t);
                let mut num = Float::with_val(ep, Float::with_val(ep, c) - &cc);
                let mut tp = tt.clone();
                for s in svals.iter() {
                    num = Float::with_val(ep, &num - Float::with_val(ep, s * &tp));
                    tp = Float::with_val(ep, &tp * &tt);
                }
                let denk = Float::with_val(ep, tt.clone().pow(k as u32));
                (tt, Float::with_val(ep, &num / &denk))
            }).collect();
            let s = neville_at_zero(&g[..nuse], ep);
            let sb = neville_at_zero(&g[..nuse - 2], ep);
            let sd = stable_digits(&s, &sb, ep).min(178);
            println!("# s{} = {}  (stable ~{} digits)", k, s.to_string_radix(10, Some(sd.max(15))), sd);
            writeln!(sf, "s{} {}", k, s.to_string_radix(10, Some(sd.max(15)))).unwrap();
            svals.push(s);
        }
        println!("# wrote {}  (feed to: python3 hunt_coeffs.py {})", path, path);
    }
    println!("# VERDICT KEY: boundC bounded (~3.71) across all m  <=>  THE BOUND holds numerically");
    println!("#             gatemargin/tau -> ~0.75 (>0)          <=>  the U-gate s<1 holds at every pole");
}
