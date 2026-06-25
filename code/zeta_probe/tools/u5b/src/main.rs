// U5b attack: pin the reflection correction (the subleading error beyond the dispersion defect)
// to high precision down to tiny tau, confirm its order is O(tau^{3/2}) (so the leading sqrt2/36 is clean),
// and extract its constant for closed-form identification.
//
// For each travel pole q_m (Sigma_1^T(q_m)=1):
//   deviation = (m+1/2)pi - w_m,   w_m = sqrt(2/tau),  tau = -ln q_m
//   defect    = sum_{n=1}^{n*} ( k_n - 2 sin(k_n/2) ),   k_n = arccos(b_n/2),  2 sin(k_n/2) = sqrt(2-b_n)
//   cube      = (1/24) sum_{n} k_n^3
//   b_n = (1 + q^3 - 2(1-q) q^{2n+2}) / q^{3/2},   n* where b_n >= 2
// Lemma lem:wkbphase says deviation = defect + (reflection), reflection = O(tau^{3/2}).
// We output rel = deviation/defect - 1 (should -> 0 like c_rel * tau) and rel/tau (-> c_rel, the target constant).
//
// Output file u5b_out.txt: "m  tau  deviation  defect  cube  dev_over_sqrt_tau  rel  rel_over_tau"
// Resumable (skips m already in the file), progress+ETA to stderr, scalar (no OOM).

use rug::float::Constant;
use rug::ops::Pow;
use rug::Float;
use std::collections::HashSet;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader, Write};
use std::time::Instant;

const PREC: u32 = 1536; // ~462 decimal digits (sig_t partial sums reach ~10^{250} at small tau; leave headroom)

macro_rules! fv {
    ($e:expr) => {
        Float::with_val(PREC, $e)
    };
}
fn nf(v: f64) -> Float {
    Float::with_val(PREC, v)
}
fn pi() -> Float {
    Float::with_val(PREC, Constant::Pi)
}

// Sigma_1^T(q): travel-block sum (pole at Sigma_1^T = 1)
fn sig_t(q: &Float) -> Float {
    let one = nf(1.0);
    let two = nf(2.0);
    let qsq = fv!(q * q);
    let tiny = nf(10.0).pow(-((PREC as i32) / 3) - 5);
    // pr LEGITIMATELY reaches ~10^{360} at small tau (the cocycle's catastrophic cancellation);
    // the true-divergence guard must sit above that yet below the precision ceiling ~10^{0.301*PREC}.
    let bigguard = nf(10.0).pow((PREC as f64 * 0.27) as i32);
    let mut s = nf(0.0);
    let mut pr = nf(1.0);
    let mut qk = q.clone(); // q^{kk}, kk = 1,3,5,...
    let mut iters: u64 = 0;
    loop {
        let qk1 = fv!(&qk * q); // q^{kk+1}
        let qk2 = fv!(&qk * &qsq); // q^{kk+2}
        let qk3 = fv!(&qk2 * q); // q^{kk+3}
        let denom1 = fv!(&one - &qk1);
        let denom2 = fv!(&one - &qk2);
        // term = 2 q / (1 - q^{kk+1}) * pr
        let twoq = fv!(&two * q);
        let term = fv!(fv!(&twoq / &denom1) * &pr);
        s += &term;
        // fac = 2 q^{kk+3}/(1-q^{kk+2}) - 2 q^{kk+2}/(1-q^{kk+1})
        let a = fv!(fv!(&two * &qk3) / &denom2);
        let b = fv!(fv!(&two * &qk2) / &denom1);
        let fac = fv!(&a - &b);
        pr = fv!(&pr * &fac);
        let prabs = pr.clone().abs();
        if prabs < tiny {
            break;
        }
        if prabs > bigguard {
            eprintln!("  [sig_t WARN: pr exceeded precision-relative guard at iter {} (tau too small for PREC)]", iters);
            break;
        }
        qk = fv!(&qk * &qsq); // kk += 2
        iters += 1;
        if iters > 5_000_000 {
            eprintln!("  [sig_t WARN: hit iter cap 5e6]");
            break;
        }
    }
    s
}

// Newton root-find: Sigma_1^T(q_m) = 1, starting from the asymptotic guess.
fn find_pole(m: u64) -> Float {
    let pi = pi();
    let wm0 = fv!(fv!(m as f64 + 0.5) * &pi);
    let tau0 = fv!(fv!(2.0) / fv!(&wm0 * &wm0));
    // Refine the guess with the KNOWN leading phase defect w_m = (m+1/2)pi - (sqrt2/36)sqrt(tau):
    // this makes q0 accurate to ~tau^3, far inside the ~tau^{3/2} pole spacing, so Newton
    // cannot jump to a neighbouring pole even at large m.
    let sqrt2_36 = fv!(fv!(nf(2.0).sqrt()) / 36.0);
    let w1 = fv!(&wm0 - fv!(&sqrt2_36 * fv!(tau0.clone().sqrt())));
    let tau1 = fv!(fv!(2.0) / fv!(&w1 * &w1));
    let mut q = fv!(fv!(-&tau1).exp());
    // Central-diff step h must sit ABOVE the cancellation-limited noise floor of sig_t
    // (sig_t loses ~250 digits to cancellation at small tau) and BELOW the truncation
    // ceiling (~1e-4). h=1e-40 is in this window for all m up to ~300 at PREC>=1536.
    let h = nf(10.0).pow(-40);
    let conv = nf(10.0).pow(-50);
    for _ in 0..25 {
        let g = fv!(&sig_t(&q) - 1.0);
        let gp = fv!(fv!(&sig_t(&fv!(&q + &h)) - &sig_t(&fv!(&q - &h))) / fv!(&h * 2.0));
        let mut dq = fv!(&g / &gp);
        // q0 is accurate to ~tau^3; cap steps well below the pole spacing (~tau^{3/2}) to
        // prevent jumping to a neighbouring pole if gp is momentarily noisy at large m.
        let maxstep = fv!(fv!(&nf(1.0) - &q) * 0.001);
        if dq.clone().abs() > maxstep {
            dq = fv!(&maxstep * dq.clone().signum());
        }
        q = fv!(&q - &dq);
        if q <= nf(0.0) {
            q = nf(1e-6);
        }
        if q >= nf(1.0) {
            q = nf(0.9999999);
        }
        if dq.clone().abs() < conv {
            break;
        }
    }
    q
}

// (defect, cube) = ( sum (k_n - 2 sin(k_n/2)), (1/24) sum k_n^3 )  over the oscillatory region n=1..n*
fn defect_sums(q: &Float) -> (Float, Float) {
    let one = nf(1.0);
    let two = nf(2.0);
    let qsq = fv!(q * q);
    let q3 = fv!(&qsq * q); // q^3
    let q32 = fv!(q3.clone().sqrt()); // q^{3/2}
    let omq = fv!(&one - q); // 1 - q
    let twoomq = fv!(&two * &omq); // 2(1-q)
    let mut defect = nf(0.0);
    let mut cube = nf(0.0);
    let mut q2n2 = fv!(&qsq * &qsq); // q^{2n+2} at n=1 -> q^4
    loop {
        // b_n = (1 + q^3 - 2(1-q) q^{2n+2}) / q^{3/2}
        let numer = fv!(fv!(&one + &q3) - fv!(&twoomq * &q2n2));
        let b = fv!(&numer / &q32);
        let twomb = fv!(&two - &b); // 2 - b_n
        if !(twomb > nf(0.0)) {
            break; // reached the turning point (b_n >= 2)
        }
        let bhalf = fv!(&b / &two);
        let k = bhalf.acos(); // arccos(b/2)
        let two_sin = fv!(twomb.sqrt()); // sqrt(2 - b) = 2 sin(k/2)
        defect += fv!(&k - &two_sin);
        let k2 = fv!(&k * &k);
        cube += fv!(&k2 * &k);
        q2n2 = fv!(&q2n2 * &qsq); // n -> n+1
    }
    cube = fv!(&cube / 24.0);
    (defect, cube)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let m_start: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2);
    let m_end: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(150);
    let path = "u5b_out.txt";

    // resume: collect m already computed
    let mut done: HashSet<u64> = HashSet::new();
    if let Ok(f) = std::fs::File::open(path) {
        for line in BufReader::new(f).lines().flatten() {
            if let Some(tok) = line.split_whitespace().next() {
                if let Ok(mm) = tok.parse::<u64>() {
                    done.insert(mm);
                }
            }
        }
    }
    let mut out = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .expect("open out");

    let pi = pi();
    let todo: Vec<u64> = (m_start..=m_end).filter(|m| !done.contains(m)).collect();
    let total = todo.len();
    eprintln!(
        "U5b: computing m={}..{} ({} poles to do, {} already done), prec={} bits",
        m_start, m_end, total, done.len(), PREC
    );
    let t0 = Instant::now();
    for (i, &m) in todo.iter().enumerate() {
        let q = find_pole(m);
        let tau = fv!(-q.clone().ln());
        let w = fv!(fv!(fv!(2.0) / &tau).sqrt());
        let dev = fv!(fv!(fv!(m as f64 + 0.5) * &pi) - &w);
        let (defect, cube) = defect_sums(&q);
        let sqrt_tau = fv!(tau.clone().sqrt());
        let dev_ost = fv!(&dev / &sqrt_tau); // -> sqrt2/36 = 0.0392837
        let rel = fv!(fv!(&dev / &defect) - 1.0); // -> 0 like c_rel*tau
        let rel_ot = fv!(&rel / &tau); // -> c_rel (the reflection constant target)
        // write with generous digits
        writeln!(
            out,
            "{}  {}  {}  {}  {}  {}  {}  {}",
            m,
            tau.to_string_radix(10, Some(40)),
            dev.to_string_radix(10, Some(40)),
            defect.to_string_radix(10, Some(40)),
            cube.to_string_radix(10, Some(40)),
            dev_ost.to_string_radix(10, Some(30)),
            rel.to_string_radix(10, Some(30)),
            rel_ot.to_string_radix(10, Some(30))
        )
        .unwrap();
        out.flush().unwrap();
        let el = t0.elapsed().as_secs_f64();
        let eta = if i + 1 > 0 {
            el / (i + 1) as f64 * (total - i - 1) as f64
        } else {
            0.0
        };
        eprintln!(
            "  m={:>4}  tau={:.3e}  dev/sqrt(tau)={:.7}  rel/tau={:.6}   [{}/{}  {:.0}s elapsed, ETA {:.0}s]",
            m,
            tau.to_f64(),
            dev_ost.to_f64(),
            rel_ot.to_f64(),
            i + 1,
            total,
            el,
            eta
        );
    }
    eprintln!("done in {:.0}s. results in {}", t0.elapsed().as_secs_f64(), path);
}
