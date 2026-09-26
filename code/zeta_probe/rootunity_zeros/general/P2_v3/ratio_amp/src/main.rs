use rug::{Complex, Float};
use rug::float::Constant;
use std::env;

const PREC: u32 = 200; // bits, ~60 decimal digits

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn c_pow_u(base: &Complex, mut e: u64) -> Complex {
    let mut result = Complex::with_val(PREC, (1, 0));
    let mut b = base.clone();
    while e > 0 {
        if e & 1 == 1 {
            result = Complex::with_val(PREC, result * &b);
        }
        b = Complex::with_val(PREC, b.clone() * &b);
        e >>= 1;
    }
    result
}

// z = exp(2 pi i a / N), returns z^m via angle reduction (m can be large, use i128)
fn z_pow(a: i64, n: i64, m: i64) -> Complex {
    let pi = Float::with_val(PREC, Constant::Pi);
    // angle = 2*pi*a*m/n, reduce m mod n first (m may be huge but fits i128 for our ranges)
    let mm = ((m as i128) % (n as i128) + (n as i128)) % (n as i128);
    let theta = (Float::with_val(PREC, 2) * &pi * Float::with_val(PREC, a) * Float::with_val(PREC, mm as i64)) / Float::with_val(PREC, n);
    let re = theta.clone().cos();
    let im = theta.sin();
    Complex::with_val(PREC, (re, im))
}

fn heads(a: i64, n: i64) -> (Complex, Complex) {
    let z = z_pow(a, n, 1);
    let one = Complex::with_val(PREC, (1, 0));
    let two = Complex::with_val(PREC, (2, 0));
    let one_minus_z: Complex = Complex::with_val(PREC, &one - &z);
    let neg_two: Complex = Complex::with_val(PREC, -&two);
    let c: Complex = Complex::with_val(PREC, &neg_two * &one_minus_z);

    let r_max = (n - 1) / 2; // He: r = 0..=r_max, index j = 2r
    let k0 = (n + 1) / 2; // Ho: k = k0..=n-1, index j = 2k-n

    let mut he = Complex::with_val(PREC, (0, 0));
    let mut ho = Complex::with_val(PREC, (0, 0));

    // running poch value: poch[j] = prod_{i=1}^{j} (1 - z^i), poch[0] = 1
    let mut poch = Complex::with_val(PREC, (1, 0));
    let mut zj = Complex::with_val(PREC, (1, 0)); // z^j

    // incremental state for He (r-index)
    let mut c_pow_r = Complex::with_val(PREC, (1, 0)); // c^r
    let mut z_rsq = Complex::with_val(PREC, (1, 0)); // z^{r^2}
    let mut r_cur: i64 = 0;

    // incremental state for Ho (k-index), initialized lazily when j reaches first odd index
    let mut c_pow_k = c_pow_u(&c, k0 as u64);
    let mut z_ksq = z_pow(a, n, (k0 as i128 * k0 as i128).rem_euclid(n as i128) as i64);
    let mut k_cur: i64 = k0;
    let mut ho_started = false;

    for j in 0..n {
        if j == 0 {
            // poch stays 1
        } else {
            zj = Complex::with_val(PREC, zj * &z);
            let one_minus_zj: Complex = Complex::with_val(PREC, &one - &zj);
            poch = Complex::with_val(PREC, &poch * &one_minus_zj);
        }
        if j % 2 == 0 {
            let r = j / 2;
            if r <= r_max {
                debug_assert_eq!(r, r_cur);
                let num: Complex = Complex::with_val(PREC, &c_pow_r * &z_rsq);
                let term: Complex = Complex::with_val(PREC, num / &poch);
                he += term;
                // advance r
                r_cur += 1;
                c_pow_r = Complex::with_val(PREC, c_pow_r * &c);
                let delta = z_pow(a, n, 2 * r + 1);
                z_rsq = Complex::with_val(PREC, z_rsq * delta);
            }
        } else {
            let k = (j + n) / 2;
            if k >= k0 && k <= n - 1 {
                debug_assert_eq!(k, k_cur);
                ho_started = true;
                let num: Complex = Complex::with_val(PREC, &c_pow_k * &z_ksq);
                let term: Complex = Complex::with_val(PREC, num / &poch);
                ho += term;
                k_cur += 1;
                c_pow_k = Complex::with_val(PREC, c_pow_k * &c);
                let delta = z_pow(a, n, 2 * k + 1);
                z_ksq = Complex::with_val(PREC, z_ksq * delta);
            }
        }
    }
    let _ = ho_started;

    // s = sqrt(c^n); c^n via z_pow-free method: use c_pow_u
    let cn = c_pow_u(&c, n as u64);
    let s = cn.sqrt();
    let ho_final: Complex = Complex::with_val(PREC, ho / s);
    (he, ho_final)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: ratio_amp <q> <mode:round|floor> <N1> [N2 N3 ...]");
        std::process::exit(1);
    }
    let q: i64 = args[1].parse().unwrap();
    let mode = args[2].as_str();
    for ns in &args[3..] {
        let n: i64 = ns.parse().unwrap();
        let mut nn = n;
        if nn % 2 == 0 { nn += 1; }
        let a: i64 = match mode {
            "round" => ((nn as f64) / (q as f64)).round() as i64,
            "floor" => ((nn as f64) / (q as f64)).floor() as i64,
            _ => panic!("bad mode"),
        };
        let a = if a == 0 { 1 } else { a };
        if gcd(a as u64, nn as u64) != 1 {
            println!("N={} a={} SKIP(gcd!=1)", nn, a);
            continue;
        }
        let (he, ho) = heads(a, nn);
        let two = Complex::with_val(PREC, (2, 0));
        let sum: Complex = Complex::with_val(PREC, &he + &ho);
        let diff: Complex = Complex::with_val(PREC, &he - &ho);
        let ap: Complex = Complex::with_val(PREC, sum / &two);
        let am: Complex = Complex::with_val(PREC, diff / &two);
        let ratio: Complex = Complex::with_val(PREC, &ap / &am);
        let amod = ratio.clone().abs();
        let aarg = ratio.clone().arg();
        println!(
            "q={} mode={} N={} a={} a/N={:.10} |A+/A-|={} arg={} re={} im={}",
            q, mode, nn, a, (a as f64) / (nn as f64),
            amod.real().to_f64(),
            aarg.real().to_f64(),
            ratio.real().to_f64(),
            ratio.imag().to_f64()
        );
    }
}
