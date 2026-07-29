// Deep BFS of the fully generic triangle reflection group over exact Q.
// Outputs: layer sizes, translation census, and the cost table c(n,m) for
// |n|,|m| <= 5, to test the shield-law automaton predictions (cost 14/16).
// Observability: per-depth progress + ETA + RSS guard + atomic checkpoint file.
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::HashMap;
use std::io::Write;
use std::time::Instant;

type R = BigRational;
type El = [R; 6]; // a b c d tx ty

fn amul(g: &El, h: &El) -> El {
    [
        &g[0] * &h[0] + &g[1] * &h[2],
        &g[0] * &h[1] + &g[1] * &h[3],
        &g[2] * &h[0] + &g[3] * &h[2],
        &g[2] * &h[1] + &g[3] * &h[3],
        &g[0] * &h[4] + &g[1] * &h[5] + &g[4],
        &g[2] * &h[4] + &g[3] * &h[5] + &g[5],
    ]
}
fn ainv(g: &El) -> El {
    let det = &g[0] * &g[3] - &g[1] * &g[2];
    let ai = &g[3] / &det;
    let bi = -&g[1] / &det;
    let ci = -&g[2] / &det;
    let di = &g[0] / &det;
    let tx = -(&ai * &g[4] + &bi * &g[5]);
    let ty = -(&ci * &g[4] + &di * &g[5]);
    [ai, bi, ci, di, tx, ty]
}
fn key(g: &El) -> Vec<u8> {
    let mut v = Vec::with_capacity(256);
    for x in g {
        let (n, d) = (x.numer(), x.denom());
        let nb = n.to_signed_bytes_le();
        let db = d.to_signed_bytes_le();
        v.extend_from_slice(&(nb.len() as u32).to_le_bytes());
        v.extend_from_slice(&nb);
        v.extend_from_slice(&(db.len() as u32).to_le_bytes());
        v.extend_from_slice(&db);
    }
    v
}
fn rq(n: i64, d: i64) -> R {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}
fn is_translation(g: &El) -> bool {
    g[0].is_one() && g[1].is_zero() && g[2].is_zero() && g[3].is_one()
}
fn rss_gb() -> f64 {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .ok();
    out.and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.trim().parse::<f64>().ok())
        .map(|kb| kb / 1e6)
        .unwrap_or(0.0)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dmax: u32 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(16);
    // apex from argv: pn pd qn qd (default 1/3, 1/2); dumps tagged when non-default
    let geti = |k: usize, d: i64| args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d);
    let (pn, pd, qn, qd) = (geti(2, 1), geti(3, 3), geti(4, 1), geti(5, 2));
    let tag = if (pn, pd, qn, qd) == (1, 3, 1, 2) {
        String::new()
    } else {
        format!("w{}_{}_{}_{}_", pn, pd, qn, qd)
    };
    // triangle (0,0),(1,0),(pn/pd,qn/qd)
    let refl = |p0: (R, R), p1: (R, R)| -> El {
        let dx = &p1.0 - &p0.0;
        let dy = &p1.1 - &p0.1;
        let l = &dx * &dx + &dy * &dy;
        let a = (&dx * &dx - &dy * &dy) / &l;
        let b = rq(2, 1) * &dx * &dy / &l;
        let d = -a.clone();
        let tx = (rq(1, 1) - &a) * &p0.0 - &b * &p0.1;
        let ty = -&b * &p0.0 + (rq(1, 1) - &d) * &p0.1;
        [a, b.clone(), b, d, tx, ty]
    };
    let v0 = (rq(0, 1), rq(0, 1));
    let v1 = (rq(1, 1), rq(0, 1));
    let v2 = (rq(pn, pd), rq(qn, qd));
    let gens = [
        refl(v0.clone(), v1.clone()),
        refl(v1.clone(), v2.clone()),
        refl(v2.clone(), v0.clone()),
    ];
    let idel: El = [rq(1, 1), rq(0, 1), rq(0, 1), rq(1, 1), rq(0, 1), rq(0, 1)];

    let t0 = Instant::now();
    let mut depth: HashMap<Vec<u8>, (u32, usize)> = HashMap::new(); // key -> (depth, store idx)
    let mut store: Vec<El> = vec![idel.clone()];
    depth.insert(key(&idel), (0, 0));
    let mut front: Vec<usize> = vec![0];
    let mut ckpt = String::new();
    for d in 1..=dmax {
        let mut new_front = Vec::new();
        let mut ntr = 0u64;
        for &i in &front {
            let m = store[i].clone();
            for g in &gens {
                let n = amul(g, &m);
                let k = key(&n);
                if !depth.contains_key(&k) {
                    if is_translation(&n) {
                        ntr += 1;
                    }
                    store.push(n);
                    depth.insert(k, (d, store.len() - 1));
                    new_front.push(store.len() - 1);
                }
            }
        }
        if ntr > 0 {
            let mut out = String::new();
            for &i in &new_front {
                let g = &store[i];
                if is_translation(g) {
                    out.push_str(&format!("{} {} {} {}\n",
                        g[4].numer(), g[4].denom(), g[5].numer(), g[5].denom()));
                }
            }
            std::fs::write(format!("translations_{}d{}.txt", tag, d), out).ok();
        }
        front = new_front;
        let el = t0.elapsed().as_secs_f64();
        let eta = el * (2f64.powi((dmax - d) as i32) - 1.0);
        let rss = rss_gb();
        println!(
            "d={:2} layer={:7} translations={:4} elapsed={:6.1}s eta={:6.1}s rss={:.2}GB",
            d, front.len(), ntr, el, eta, rss
        );
        ckpt.push_str(&format!("{{\"d\":{},\"layer\":{},\"tr\":{}}}\n", d, front.len(), ntr));
        std::fs::write("ckpt.tmp", &ckpt).ok();
        std::fs::rename("ckpt.tmp", "layers_checkpoint.jsonl").ok();
        if rss > 6.0 {
            println!("ABORT: rss > 6 GB");
            return;
        }
    }
    // cost table: t1 = (g0 g1 g2)^2, conjugators (g0g1)^n (g0g2)^m
    let g012 = amul(&gens[0], &amul(&gens[1], &gens[2]));
    let t1 = amul(&g012, &g012);
    let a01 = amul(&gens[0], &gens[1]);
    let a02 = amul(&gens[0], &gens[2]);
    let powm = |mat: &El, k: i32| -> El {
        let mut p = idel.clone();
        let base = if k >= 0 { mat.clone() } else { ainv(mat) };
        for _ in 0..k.abs() {
            p = amul(&base, &p);
        }
        p
    };
    let mut out = String::from("{\"cost\":{");
    let mut first = true;
    println!("cost table c(n,m), |n|,|m| <= 5   (>{} = outside ball)", dmax);
    for n in -5i32..=5 {
        let mut row = String::new();
        for m in -5i32..=5 {
            let c = amul(&powm(&a01, n), &powm(&a02, m));
            let t = amul(&c, &amul(&t1, &ainv(&c)));
            let dep = depth.get(&key(&t)).map(|x| x.0 as i64).unwrap_or(-1);
            row.push_str(&format!("{:>5}", if dep < 0 { "-".to_string() } else { dep.to_string() }));
            if !first {
                out.push(',');
            }
            first = false;
            out.push_str(&format!("\"{},{}\":{}", n, m, dep));
        }
        println!("n={:2} |{}", n, row);
    }
    out.push_str("}}");
    let mut f = std::fs::File::create("cost_table.json").unwrap();
    f.write_all(out.as_bytes()).unwrap();
    println!("done [{:.1}s] -> cost_table.json", t0.elapsed().as_secs_f64());
}
