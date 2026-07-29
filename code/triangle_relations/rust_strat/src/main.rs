// Exact BFS in a stratum triangle group: translation census by word length.
// Arithmetic in K = Q(2cos(pi/m))(sin(pi/m)) with exact BigRationals.
// Rule 8: per-depth progress, ETA, RSS guard, atomic checkpoint.
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::HashSet;
use std::str::FromStr;
use std::time::Instant;

type R = BigRational;
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Nf(Vec<R>);
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Kel { u: Nf, v: Nf }
type El = Vec<Kel>; // 6 entries: a b c d tx ty

struct F { deg: usize, mp: Vec<R>, s2: Nf }

impl F {
    fn nzero(&self) -> Nf { Nf(vec![R::zero(); self.deg]) }
    fn none_(&self) -> Nf {
        let mut v = vec![R::zero(); self.deg]; v[0] = R::one(); Nf(v)
    }
    fn nadd(&self, a: &Nf, b: &Nf) -> Nf { Nf((0..self.deg).map(|i| &a.0[i] + &b.0[i]).collect()) }
    fn nsub(&self, a: &Nf, b: &Nf) -> Nf { Nf((0..self.deg).map(|i| &a.0[i] - &b.0[i]).collect()) }
    fn nmul(&self, a: &Nf, b: &Nf) -> Nf {
        let d = self.deg;
        let mut f = vec![R::zero(); 2 * d];
        for i in 0..d {
            if a.0[i].is_zero() { continue; }
            for j in 0..d {
                if b.0[j].is_zero() { continue; }
                f[i + j] = &f[i + j] + &a.0[i] * &b.0[j];
            }
        }
        for k in (d..2 * d - 1).rev() {
            let co = f[k].clone();
            if !co.is_zero() {
                f[k] = R::zero();
                for i in 0..d { f[k - d + i] = &f[k - d + i] - &co * &self.mp[i]; }
            }
        }
        Nf(f[..d].to_vec())
    }
    fn kzero(&self) -> Kel { Kel { u: self.nzero(), v: self.nzero() } }
    fn kone(&self) -> Kel { Kel { u: self.none_(), v: self.nzero() } }
    fn kadd(&self, a: &Kel, b: &Kel) -> Kel {
        Kel { u: self.nadd(&a.u, &b.u), v: self.nadd(&a.v, &b.v) }
    }
    fn kmul(&self, a: &Kel, b: &Kel) -> Kel {
        let uu = self.nmul(&a.u, &b.u);
        let vv = self.nmul(&self.nmul(&a.v, &b.v), &self.s2);
        let uv = self.nmul(&a.u, &b.v);
        let vu = self.nmul(&a.v, &b.u);
        Kel { u: self.nadd(&uu, &vv), v: self.nadd(&uv, &vu) }
    }
    fn amul(&self, g: &El, h: &El) -> El {
        vec![
            self.kadd(&self.kmul(&g[0], &h[0]), &self.kmul(&g[1], &h[2])),
            self.kadd(&self.kmul(&g[0], &h[1]), &self.kmul(&g[1], &h[3])),
            self.kadd(&self.kmul(&g[2], &h[0]), &self.kmul(&g[3], &h[2])),
            self.kadd(&self.kmul(&g[2], &h[1]), &self.kmul(&g[3], &h[3])),
            self.kadd(&self.kadd(&self.kmul(&g[0], &h[4]), &self.kmul(&g[1], &h[5])), &g[4]),
            self.kadd(&self.kadd(&self.kmul(&g[2], &h[4]), &self.kmul(&g[3], &h[5])), &g[5]),
        ]
    }
}

fn parse_nf(s: &str, deg: usize) -> Nf {
    let v: Vec<R> = s.split_whitespace().map(|t| R::from_str(t).unwrap()).collect();
    assert_eq!(v.len(), deg);
    Nf(v)
}
fn rss_gb() -> f64 {
    std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.trim().parse::<f64>().ok())
        .map(|kb| kb / 1e6).unwrap_or(0.0)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let dmax: u32 = args[2].parse().unwrap();
    let txt = std::fs::read_to_string(path).unwrap();
    let mut lines = txt.lines();
    let hdr: Vec<usize> = lines.next().unwrap().split_whitespace()
        .map(|x| x.parse().unwrap()).collect();
    let (m, deg) = (hdr[0], hdr[1]);
    let mp = parse_nf(lines.next().unwrap(), deg).0;
    let s2 = parse_nf(lines.next().unwrap(), deg);
    let f = F { deg, mp, s2 };
    let mut gens: Vec<El> = Vec::new();
    for _ in 0..3 {
        let mut g: El = Vec::new();
        for _ in 0..6 {
            let l = lines.next().unwrap();
            let parts: Vec<&str> = l.split('|').collect();
            g.push(Kel { u: parse_nf(parts[0], deg), v: parse_nf(parts[1], deg) });
        }
        gens.push(g);
    }
    let idel: El = vec![f.kone(), f.kzero(), f.kzero(), f.kone(), f.kzero(), f.kzero()];
    for g in &gens {
        assert_eq!(f.amul(g, g), idel, "generator is not an involution");
    }
    let t0 = Instant::now();
    let mut seen: HashSet<El> = HashSet::new();
    seen.insert(idel.clone());
    let mut front: Vec<El> = vec![idel.clone()];
    let mut ck = String::new();
    println!("m={} deg={} dmax={}", m, deg, dmax);
    for d in 1..=dmax {
        let mut nf: Vec<El> = Vec::new();
        let mut ntr = 0u64;
        for x in &front {
            for g in &gens {
                let y = f.amul(x, g);
                if !seen.contains(&y) {
                    if y[0] == f.kone() && y[1] == f.kzero()
                       && y[2] == f.kzero() && y[3] == f.kone() { ntr += 1; }
                    seen.insert(y.clone());
                    nf.push(y);
                }
            }
        }
        front = nf;
        let el = t0.elapsed().as_secs_f64();
        let eta = el * (2f64.powi((dmax - d) as i32) - 1.0);
        let rs = rss_gb();
        println!("d={:2} layer={:8} translations={:6} elapsed={:7.1}s eta={:8.1}s rss={:.2}GB",
                 d, front.len(), ntr, el, eta, rs);
        ck.push_str(&format!("{{\"d\":{},\"layer\":{},\"tr\":{}}}\n", d, front.len(), ntr));
        std::fs::write("ck.tmp", &ck).ok();
        std::fs::rename("ck.tmp", format!("strat_m{}_checkpoint.jsonl", m)).ok();
        if rs > 6.0 { println!("ABORT: rss > 6 GB"); return; }
    }
    println!("done [{:.1}s]", t0.elapsed().as_secs_f64());
}
