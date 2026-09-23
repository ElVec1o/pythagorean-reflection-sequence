// Room 40b: (1) interval certification of the uniform Z>0 bound on eps in (0, E0];
//           (2) direct interval certification at the poles q_m of Z>0, D!=0, 1-g t1>0, S!=0.
// Interval core (I, guard) copied verbatim from r39pole/src/main.rs (lines 1-77).
include!("iv.rs");

fn half() -> I { I::n(1).div(&I::n(2)) }

/// Generic q-series  sum_{k>=0} C^k q^{k^2+a k} / prod_{j=1}^{2k} (1 - q^{j+b}),  C = -2*lam*eps.
/// Ratio t_{k+1}/t_k = C q^{2k+1+a} / ((1-q^{2k+1+b})(1-q^{2k+2+b})); |ratio| is decreasing in k
/// for q in (0,1) (numerator decreasing, both denominator factors increasing), so once
/// r_K := sup|ratio(K->K+1)| < 1/2 the tail sum_{k>K}|t_k| <= |t_K| r_K/(1-r_K) <= 2|t_K| r_K.
fn qser(lam: &I, q: &I, a: u64, b: u64) -> I {
    let one = I::n(1);
    let eps = one.sub(q);
    let c = I::n(-2).mul(lam).mul(&eps);
    let mut t = one.clone();
    let mut sum = one.clone();
    let mut k: u64 = 0;
    let tiny = Float::with_val(pr(), Float::i_exp(1, -(pr() as i32) + 40));
    loop {
        let e1 = q.pow(2 * k + 1 + a);
        let d1 = one.sub(&q.pow(2 * k + 1 + b));
        let d2 = one.sub(&q.pow(2 * k + 2 + b));
        let ratio = c.mul(&e1).div(&d1.mul(&d2));
        let rmag = ratio.mag();
        if k > 3 && rmag.hi < 0.5 {
            let tb = t.mag().mul(&rmag).div(&one.sub(&rmag));
            if tb.hi < tiny { return sum.widen(&tb); }
        }
        t = t.mul(&ratio);
        sum = sum.add(&t);
        k += 1;
        if k % 64 == 0 { guard("qser"); }
        if k > 200000 { panic!("qser no convergence"); }
    }
}
fn bfun(q: &I) -> I { qser(&I::n(1), q, 0, 0) }            // B = F(1,q)
fn sfun(q: &I) -> I { qser(q, q, 0, 0) }                   // S = F(q,q)
fn gfun(q: &I) -> I { qser(&I::n(1), q, 2, 1) }            // G, A = 1/G

// ---------------- Part 1: uniform bounds ----------------
// returns (ASlow, Yup, Zlow) as intervals whose .lo/.hi are the certified bounds on the eps-cell
fn uniform_orig(e: &I) -> (I, I, I) {
    let one = I::n(1); let two = I::n(2);
    let q = one.sub(e);
    let o = two.mul(e).sqrt(); let oq = two.mul(&q).mul(e).sqrt();
    let b = o.div(&two.sub(&o)); let bq = oq.div(&two.sub(&oq));
    let u2 = b.exp().div(&one.sub(&o.mul(&half()))); let u = u2.sqrt();
    let ds = bq.mul(&half()).exp().mul(&one.add(&oq.mul(&half())).sqrt())
        .mul(&two.mul(e).div(&q).sqrt()).mul(&u).div(&one.sub(&oq.mul(&half())).sqrt());
    let as_ = q.mul(&one.sub(&b).sub(&o.mul(&u2).div(&one.add(&q))).sub(&two.mul(&ds).mul(&u)));
    let y = q.mul(&q).mul(&b.exp().sub(&one).add(&ds));
    let z = as_.sub(&y.div(&one.sub(&q.mul(e))));
    (as_, y, z)
}
// sharpened constants (see report): U_x^2 = e^b/(1-O^2/4); D' = sqrt(2e) U_x e^{b/2}/sqrt(1-O^2/4);
// AS >= q[(1-b) - O e^b/((1+q)(2-O)) - 2 U_x D'];  Y <= q^2 (e^b - 1 + D')
fn uniform_sharp(e: &I) -> (I, I, I) {
    let one = I::n(1); let two = I::n(2);
    let q = one.sub(e);
    let o = two.mul(e).sqrt();
    let b = o.div(&two.sub(&o));
    let w = one.sub(&o.mul(&o).div(&I::n(4)));
    let ux = b.exp().div(&w).sqrt();
    let dp = two.mul(e).sqrt().mul(&ux).mul(&b.mul(&half()).exp()).div(&w.sqrt());
    let as_ = q.mul(&one.sub(&b).sub(&o.mul(&b.exp()).div(&one.add(&q).mul(&two.sub(&o)))).sub(&two.mul(&ux).mul(&dp)));
    let y = q.mul(&q).mul(&b.exp().sub(&one).add(&dp));
    let z = as_.sub(&y.div(&one.sub(&q.mul(e))));
    (as_, y, z)
}
fn part1(e0: &str, ncell: i64, which: &str) {
    let e0i = I::s(e0);
    let mut worst_z = f64::INFINITY; let mut worst_as = f64::INFINITY; let mut ok = true;
    for i in 0..ncell {
        let lo = e0i.mul(&I::n(i)).div(&I::n(ncell)); let hi = e0i.mul(&I::n(i + 1)).div(&I::n(ncell));
        let cell = I { lo: lo.lo.clone(), hi: hi.hi.clone() };
        let (a, _y, z) = if which == "orig" { uniform_orig(&cell) } else { uniform_sharp(&cell) };
        if !(a.lo > 0 && z.lo > 0) { ok = false; }
        worst_z = worst_z.min(z.lo.to_f64()); worst_as = worst_as.min(a.lo.to_f64());
    }
    println!("UNIFORM[{}] eps in (0,{}] cells={} : AS>0 & Zlow>0 on all cells = {}  min ASlow={:.6} min Zlow={:.6}", which, e0, ncell, ok, worst_as, worst_z);
}

// ---------------- Part 2: poles ----------------
fn bsign_at(p: &Float) -> i32 { bfun(&I::pt(p)).sign() }
fn pole(m: usize, a: &str, b: &str) {
    guard("pole");
    // shrink the certified count-cell inward by 1e-15 relative so our cell lies inside it
    let fa = Float::with_val(pr(), Float::parse(a).unwrap());
    let fb = Float::with_val(pr(), Float::parse(b).unwrap());
    let w = Float::with_val(pr(), &fb - &fa);
    let mut lo = Float::with_val(pr(), &fa + Float::with_val(pr(), &w * 1e-9f64));
    let mut hi = Float::with_val(pr(), &fb - Float::with_val(pr(), &w * 1e-9f64));
    let sl = bsign_at(&lo); let sh = bsign_at(&hi);
    assert!(sl != 0 && sh != 0 && sl != sh, "m={} no certified sign change on shrunk cell", m);
    let target = Float::with_val(pr(), Float::i_exp(1, -(pr() as i32) + 60));
    let mut it = 0;
    while Float::with_val(pr(), &hi - &lo) > target && it < 400 {
        let mid = Float::with_val(pr(), &lo + &hi) / 2u32;
        let mid = Float::with_val(pr(), mid);
        let s = bsign_at(&mid);
        if s == 0 { break; }
        if s == sl { lo = mid; } else { hi = mid; }
        it += 1;
    }
    let q = I { lo: lo.clone(), hi: hi.clone() };
    let one = I::n(1); let two = I::n(2);
    let eps = one.sub(&q);
    let g0 = gfun(&q); let aa = one.div(&g0); let s = sfun(&q);
    let as_ = aa.mul(&s);
    let y = eps.mul(&aa).mul(&aa).div(&two).sub(&q.mul(&q).mul(&one.sub(&s)));
    let t1 = eps.mul(&aa).div(&two.mul(&q).mul(&s)).sub(&one);
    let psi = aa.div(&two.mul(&q)).sub(&s);
    let (_, _, zu) = uniform_sharp(&eps);
    print!("m={:2} q in [{:.17}, +{:.1e}] eps={:.5e} A={:.6} S={:.6e} (S!=0: {}) AS=[{:.6},{:.6}] Y=[{:.5},{:.5}] unifZlow={:.4}",
        m, q.lo.to_f64(), q.wid(), eps.f(), aa.f(), s.f(), s.sign() != 0, as_.lo.to_f64(), as_.hi.to_f64(), y.lo.to_f64(), y.hi.to_f64(), zu.lo.to_f64());
    for (yn, yv) in [("1", one.clone()), ("q", q.clone())] {
        let g = q.div(&one.sub(&q.mul(&yv)));
        let kap = eps.mul(&g).div(&one.add(&g.mul(&q)));
        let z = aa.mul(&one.add(&kap)).mul(&s).sub(&kap.mul(&aa).mul(&aa).div(&two.mul(&q)))
            .add(&q.mul(&kap).div(&eps).mul(&one.sub(&s)));
        let d = s.sub(&kap.mul(&psi));
        let omg = one.sub(&g.mul(&t1));
        print!(" | y={}: Z=[{:.6},{:.6}] 1-gt1=[{:.6},{:.6}] D=[{:.4e},{:.4e}] sgnD={}", yn, z.lo.to_f64(), z.hi.to_f64(), omg.lo.to_f64(), omg.hi.to_f64(), d.lo.to_f64(), d.hi.to_f64(), d.sign());
        assert!(z.lo > 0 && omg.lo > 0 && d.sign() != 0, "m={} y={} FAILED", m, yn);
    }
    println!(" | wid(Z,1)~{:.1e} it={}", as_.wid(), it);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    PREC.store(args[2].parse().unwrap(), Ordering::Relaxed);
    let t0 = std::time::Instant::now();
    match args[1].as_str() {
        "uniform" => { part1(&args[3], args[4].parse().unwrap(), &args[5]); }
        "poles" => {
            // certified count cells from report_r39_polecount / run1.log, run2.log, room-39 run for [0.1,0.5]
            let cells = [
                (1, "0.44375", "0.45937499999999997"),
                (2, "0.912109375", "0.9140625"),
                (3, "0.9677734375", "0.96875"),
                (4, "0.98339843750", "0.98388671875"),
                (5, "0.98988281249999998668", "0.99012695312499998668"),
                (6, "0.99330078124999998668", "0.99342285156249998668"),
                (7, "0.99513183593749998668", "0.99525390624999998668"),
                (8, "0.99635253906249998668", "0.99641357421874998668"),
                (9, "0.99714599609374998668", "0.99720703124999998668"),
                (10, "0.99775634765624998668", "0.99781738281249998668"),
                (11, "0.99815307617187498668", "0.99818359374999998668"),
                (12, "0.99845825195312498668", "0.99848876953124998668"),
                (13, "0.99870239257812498668", "0.99873291015624998668"),
            ];
            let lo: usize = args[3].parse().unwrap(); let hi: usize = args[4].parse().unwrap();
            for (m, a, b) in cells.iter() { if *m >= lo && *m <= hi { pole(*m, a, b); } }
        }
        _ => panic!("mode"),
    }
    println!("time={:.1}s maxrss={:.2e} bytes", t0.elapsed().as_secs_f64(), rss_bytes());
}
