// ortho_cd -- orbit growth of the right-corner orthoscheme reflection group, against the
// right-angled Coxeter envelope.  Certificate for the layer counts, the collision depths and
// the Diophantine searches of paper/journal/paper_orthoscheme.tex.
//
// GEOMETRY.  Orthoscheme O(a_1..a_n): V_0 = 0, V_k = V_{k-1} + a_k e_k.  The facet opposite V_j
// carries the reflection R_j:
//   R_0: hyperplane {x_1 = a_1},          normal e_1        (it contains V_1..V_n)
//   R_j: hyperplane through 0, normal  a_{j+1} e_j - a_j e_{j+1}   (1 <= j <= n-1)
//   R_n: hyperplane {x_n = 0},            normal e_n
// All rational, so arithmetic in F_p is exact for the tuples run here; two primes are used and
// the two runs must agree.  Reduction mod p can only identify group elements that are already
// equal in characteristic zero or that collide mod p, so a printed layer count is a LOWER bound
// for the characteristic-zero count; agreement at two independent 61-bit primes is the check.
//
// u_d is the number of chambers g.O at word distance d.  O is a fundamental domain, so this is
// the sphere size of the image group rho_n(W_n); the image group is enumerated directly.
//
// ENVELOPE.  W_n(t) = (1+t)^{n+1} / J_{n+1}(t) with J_m = (1+t)(J_{m-1} - t J_{m-2}),
// J_0 = J_1 = 1 (the right-angled Coxeter group on the complement of the path P_{n+1}).
//
// USAGE
//   ortho_cd [--atlas FILE] [--quartics BOUND] [--max-ball N] [--no-quartics] [--quiet]
//   ortho_cd --row "label | legs | depth [| expected layers [| expected cd]]"
// Defaults: --atlas atlas.txt (relative to the tool directory), --quartics 300,
//           --max-ball 3000000.
// Exit status 0 iff every row that carries an expectation matched it at both primes, and every
// quartic/conic expectation held.  Rule 8: run under ../runcap.sh.

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::exit;

// ---------------------------------------------------------------- F_p

static mut P: u64 = 0;
#[inline]
fn p() -> u64 {
    unsafe { P }
}
#[inline]
fn add(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= p() { s - p() } else { s }
}
#[inline]
fn sub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a + p() - b }
}
#[inline]
fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % p() as u128) as u64
}
fn powm(a: u64, mut e: u64) -> u64 {
    let (mut r, mut b) = (1u64, a);
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, b);
        }
        b = mul(b, b);
        e >>= 1;
    }
    r
}
fn inv(a: u64) -> u64 {
    assert!(a != 0);
    powm(a, p() - 2)
}
fn fp(x: i64) -> u64 {
    let m = p() as i64;
    (((x % m) + m) % m) as u64
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for q in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % q == 0 { return n == q; }
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 { d /= 2; s += 1; }
    'o: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = { let (mut r, mut b, mut e) = (1u128, a as u128 % n as u128, d);
            while e > 0 { if e & 1 == 1 { r = r * b % n as u128; } b = b * b % n as u128; e >>= 1; }
            r as u64 };
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s - 1 {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n - 1 { continue 'o; }
        }
        return false;
    }
    true
}

// ---------------------------------------------------------------- affine maps in dim n

/// x |-> M x + t, stored row-major, dimension n.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Aff {
    n: usize,
    m: Vec<u64>,
    t: Vec<u64>,
}

fn ident(n: usize) -> Aff {
    let mut m = vec![0u64; n * n];
    for i in 0..n { m[i * n + i] = 1; }
    Aff { n, m, t: vec![0u64; n] }
}

/// f1 after f2
fn compose(f1: &Aff, f2: &Aff) -> Aff {
    let n = f1.n;
    let mut m = vec![0u64; n * n];
    for i in 0..n {
        for k in 0..n {
            let a = f1.m[i * n + k];
            if a == 0 { continue; }
            for j in 0..n {
                m[i * n + j] = add(m[i * n + j], mul(a, f2.m[k * n + j]));
            }
        }
    }
    let mut t = f1.t.clone();
    for i in 0..n {
        for k in 0..n {
            t[i] = add(t[i], mul(f1.m[i * n + k], f2.t[k]));
        }
    }
    Aff { n, m, t }
}

/// Reflection in {x : (x - pt).v = 0}, v not necessarily unit.
fn reflection(n: usize, pt: &[u64], v: &[u64]) -> Aff {
    let mut vv = 0u64;
    for i in 0..n { vv = add(vv, mul(v[i], v[i])); }
    assert!(vv != 0, "normal has zero length in F_p");
    let c = mul(2, inv(vv));
    let mut m = vec![0u64; n * n];
    for i in 0..n {
        for j in 0..n {
            let d = if i == j { 1u64 } else { 0u64 };
            m[i * n + j] = sub(d, mul(c, mul(v[i], v[j])));
        }
    }
    let mut pv = 0u64;
    for i in 0..n { pv = add(pv, mul(pt[i], v[i])); }
    let k = mul(c, pv);
    let t: Vec<u64> = (0..n).map(|i| mul(k, v[i])).collect();
    Aff { n, m, t }
}

/// The n+1 face reflections of the orthoscheme with legs a_1..a_n (given as rationals p/q).
fn ortho_gens(legs: &[(i64, i64)]) -> Vec<Aff> {
    let n = legs.len();
    let a: Vec<u64> = legs.iter().map(|&(x, y)| mul(fp(x), inv(fp(y)))).collect();
    let mut gens = Vec::new();
    // R_0: {x_1 = a_1}, normal e_1
    let mut pt = vec![0u64; n];
    pt[0] = a[0];
    let mut v = vec![0u64; n];
    v[0] = 1;
    gens.push(reflection(n, &pt, &v));
    // R_j, 1 <= j <= n-1: through 0, normal a_{j+1} e_j - a_j e_{j+1}   (1-indexed legs)
    for j in 1..n {
        let mut v = vec![0u64; n];
        v[j - 1] = a[j]; // a_{j+1} in 1-indexed = a[j] in 0-indexed
        v[j] = sub(0, a[j - 1]);
        gens.push(reflection(n, &vec![0u64; n], &v));
    }
    // R_n: {x_n = 0}, normal e_n
    let mut v = vec![0u64; n];
    v[n - 1] = 1;
    gens.push(reflection(n, &vec![0u64; n], &v));
    assert_eq!(gens.len(), n + 1);
    gens
}

/// Breadth-first search of the image group.  Returns the sphere sizes u_0..u_depth, or the
/// partial list and the depth actually reached when the ball cap is hit first.
fn spheres(gens: &[Aff], n: usize, depth: usize, max_ball: usize) -> (Vec<usize>, bool) {
    let id = ident(n);
    let mut seen: HashSet<Aff> = HashSet::new();
    seen.insert(id.clone());
    let mut frontier = vec![id];
    let mut out = vec![1usize];
    for _ in 1..=depth {
        let mut next = Vec::new();
        for f in &frontier {
            for g in gens {
                let h = compose(f, g);
                if seen.insert(h.clone()) {
                    next.push(h);
                    if seen.len() > max_ball { return (out, true); }
                }
            }
        }
        out.push(next.len());
        frontier = next;
    }
    (out, false)
}

// ---------------------------------------------------------------- the RACG envelope

type Poly = Vec<i128>;
fn pmul(a: &Poly, b: &Poly) -> Poly {
    let mut c = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() { c[i + j] += x * y; }
    }
    c
}
fn psub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    (0..n).map(|i| a.get(i).copied().unwrap_or(0) - b.get(i).copied().unwrap_or(0)).collect()
}
/// coefficients of (1+t)^{n+1} / J_{n+1}(t)
fn envelope(n: usize, upto: usize) -> Vec<i128> {
    let one_pt: Poly = vec![1, 1];
    let t: Poly = vec![0, 1];
    let (mut a, mut b): (Poly, Poly) = (vec![1], vec![1]);
    for _ in 2..=(n + 1) {
        let nxt = pmul(&one_pt, &psub(&b, &pmul(&t, &a)));
        a = b;
        b = nxt;
    }
    let j = b;
    let mut num: Poly = vec![1];
    for _ in 0..(n + 1) { num = pmul(&num, &one_pt); }
    let mut out = vec![0i128; upto + 1];
    for i in 0..=upto {
        let mut acc = num.get(i).copied().unwrap_or(0);
        for k in 1..=i { acc -= j.get(k).copied().unwrap_or(0) * out[i - k]; }
        out[i] = acc;
    }
    out
}

fn e_t(legs: &[(i64, i64)]) -> (usize, usize) {
    let n = legs.len();
    let eq = |i: usize, j: usize| legs[i].0 * legs[j].1 == legs[j].0 * legs[i].1;
    let mut e = 0;
    if n >= 2 && eq(0, 1) { e += 1; }
    if n >= 2 && eq(n - 2, n - 1) { e += 1; }
    if n == 2 && eq(0, 1) { e = 1; }
    let mut t = 0;
    for i in 0..n.saturating_sub(2) {
        if eq(i, i + 1) && eq(i + 1, i + 2) { t += 1; }
    }
    (e, t)
}

// ---------------------------------------------------------------- the atlas file

/// One row of the input file:
///   label | legs | depth | expected layer counts (optional) | expected cd (optional)
/// Legs are comma-separated positive rationals `p` or `p/q`.  "Expected cd" is a positive
/// integer, or `inf` for "no deviation from the envelope up to the computed depth".
struct Row {
    label: String,
    legs: Vec<(i64, i64)>,
    depth: usize,
    exp_layers: Option<Vec<usize>>,
    exp_cd: Option<Option<usize>>, // Some(None) = inf
}

fn parse_row(line: &str) -> Result<Row, String> {
    let f: Vec<&str> = line.split('|').map(|s| s.trim()).collect();
    if f.len() < 3 { return Err(format!("need at least 3 fields, got {}", f.len())); }
    let label = f[0].to_string();
    let mut legs = Vec::new();
    for tok in f[1].split(',') {
        let tok = tok.trim();
        let (num, den) = match tok.split_once('/') {
            Some((a, b)) => (a.trim(), b.trim()),
            None => (tok, "1"),
        };
        let num: i64 = num.parse().map_err(|_| format!("bad leg {tok:?}"))?;
        let den: i64 = den.parse().map_err(|_| format!("bad leg {tok:?}"))?;
        if num <= 0 || den <= 0 { return Err(format!("legs must be positive: {tok:?}")); }
        legs.push((num, den));
    }
    if legs.len() < 2 { return Err("need n >= 2 legs".into()); }
    let depth: usize = f[2].parse().map_err(|_| format!("bad depth {:?}", f[2]))?;
    let exp_layers = if f.len() > 3 && !f[3].is_empty() {
        let mut v = Vec::new();
        for tok in f[3].split(',') {
            v.push(tok.trim().parse::<usize>().map_err(|_| format!("bad count {tok:?}"))?);
        }
        Some(v)
    } else { None };
    let exp_cd = if f.len() > 4 && !f[4].is_empty() {
        let s = f[4];
        if s == "inf" { Some(None) }
        else { Some(Some(s.parse::<usize>().map_err(|_| format!("bad cd {s:?}"))?)) }
    } else { None };
    Ok(Row { label, legs, depth, exp_layers, exp_cd })
}

/// Run one row at the current prime.  Returns (layer counts actually computed, cap hit, ok).
fn run_row(r: &Row, max_ball: usize, quiet: bool) -> (Vec<usize>, bool, bool) {
    let n = r.legs.len();
    let gens = ortho_gens(&r.legs);
    let env = envelope(n, r.depth);
    let (sp, capped) = spheres(&gens, n, r.depth, max_ball);
    let reached = sp.len() - 1;
    let (e, t) = e_t(&r.legs);
    let pred = if e == 0 && t == 0 { "inf".to_string() }
               else if t >= 1 { "3".to_string() }
               else { "4".to_string() };
    let cd = (1..=reached).find(|&d| (sp[d] as i128) < env[d]);

    let mut ok = true;
    let mut notes: Vec<String> = Vec::new();
    if let Some(exp) = &r.exp_layers {
        if exp.len() > sp.len() {
            ok = false;
            notes.push(format!("FAIL expected {} layer counts, only {} computed",
                               exp.len(), sp.len()));
        } else if exp[..] != sp[..exp.len()] {
            ok = false;
            notes.push(format!("FAIL layer counts: expected {:?} got {:?}",
                               exp, &sp[..exp.len()]));
        } else {
            notes.push(format!("layer counts match the table ({} entries)", exp.len()));
        }
    }
    if let Some(exp) = &r.exp_cd {
        match (exp, cd) {
            (None, None) => notes.push(format!(
                "no deviation from the envelope through depth {reached}, as expected")),
            (None, Some(d)) => { ok = false;
                notes.push(format!("FAIL expected no deviation, found one at d = {d}")); }
            (Some(x), Some(d)) if *x == d =>
                notes.push(format!("first deviation at d = {d}, as expected")),
            (Some(x), Some(d)) => { ok = false;
                notes.push(format!("FAIL expected first deviation at d = {x}, found d = {d}")); }
            (Some(x), None) => { ok = false;
                notes.push(format!(
                    "FAIL expected first deviation at d = {x}, none through depth {reached}")); }
        }
    }
    if r.exp_cd.is_none() {
        notes.push(match cd {
            Some(d) => format!("first deviation at d = {d}"),
            None => format!("no deviation through depth {reached}"),
        });
    }
    if capped {
        notes.push(format!("BALL CAP {max_ball} hit: depth {reached} of {} reached",
                           r.depth));
    }

    if !quiet || !ok {
        println!("  {:24} n={} (e,t)=({},{})  (e,t)-rule predicts cd = {}",
                 r.label, n, e, t, pred);
        println!("  {:24}   u        = {:?}", "", sp);
        println!("  {:24}   envelope = {:?}", "",
                 env[..sp.len()].iter().map(|&x| x as usize).collect::<Vec<_>>());
        for s in &notes { println!("  {:24}   {}", "", s); }
    }
    (sp, capped, ok)
}

// ---------------------------------------------------------------- the three quartics

/// The three quartics of Lemma "cremona-empty", in the variables that actually occur.
///
/// The lemma is about quartics in the LEGS.  The paper records, in the paragraph before the
/// lemma, that the same equations read as conics in X = x^2, Z = z^2 have infinitely many
/// rational points, and names one on each: (X,Z) = (3,2) on X^2 + 6XZ + Z^2 = k^2 with k = 7,
/// and (X,Z) = (2,5) and (5,9) on the other two.  This routine checks both halves: that the
/// quartic search over the stated box finds nothing, and that the three named conic points are
/// genuine solutions, so that the restriction to squares is not cosmetic.  Returns true iff
/// both halves came out as the paper states.
fn quartic_search(bound: i64) -> bool {
    let is_sq = |v: i128| -> bool {
        if v < 0 { return false; }
        let mut r = (v as f64).sqrt() as i128;
        while r * r > v { r -= 1; }
        while (r + 1) * (r + 1) <= v { r += 1; }
        r * r == v
    };
    // (name, coefficients p2 X^2 + q2 XZ + r2 Z^2, the conic point named in the paper)
    let forms: [(&str, i128, i128, i128, (i128, i128)); 3] = [
        ("V_1/4 : x^4 + 14 x^2 z^2 + z^4", 1, 14, 1, (2, 5)),
        ("V_1/2 : x^4 +  6 x^2 z^2 + z^4", 1, 6, 1, (3, 2)),
        ("V_3/4 : 9x^4 + 30 x^2 z^2 + 9z^4", 9, 30, 9, (5, 9)),
    ];
    let mut ok = true;
    for (name, p2, q2, r2, (px, pz)) in forms {
        let mut bad: Vec<(i64, i64)> = Vec::new();
        let mut conic_hits = 0usize;
        for x in 1..=bound {
            for z in 1..=bound {
                if x == z { continue; }
                let (xi, zi) = (x as i128, z as i128);
                let v = p2 * xi * xi * xi * xi + q2 * xi * xi * zi * zi + r2 * zi * zi * zi * zi;
                if is_sq(v) && bad.len() < 4 { bad.push((x, z)); }
                let w = p2 * xi * xi + q2 * xi * zi + r2 * zi * zi;
                if is_sq(w) { conic_hits += 1; }
            }
        }
        let val = p2 * px * px + q2 * px * pz + r2 * pz * pz;
        let named_ok = is_sq(val);
        let k = { let mut r = (val as f64).sqrt() as i128;
                  while r * r > val { r -= 1; }
                  while (r + 1) * (r + 1) <= val { r += 1; }
                  r };
        println!("  {}", name);
        println!("      as a quartic in (x,z), x != z, 1..{}: {}", bound,
                 if bad.is_empty() { "NO nontrivial solution".to_string() }
                 else { format!("SOLUTIONS {:?}", bad) });
        println!("      as a conic in (X,Z), X != Z, 1..{}: {} solutions; \
                  the point named in the paper is (X,Z) = ({},{}), value {} = {}^2 [{}]",
                 bound, conic_hits, px, pz, val, k,
                 if named_ok { "confirmed" } else { "NOT A SQUARE -- FAIL" });
        if !bad.is_empty() {
            println!("      FAIL: the quartic was expected to have no nontrivial solution here");
            ok = false;
        }
        if !named_ok || conic_hits == 0 {
            println!("      FAIL: the conic was expected to have rational points here");
            ok = false;
        }
    }
    println!("  The contrast between the two lines is the point: the quartics are empty on the");
    println!("  box, the conics in X = x^2, Z = z^2 are not, so the restriction to squares in");
    println!("  Lemma \"cremona-empty\" is not cosmetic.");
    ok
}

// ---------------------------------------------------------------- main

fn tool_dir() -> PathBuf {
    // the atlas ships next to Cargo.toml
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    let mut atlas: Option<String> = None;
    let mut inline: Vec<String> = Vec::new();
    let mut quartic_bound: i64 = 300;
    let mut do_quartics = true;
    let mut max_ball: usize = 3_000_000;
    let mut quiet = false;
    let mut i = 1;
    while i < argv.len() {
        match argv[i].as_str() {
            "--atlas" => { i += 1; atlas = Some(argv[i].clone()); }
            "--row" => { i += 1; inline.push(argv[i].clone()); }
            "--quartics" => { i += 1; quartic_bound = argv[i].parse().expect("bad --quartics"); }
            "--no-quartics" => { do_quartics = false; }
            "--max-ball" => { i += 1; max_ball = argv[i].parse().expect("bad --max-ball"); }
            "--quiet" => { quiet = true; }
            "-h" | "--help" => {
                println!("usage: ortho_cd [--atlas FILE] [--row \"label | legs | depth \
                          [| layers [| cd]]\"]");
                println!("                [--quartics BOUND] [--no-quartics] \
                          [--max-ball N] [--quiet]");
                return;
            }
            other => { eprintln!("unknown argument {other:?}"); exit(2); }
        }
        i += 1;
    }

    // Collect the rows.
    let mut src: Vec<(usize, String)> = Vec::new();
    if inline.is_empty() {
        let path = match &atlas {
            Some(s) => PathBuf::from(s),
            None => tool_dir().join("atlas.txt"),
        };
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| { eprintln!("cannot read {}: {e}", path.display()); exit(2); });
        for (k, line) in text.lines().enumerate() {
            let l = line.trim();
            if l.is_empty() || l.starts_with('#') { continue; }
            src.push((k + 1, l.to_string()));
        }
        println!("atlas: {} ({} rows)", path.display(), src.len());
    } else {
        for (k, s) in inline.iter().enumerate() { src.push((k + 1, s.clone())); }
    }
    let rows: Vec<Row> = src.iter().map(|(ln, s)| parse_row(s)
        .unwrap_or_else(|e| { eprintln!("line {ln}: {e}"); exit(2); })).collect();

    let mut all_ok = true;

    if do_quartics {
        println!("\n=== the three quartics, box 1..{quartic_bound} ===");
        all_ok &= quartic_search(quartic_bound);
    }

    // Two primes; the two runs must agree row by row.
    let mut per_prime: Vec<Vec<Vec<usize>>> = Vec::new();
    let primes = [(1u64 << 61) - 1, 2_305_843_009_213_700_000];
    for seed in primes {
        let mut c = seed | 1;
        while !is_prime(c) { c += 2; }
        unsafe { P = c; }
        println!("\n=== p = {c} ===");
        let mut here = Vec::new();
        for r in &rows {
            let (sp, _capped, ok) = run_row(r, max_ball, quiet);
            all_ok &= ok;
            here.push(sp);
        }
        per_prime.push(here);
    }

    println!("\n=== cross-prime agreement ===");
    let mut disagree = 0;
    for (k, r) in rows.iter().enumerate() {
        if per_prime[0][k] != per_prime[1][k] {
            println!("  DISAGREE {}: {:?} vs {:?}", r.label, per_prime[0][k], per_prime[1][k]);
            disagree += 1;
        }
    }
    if disagree == 0 { println!("  all {} rows agree at both primes", rows.len()); }
    else { all_ok = false; }

    println!("\n{}", if all_ok { "VERDICT: all expectations met" }
                     else { "VERDICT: FAIL, see the lines marked FAIL above" });
    if !all_ok { exit(1); }
}
