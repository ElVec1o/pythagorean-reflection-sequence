// assemblycontract -- exact cross-check of the NAMED assembly contract formalised in
// lean/with_mathlib/AssemblyContract.lean (BLOCK 343).
//
// The Lean file replaces the vacuous existential `EltBridge.IsAssembly` by a contract
// whose coefficients are NAMED, built from ordered products of BLOCK 340's transfer
// `EltBridge.maxM`:
//
//   maxProd q j 0     = I
//   maxProd q j (a+1) = if j <= a then maxM q (a+1) * maxProd q j a else I
//   maxM q a          = [[1 + 2q^{2a}, -2q^a], [2q^{3a}, 1 - 2q^{2a}]]
//
//   alpha(q,M) = ( maxProd q 0 M . [1,1]
//                  + sum_{j=0}^{M-1} maxProd q (j+1) M . [2, 2q^{j+1}] )_1
//   beta (q,M) = ( maxProd q 0 M . [q^2,q^2]
//                  + sum_{j=0}^{M-1} maxProd q (j+1) M . [2q^{j+1}, 2q^{2(j+1)}] )_1
//
//   IsMaxAssembly q M W  <=>  W = alpha(q,M) + beta(q,M) * W
//
// Lean proves (0 sorry, axioms propext/Classical.choice/Quot.sound only):
//   * the contract has EXACTLY ONE solution over PowerSeries Z at q = X
//     (isMaxAssembly_existsUnique), so it is not vacuous in either direction;
//   * the truncated bulk model exists at every cutoff M (bulkSol, via the unipotent
//     finite system (1-K)u = 1) and its generating constant S'(M) satisfies it
//     (bulk_isMaxAssembly), hence EQUALS the unique solution (bulk_eq_of_isMaxAssembly).
//
// This program checks the numerical content of that, in exact i128 truncated at degree D:
//
//  [1] BRUTE  solve the truncated bulk system directly (raw max-kernel double sum, no
//             algebra) and form  Tc = sum_{b<=M} m(b) X^b u(b).
//  [2] NAMED  compute alpha, beta from the ordered products above and solve the scalar
//             affine equation  W = alpha + beta W, i.e. W = alpha/(1-beta).
//  [3] AGREE  [1] == [2] for every cutoff M -- the Lean identification, numerically.
//  [4] LIMIT  at M >= D, Tc reproduces BLOCK 340's tabulated T series
//             1, 2, 3, 10, 9, 30, 37, 82, 133, 236, 457, 702, 1455, 2248, 4469, ...
//  [5] UNIT   1 - beta(X,M) has constant term 1 (the Lean uniqueness hypothesis).
//
// Rust only (repo rule: never Python for enumeration).
// cargo run --release --bin assemblycontract

type Poly = Vec<i128>;

fn zero(d: usize) -> Poly { vec![0; d + 1] }
fn one(d: usize) -> Poly { let mut p = zero(d); p[0] = 1; p }
fn xpow(d: usize, k: usize) -> Poly { let mut p = zero(d); if k <= d { p[k] = 1; } p }

fn add(a: &Poly, b: &Poly) -> Poly {
    a.iter().zip(b.iter()).map(|(x, y)| x.checked_add(*y).expect("overflow add")).collect()
}
fn sub(a: &Poly, b: &Poly) -> Poly {
    a.iter().zip(b.iter()).map(|(x, y)| x.checked_sub(*y).expect("overflow sub")).collect()
}
fn scal(a: &Poly, c: i128) -> Poly {
    a.iter().map(|x| x.checked_mul(c).expect("overflow scal")).collect()
}
fn mul(a: &Poly, b: &Poly) -> Poly {
    let d = a.len() - 1;
    let mut out = zero(d);
    for i in 0..=d {
        if a[i] == 0 { continue; }
        for j in 0..=(d - i) {
            if b[j] == 0 { continue; }
            let t = a[i].checked_mul(b[j]).expect("overflow mul");
            out[i + j] = out[i + j].checked_add(t).expect("overflow mul-acc");
        }
    }
    out
}
/// formal inverse; requires constant term +-1
fn inv(a: &Poly) -> Poly {
    let d = a.len() - 1;
    assert!(a[0] == 1 || a[0] == -1, "inverse needs unit constant term, got {}", a[0]);
    let mut out = zero(d);
    out[0] = a[0];
    for n in 1..=d {
        let mut s: i128 = 0;
        for k in 1..=n { s += a[k] * out[n - k]; }
        out[n] = -s / a[0];
        assert_eq!(a[0] * out[n] + s, 0, "non-exact inverse step");
    }
    out
}

type Mat = [[Poly; 2]; 2];
type Vec2 = [Poly; 2];

fn mat_id(d: usize) -> Mat { [[one(d), zero(d)], [zero(d), one(d)]] }

fn mat_mul(a: &Mat, b: &Mat) -> Mat {
    let d = a[0][0].len() - 1;
    let mut out = [[zero(d), zero(d)], [zero(d), zero(d)]];
    for i in 0..2 { for j in 0..2 {
        let mut s = zero(d);
        for k in 0..2 { s = add(&s, &mul(&a[i][k], &b[k][j])); }
        out[i][j] = s;
    }}
    out
}

fn mat_vec(a: &Mat, v: &Vec2) -> Vec2 {
    [ add(&mul(&a[0][0], &v[0]), &mul(&a[0][1], &v[1])),
      add(&mul(&a[1][0], &v[0]), &mul(&a[1][1], &v[1])) ]
}

/// EltBridge.maxM q a = !![1 + 2q^a q^a, -(2 q^a); 2 q^a q^a q^a, 1 - 2 q^a q^a]
fn max_m(d: usize, a: usize) -> Mat {
    let qa = xpow(d, a);
    let q2a = xpow(d, 2 * a);
    let q3a = xpow(d, 3 * a);
    [[ add(&one(d), &scal(&q2a, 2)), scal(&qa, -2) ],
     [ scal(&q3a, 2),                sub(&one(d), &scal(&q2a, 2)) ]]
}

/// AssemblyContract.maxProd q j a
fn max_prod(d: usize, j: usize, a: usize) -> Mat {
    let mut acc = mat_id(d);
    // maxProd q j (a) = maxM q a * maxM q (a-1) * ... * maxM q (j+1)
    let mut cur = a;
    while cur >= 1 && cur > j {
        acc = mat_mul(&acc, &max_m(d, cur));
        cur -= 1;
    }
    acc
}

fn m_mult(b: usize) -> i128 { if b == 0 { 1 } else { 2 } }
fn mu_n(a: usize) -> usize { if a == 0 { 2 } else { a } }

/// [1] the raw truncated bulk system, solved by direct iteration of the max kernel.
fn brute_tc(d: usize, cutoff: usize) -> Poly {
    let mut u: Vec<Poly> = (0..=cutoff).map(|_| zero(d)).collect();
    for _ in 0..(d + 2) {
        let mut nu: Vec<Poly> = Vec::with_capacity(cutoff + 1);
        for a in 0..=cutoff {
            let mut s = zero(d);
            for b in 0..=cutoff {
                let t = mul(&xpow(d, a.max(b)), &u[b]);
                s = add(&s, &scal(&t, m_mult(b)));
            }
            nu.push(add(&one(d), &mul(&xpow(d, mu_n(a)), &s)));
        }
        u = nu;
    }
    let mut tc = zero(d);
    for b in 0..=cutoff {
        tc = add(&tc, &scal(&mul(&xpow(d, b), &u[b]), m_mult(b)));
    }
    tc
}

/// [2] alpha, beta exactly as AssemblyContract.maxAlpha / maxBeta.
fn alpha_beta(d: usize, cutoff: usize) -> (Poly, Poly) {
    let init_a: Vec2 = [one(d), one(d)];
    let init_b: Vec2 = [xpow(d, 2), xpow(d, 2)];
    let p0 = max_prod(d, 0, cutoff);
    let mut va = mat_vec(&p0, &init_a);
    let mut vb = mat_vec(&p0, &init_b);
    for j in 0..cutoff {
        let jj = j + 1;
        let pj = max_prod(d, jj, cutoff);
        let sa: Vec2 = [scal(&one(d), 2), scal(&xpow(d, jj), 2)];
        let sb: Vec2 = [scal(&xpow(d, jj), 2), scal(&xpow(d, 2 * jj), 2)];
        let ta = mat_vec(&pj, &sa);
        let tb = mat_vec(&pj, &sb);
        va = [add(&va[0], &ta[0]), add(&va[1], &ta[1])];
        vb = [add(&vb[0], &tb[0]), add(&vb[1], &tb[1])];
    }
    (va[1].clone(), vb[1].clone())
}

fn main() {
    let d: usize = 40;
    println!("assemblycontract -- named assembly contract cross-check, degree D = {}", d);
    println!();

    let mut all_ok = true;

    // [3] contract solution == brute-force bulk constant, at every cutoff
    println!("[3] AGREE  named contract solution  vs  raw truncated bulk model");
    for cutoff in 0..=14usize {
        let tc = brute_tc(d, cutoff);
        let (alpha, beta) = alpha_beta(d, cutoff);
        assert_eq!(beta[0], 0, "beta must have zero constant term (cutoff {})", cutoff);
        let w = mul(&alpha, &inv(&sub(&one(d), &beta)));
        let ok = w == tc;
        if !ok { all_ok = false; }
        println!("    cutoff M = {:2}   alpha+beta*W == S'(M) : {}", cutoff, if ok { "OK" } else { "MISMATCH" });
        if !ok {
            println!("        named : {:?}", &w[..12.min(w.len())]);
            println!("        brute : {:?}", &tc[..12.min(tc.len())]);
        }
        // also check the contract equation itself holds for the brute-force value
        let lhs = tc.clone();
        let rhs = add(&alpha, &mul(&beta, &tc));
        if lhs != rhs { all_ok = false; println!("        contract equation FAILS at cutoff {}", cutoff); }
    }
    println!();

    // [4] the M -> infinity limit reproduces BLOCK 340's T series
    println!("[4] LIMIT  S'(M) at M >= D reproduces BLOCK 340's tabulated T");
    let dsmall = 16usize;
    let tc = brute_tc(dsmall, dsmall + 2);
    let (alpha, beta) = alpha_beta(dsmall, dsmall + 2);
    let w = mul(&alpha, &inv(&sub(&one(dsmall), &beta)));
    let expect: Vec<i128> = vec![1, 2, 3, 10, 9, 30, 37, 82, 133, 236, 457, 702, 1455, 2248, 4469, 7308];
    let got: Vec<i128> = tc[..expect.len()].to_vec();
    let got_named: Vec<i128> = w[..expect.len()].to_vec();
    println!("    expected (README BLOCK 340) : {:?}", expect);
    println!("    brute                       : {:?}", got);
    println!("    named contract              : {:?}", got_named);
    if got != expect || got_named != expect { all_ok = false; println!("    MISMATCH"); } else { println!("    OK"); }
    println!();

    // [5] 1 - beta is a unit
    println!("[5] UNIT   constant term of 1 - beta(X,M)");
    for cutoff in [0usize, 1, 3, 7, 12] {
        let (_, beta) = alpha_beta(d, cutoff);
        let c = 1 - beta[0];
        println!("    cutoff M = {:2}   const(1-beta) = {}", cutoff, c);
        if c != 1 { all_ok = false; }
    }
    println!();

    println!("{}", if all_ok { "ALL CHECKS PASS" } else { "SOME CHECK FAILED" });
    assert!(all_ok, "assemblycontract: a check failed");
}
