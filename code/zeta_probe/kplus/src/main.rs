// kplus: checks that the positive compact locus K+ of the Gram hypersurface of W_n
// (x_i = c_i^2 in (0,1), D_2..D_n > 0, D_{n+1} = 0) is exactly the set of squared
// consecutive-facet cosines of n-orthoschemes, with the explicit inverse
// b_{k+1}/b_k = x_k D_{k-1}/D_{k+1}  (b_i = a_i^2 squared legs).
// Also checks D_{n-1} != 0 at the paper's Vinberg points (exact integers), n = 3..200.
fn lcg(s: &mut u64) -> f64 { *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); ((*s >> 11) as f64) / ((1u64 << 53) as f64) }
fn normals(a: &[f64]) -> Vec<Vec<f64>> {
    let n = a.len(); let mut m = vec![];
    let mut v = vec![0.0; n]; v[0] = 1.0; m.push(v);
    for j in 1..n { let mut v = vec![0.0; n]; v[j-1] = a[j]; v[j] = -a[j-1]; m.push(v); }
    let mut v = vec![0.0; n]; v[n-1] = 1.0; m.push(v);
    for v in m.iter_mut() { let s: f64 = v.iter().map(|t| t*t).sum::<f64>().sqrt(); for t in v.iter_mut() { *t /= s; } }
    m
}
fn gram(m: &[Vec<f64>]) -> Vec<Vec<f64>> { m.iter().map(|u| m.iter().map(|v| u.iter().zip(v).map(|(p,q)| p*q).sum()).collect()).collect() }
fn conts(x: &[f64]) -> Vec<f64> { let mut d = vec![1.0, 1.0]; for k in 1..=x.len() { let t = d[k] - x[k-1]*d[k-1]; d.push(t); } d }
fn main() {
    let mut s = 12345u64; let mut worst_fwd = 0f64; let mut worst_inv = 0f64; let mut worst_orth = 0f64; let mut minD = f64::INFINITY;
    for n in 3..=12 { for _ in 0..2000 {
        // forward: random legs -> x, check K+ membership and closed form
        let a: Vec<f64> = (0..n).map(|_| 0.1 + 3.0*lcg(&mut s)).collect();
        let g = gram(&normals(&a));
        for i in 0..=n { for j in 0..=n { if (i as i64 - j as i64).abs() >= 2 { worst_orth = worst_orth.max(g[i][j].abs()); } } }
        let x: Vec<f64> = (1..=n).map(|k| g[k-1][k]*g[k-1][k]).collect();
        let b: Vec<f64> = a.iter().map(|t| t*t).collect();
        let d = conts(&x);
        worst_fwd = worst_fwd.max(d[n+1].abs());
        for k in 2..=n { minD = minD.min(d[k]); }
        for k in 1..n { let pred: f64 = (0..k).map(|j| b[j]/(b[j]+b[j+1])).product(); worst_fwd = worst_fwd.max((d[k+1]-pred).abs()); }
        // inverse: random x_1..x_{n-1} with D_k>0, x_n = D_n/D_{n-1}, rebuild legs, compare
        let mut xr: Vec<f64>;
        loop { xr = (0..n-1).map(|_| lcg(&mut s)).collect(); let d = conts(&xr); if (2..=n).all(|k| d[k] > 1e-3) { break; } }
        let d = conts(&xr); xr.push(d[n]/d[n-1]);
        let dd = conts(&xr);
        let mut bb = vec![1.0f64];
        for k in 1..n { let r = xr[k-1]*dd[k-1]/dd[k+1]; let last = *bb.last().unwrap(); bb.push(last*r); }
        let aa: Vec<f64> = bb.iter().map(|t| t.sqrt()).collect();
        let g2 = gram(&normals(&aa));
        for k in 1..=n { worst_inv = worst_inv.max(((g2[k-1][k]*g2[k-1][k]) - xr[k-1]).abs() / xr[k-1].max(1e-12)); }
    }}
    println!("forward: max |D_(n+1)| and closed-form error = {:.3e}; min D_k (k=2..n) = {:.3e}", worst_fwd, minD);
    println!("non-adjacent normals orthogonal: max |G_ij|, |i-j|>=2 = {:.3e}", worst_orth);
    println!("inverse (K+ point -> legs -> Gram) max rel error = {:.3e}", worst_inv);
    // exact integer check at the Vinberg points of Lemma vinbergpoint
    let mut ok = true;
    for n in 3..=200usize {
        let fam: Vec<i128> = match n % 3 { 1 => vec![], 0 => vec![2], _ => vec![2,1,3] };
        let mut x: Vec<i128> = fam.clone(); while x.len() < n-1 { x.push(1); }
        let mut d: Vec<i128> = vec![1,1]; for k in 1..n { let t = d[k] - x[k-1]*d[k-1]; d.push(t); }
        // x_n = D_n / D_{n-1}
        if d[n-1] == 0 || d[n] % d[n-1] != 0 { ok = false; println!("n={} D_(n-1)={} D_n={}", n, d[n-1], d[n]); continue; }
        let xn = d[n]/d[n-1]; x.push(xn);
        let dn1 = d[n] - xn*d[n-1];
        if xn < 1 || dn1 != 0 || x.iter().any(|&t| t < 1) { ok = false; println!("n={} fails: xn={} D_(n+1)={}", n, xn, dn1); }
    }
    println!("Vinberg points n=3..200: all x_i>=1, D_(n+1)=0, D_(n-1)!=0 : {}", ok);
}
