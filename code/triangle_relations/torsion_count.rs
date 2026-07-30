// Count how many of the c^2 words w_{a,b} have finite order in W_m = D_m * C_2.
// Criterion (proved in lean/with_mathlib/CoxeterTorsion.lean):
//   w = u0 x2 u1 x2 u2 has finite order  <=>  u1 = 1 in D_m  or  u2*u0 = 1 in D_m.
// D_m elements as (k, e): rot^k * r0^e, with rot = r0 r1 of order m.
#[derive(Clone, Copy, PartialEq)]
struct D { k: i64, e: u8 }
fn mul(x: D, y: D, m: i64) -> D {
    let k = if x.e == 0 { x.k + y.k } else { x.k - y.k };
    D { k: ((k % m) + m) % m, e: (x.e + y.e) % 2 }
}
const ID: D = D { k: 0, e: 0 };
fn gen(i: u8, m: i64) -> D {           // r0 = (0,1); r1 = r0*rot = (-1,1)
    if i == 0 { D { k: 0, e: 1 } } else { D { k: ((-1 % m) + m) % m, e: 1 } }
}
fn eval(w: &[u8], m: i64) -> D { w.iter().fold(ID, |acc, &l| mul(acc, gen(l, m), m)) }

fn main() {
    let mut bad = 0usize;
    for m in 3..=60i64 {
        for c in 1..=(m - 1) {
            let mut fin = 0usize;
            let mut wit: Vec<(i64, i64)> = Vec::new();
            for a in 0..=c {
                for b in 1..=(c + 1) {
                    if b == a || b == a + 1 { continue; }
                    // build w_{a,b}: positions 1..2c+2
                    let mut word: Vec<u8> = Vec::new();
                    for p in 1..=(2 * c + 2) {
                        if p % 2 == 1 { word.push(if p == 2 * a + 1 { 2 } else { 1 }); }
                        else { word.push(if p == 2 * b { 2 } else { 0 }); }
                    }
                    let idx: Vec<usize> = (0..word.len()).filter(|&i| word[i] == 2).collect();
                    assert_eq!(idx.len(), 2);
                    let u0 = eval(&word[..idx[0]], m);
                    let u1 = eval(&word[idx[0] + 1..idx[1]], m);
                    let u2 = eval(&word[idx[1] + 1..], m);
                    if u1 == ID || mul(u2, u0, m) == ID { fin += 1; wit.push((a, b)); }
                }
            }
            if fin != 1 {
                bad += 1;
                if bad <= 12 {
                    println!("m={:2} c={:2}  finite-order count = {:3}  (paper claims 1)  first few {:?}",
                             m, c, fin, &wit[..wit.len().min(4)]);
                }
            }
        }
    }
    println!("\n(m,c) pairs where the count is NOT 1, over 3<=m<=60, 1<=c<=m-1: {}", bad);
    // where does it start failing, as a function of c vs m?
    println!("\n--- smallest failing c for each m (3..=20) ---");
    for m in 3..=20i64 {
        let mut first = None;
        for c in 1..=(m - 1) {
            let mut fin = 0usize;
            for a in 0..=c { for b in 1..=(c + 1) {
                if b == a || b == a + 1 { continue; }
                let mut word: Vec<u8> = Vec::new();
                for p in 1..=(2 * c + 2) {
                    if p % 2 == 1 { word.push(if p == 2 * a + 1 { 2 } else { 1 }); }
                    else { word.push(if p == 2 * b { 2 } else { 0 }); }
                }
                let idx: Vec<usize> = (0..word.len()).filter(|&i| word[i] == 2).collect();
                let u0 = eval(&word[..idx[0]], m);
                let u1 = eval(&word[idx[0] + 1..idx[1]], m);
                let u2 = eval(&word[idx[1] + 1..], m);
                if u1 == ID || mul(u2, u0, m) == ID { fin += 1; }
            }}
            if fin != 1 { first = Some((c, fin)); break; }
        }
        match first {
            Some((c, f)) => println!("m={:2}: first failure at c={:2} (count {}), m/2 = {:.1}", m, c, f, m as f64 / 2.0),
            None => println!("m={:2}: no failure for any c <= m-1", m),
        }
    }
}
