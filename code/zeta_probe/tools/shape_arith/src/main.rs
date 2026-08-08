// shape_arith -- the four remaining numerical claims of paper 1, checked exactly.
//
// Definitions (paper 1, "Arithmetic complexity and minimal polynomial"): scale the legs to
// coprime integers (a,b), a != b.  With lambda = a - bi when a+b is odd and
// lambda = (a - bi)/(1 + i) when a and b are both odd, the arithmetic complexity is
// c_T = N(lambda), and e_T = 2(a^2 - b^2) resp. a^2 - b^2.  The minimal polynomial is
// mu_T(t) = c_T t^2 - e_T t + c_T.
//
// CLAIM 1.  "Each admissible complexity is realized by finitely many rotation numbers
//            (sixteen for d = 30; twenty-four for d = 36)."
// CLAIM 2.  the element -2(t+1) mu_{(1,2)} has lamp profile (-10, 2, 2, -10).
// CLAIM 3.  e_T is always even (hence the four "abstract pairs" with odd e are unrealizable).
// CLAIM 4.  the strand bound's alphabet has "exactly eight shapes".
//
// Rule 8: every loop is bounded by an explicit constant; peak memory is a few MB.

const AMAX: i64 = 400; // bound on legs; c_T <= 72 needs only a,b <= 12

fn gcd(mut x: i64, mut y: i64) -> i64 {
    while y != 0 { let t = x % y; x = y; y = t; }
    x.abs()
}

/// (c_T, e_T) for a coprime ordered pair with a != b, both positive.
/// e_T is reported with the sign the definition gives; the paper's tables use |e_T|.
fn ce(a: i64, b: i64) -> (i64, i64) {
    if (a + b) % 2 != 0 {
        (a * a + b * b, 2 * (a * a - b * b))
    } else {
        // a, b both odd (they are coprime, so not both even)
        ((a * a + b * b) / 2, a * a - b * b)
    }
}

fn main() {
    // ---------------- CLAIM 1: how many shapes have c_T <= 2d ----------------
    // A "shape" is an unordered pair {a,b} of coprime positive integers with a != b; the
    // rotation number zeta_T = (a+bi)/(a-bi) determines and is determined by it.
    println!("=== CLAIM 1: shapes by arithmetic complexity ===");
    let mut shapes: Vec<(i64, i64, i64, i64)> = Vec::new(); // (c, |e|, a, b)
    for a in 1..=30i64 {
        for b in (a + 1)..=30i64 {
            if gcd(a, b) != 1 { continue; }
            let (c, e) = ce(a, b);
            if c <= 100 { shapes.push((c, e.abs(), a, b)); }
        }
    }
    shapes.sort();
    for &bound in &[60i64, 64, 72] {
        let sel: Vec<_> = shapes.iter().filter(|s| s.0 <= bound).collect();
        let mut comps: Vec<i64> = sel.iter().map(|s| s.0).collect();
        comps.dedup();
        println!("  c_T <= {:3}:  {} shapes, over {} distinct complexities {:?}",
                 bound, sel.len(), comps.len(), comps);
    }
    println!("  breakdown at c_T <= 72:");
    let mut last = -1i64;
    for &&(c, e, a, b) in shapes.iter().filter(|s| s.0 <= 72).collect::<Vec<_>>().iter() {
        if c != last { print!("\n    c_T={:3}: ", c); last = c; }
        print!("({},{}) e={}  ", a, b, e);
    }
    println!("\n  NOTE: 65 = 5*13 is the first complexity with TWO essentially distinct");
    println!("  representations as a sum of two squares, so it contributes FOUR shapes,");
    println!("  not two.  That is the whole of the discrepancy between 22 and 24.");

    // ---------------- CLAIM 2: the lamp profile of -2(t+1) mu ----------------
    println!("\n=== CLAIM 2: lamp profile of -2(t+1) mu_T ===");
    for &(a, b) in &[(1i64, 2i64), (2, 1)] {
        let (c, e_signed) = ce(a, b);
        for &(label, e) in &[("as defined (signed)", e_signed), ("as tabulated (|e|)", e_signed.abs())] {
            // mu = c t^2 - e t + c ; multiply by -2(t+1)
            // -2(t+1)(c t^2 - e t + c) = -2( c t^3 + (c-e) t^2 + (c-e) t + c )
            let coeffs = [-2 * c, -2 * (c - e), -2 * (c - e), -2 * c]; // t^0..t^3, palindromic
            println!("  (a,b)=({},{})  {}: c={} e={}  mu = {}t^2 {}{}t + {}  ->  profile {:?}",
                     a, b, label, c, e, c,
                     if e > 0 { "- " } else { "+ " }, e.abs(), c, coeffs);
        }
    }
    println!("  The paper's profile (-10, 2, 2, -10) requires e = +6, i.e. mu = 5t^2 - 6t + 5.");
    println!("  The definition with (a,b) = (1,2) gives e = 2(1-4) = -6 and mu = 5t^2 + 6t + 5,");
    println!("  whose profile is (-10, -22, -22, -10).  The tables use |e| throughout, so the");
    println!("  profile is right and the DEFINITION's sign convention is what is inconsistent.");

    // ---------------- CLAIM 3: parity of e_T ----------------
    println!("\n=== CLAIM 3: is e_T always even? ===");
    let mut odd = 0u64;
    let mut tested = 0u64;
    for a in 1..=AMAX {
        for b in 1..=AMAX {
            if a == b || gcd(a, b) != 1 { continue; }
            let (_, e) = ce(a, b);
            tested += 1;
            if e % 2 != 0 { odd += 1; }
        }
    }
    println!("  coprime ordered pairs with a != b, legs <= {}: {} tested, {} with odd e_T",
             AMAX, tested, odd);
    println!("  (Proof: a+b odd gives e_T = 2(a^2-b^2), even outright; a,b both odd gives");
    println!("   e_T = a^2 - b^2, a difference of two odd squares, hence even. Formalised in");
    println!("   lean/with_mathlib/ShapeArith.lean as e_T_even.)");
    print!("  the four 'abstract pairs' of the deviation-law table: ");
    for &(c, e) in &[(61i64, 11i64), (37, 35), (53, 45), (73, 55)] {
        let realizable = shapes.iter().any(|s| s.0 == c && s.1 == e);
        print!("({},{}) {}   ", c, e, if realizable { "realizable" } else { "NOT realizable" });
    }
    println!("\n  all four have odd e, so none is the (c_T,e_T) of any rational-leg triangle.");

    // ---------------- CLAIM 4: the strand alphabet ----------------
    println!("\n=== CLAIM 4: size of the strand alphabet ===");
    let contents = ["(1,0)", "(0,1)", "(1,1)"];
    let signs = ["lamp +", "lamp -"];
    let markers = ["marker", "no marker"];
    let mut count = 0;
    for c in contents { for s in signs { for m in markers { let _ = (c, s, m); count += 1; } } }
    println!("  the refinement stated in the proof is 3 crossing contents x 2 lamp signs");
    println!("  x 2 marker states = {}, not 8.", count);
    println!("  What the downstream argument uses is only that the alphabet is FINITE and that");
    println!("  exactly one letter, the through-shape (1,1), has unbounded multiplicity.");
}
