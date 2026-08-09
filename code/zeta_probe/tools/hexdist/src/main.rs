// hexdist -- the graph distance k(n,j) = d_X(e, f_{n,j}) of paper 4, mapped exactly.
//
// X is the honeycomb dual to the triangular lattice of sites (n,j), with hex generators
// a=(1,0), b=(0,1), c=(1,-1) and a=b+c.  A VERTEX of X is a triangle of mutually hex-adjacent
// sites; there are two families,
//     up   (n,j,0) = {(n,j), (n+1,j), (n,j+1)}
//     down (n,j,1) = {(n,j), (n+1,j), (n+1,j-1)}
// and up (n,j,0) is adjacent to down (n,j,1), (n-1,j+1,1) and (n,j+1,1), giving degree 3.
// Each site lies on six vertices, the six corners of its hexagon.
// The base vertex is e = {(0,0), (-1,0), (-1,1)} = up(-1,0,0), which is exactly the triple of
// base sites of the paper.
//
// k(n,j) := min over the six vertices of the hexagon of (n,j) of the X-distance to e.
//
// Purpose: cor:antipair's lower bound is currently VERIFIED, not proved.  This maps the row
// structure exactly so the provable statement can be identified.
//
// Rule 8: BFS over a bounded radius; vertex count ~ 6R^2, a few MB at R = 120.

use std::collections::HashMap;

const R: i64 = 120;              // half-width of the site window
const MAX_V: usize = 4_000_000;  // hard cap (Rule 8)

#[inline]
fn key(n: i64, j: i64, t: u8) -> (i64, i64, u8) { (n, j, t) }

/// the three neighbours of a vertex
fn nbrs(n: i64, j: i64, t: u8) -> [(i64, i64, u8); 3] {
    if t == 0 {
        // up (n,j,0) ~ down (n,j,1), (n-1,j+1,1), (n,j+1,1)
        [key(n, j, 1), key(n - 1, j + 1, 1), key(n, j + 1, 1)]
    } else {
        // inverse of the above
        [key(n, j, 0), key(n + 1, j - 1, 0), key(n, j - 1, 0)]
    }
}

/// the six vertices whose triangle contains the site (n,j)
fn corners(n: i64, j: i64) -> [(i64, i64, u8); 6] {
    [
        key(n, j, 0), key(n - 1, j, 0), key(n, j - 1, 0),
        key(n, j, 1), key(n - 1, j, 1), key(n - 1, j + 1, 1),
    ]
}

fn main() {
    // BFS from e = up(-1,0,0)
    let start = key(-1, 0, 0);
    let mut dist: HashMap<(i64, i64, u8), i64> = HashMap::new();
    dist.insert(start, 0);
    let mut frontier = vec![start];
    let mut d = 0i64;
    while !frontier.is_empty() {
        d += 1;
        let mut next = Vec::new();
        for &(n, j, t) in &frontier {
            for &(m, k, u) in nbrs(n, j, t).iter() {
                if m.abs() > R + 2 || k.abs() > R + 2 { continue; }
                if !dist.contains_key(&(m, k, u)) {
                    dist.insert((m, k, u), d);
                    next.push((m, k, u));
                    assert!(dist.len() <= MAX_V, "vertex cap exceeded (Rule 8)");
                }
            }
        }
        frontier = next;
    }
    println!("BFS complete: {} vertices, eccentricity within window {}", dist.len(), d - 1);

    let kk = |n: i64, j: i64| -> Option<i64> {
        corners(n, j).iter().filter_map(|v| dist.get(v).copied()).min()
    };

    // ---- sanity: the paper's row-0 and row-1 closed forms ----
    println!("\n[1] lem:krows closed forms");
    let mut ok0 = true; let mut ok1 = true;
    for n in -40..=40i64 {
        let want0 = if n >= 0 { 2 * n } else { -2 * n - 2 };
        if kk(n, 0) != Some(want0) { ok0 = false; }
        let want1 = if n >= 0 { 2 * n + 1 } else if n == -1 { 0 } else { -2 * n - 3 };
        if kk(n, 1) != Some(want1) { ok1 = false; }
    }
    println!("  row 0 formula holds on |n|<=40: {}", ok0);
    println!("  row 1 formula holds on |n|<=40: {}", ok1);

    // ---- the row structure off the base rows ----
    println!("\n[2] row minima, valley width, and the profile");
    println!("   j   min   argmin-range        first few values from the left edge of the valley");
    for j in -12..=12i64 {
        let vals: Vec<i64> = (-60..=60).filter_map(|n| kk(n, j)).collect();
        let mn = *vals.iter().min().unwrap();
        let idx: Vec<usize> = vals.iter().enumerate().filter(|(_, &v)| v == mn).map(|(i, _)| i).collect();
        let lo = idx[0] as i64 - 60;
        let hi = *idx.last().unwrap() as i64 - 60;
        let mut prof = Vec::new();
        for n in hi..=(hi + 6).min(60) { if let Some(v) = kk(n, j) { prof.push(v); } }
        println!("  {:3}  {:4}   n in [{:4},{:4}] (w={})   {:?}", j, mn, lo, hi, hi - lo + 1, prof);
    }

    // ---- candidate law for the row minimum ----
    println!("\n[3] candidate: min_n k(n,j) = 2|j|-2 for j>=2, 2|j|-1 for j<=-1, 0 for j in {{0,1}}");
    let mut all = true;
    for j in -60..=60i64 {
        let mn = (-90..=90).filter_map(|n| kk(n, j)).min().unwrap();
        let pred = if j == 0 || j == 1 { 0 } else if j >= 2 { 2 * j - 2 } else { -2 * j - 1 };
        if mn != pred { println!("   MISMATCH j={} measured {} predicted {}", j, mn, pred); all = false; }
    }
    println!("  holds for all |j|<=60: {}", all);

    // ---- hunt a closed form: compare with the hex distance to the base-site set ----
    println!("\n[3b] closed form hunt: D = hex distance from (n,j) to {{(0,0),(-1,0),(-1,1)}}");
    let mut dd: HashMap<(i64,i64), i64> = HashMap::new();
    for s0 in [(0i64,0i64), (-1,0), (-1,1)] { dd.insert(s0, 0); }
    let mut fr: Vec<(i64,i64)> = vec![(0,0), (-1,0), (-1,1)];
    let mut dcur = 0i64;
    while !fr.is_empty() {
        dcur += 1;
        let mut nx = Vec::new();
        for &(n,j) in &fr {
            for &(dn,dj) in [(1i64,0i64),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)].iter() {
                let w = (n+dn, j+dj);
                if w.0.abs() > R || w.1.abs() > R { continue; }
                if !dd.contains_key(&w) { dd.insert(w, dcur); nx.push(w); }
            }
        }
        fr = nx;
    }
    let mut hist: HashMap<i64, i64> = HashMap::new();
    for j in -50..=50i64 { for n in -50..=50i64 {
        if let (Some(k), Some(&d0)) = (kk(n,j), dd.get(&(n,j))) { *hist.entry(k - 2*d0).or_insert(0) += 1; }
    }}
    let mut hv: Vec<_> = hist.into_iter().collect(); hv.sort();
    println!("  distribution of k - 2D over |n|,|j|<=50: {:?}", hv);
    // which sites give offset 0 vs -1 ?
    println!("  sample: (n,j) : k, D, k-2D");
    for &(n,j) in [(1i64,0i64),(0,1),(2,0),(1,1),(0,-1),(-2,0),(-1,2),(3,-2)].iter() {
        if let (Some(k), Some(&d0)) = (kk(n,j), dd.get(&(n,j))) {
            println!("    ({:3},{:3}) : k={:3}  D={:3}  k-2D={:3}", n, j, k, d0, k-2*d0);
        }
    }

    // ---- the epsilon grid ----
    println!("\n[3c] epsilon = 2D - k  on a window (rows j from +6 down to -6, n from -8 to 8)");
    print!("      n:");
    for n in -8..=8i64 { print!("{:3}", n); }
    println!();
    for j in (-6..=6i64).rev() {
        print!("  j={:3}:", j);
        for n in -8..=8i64 {
            if let (Some(k), Some(&d0)) = (kk(n,j), dd.get(&(n,j))) { print!("{:3}", 2*d0 - k); }
            else { print!("  ."); }
        }
        println!();
    }
    // test: is epsilon = 1 exactly when the site is "b-ward" of the base triangle?
    let eps = |n: i64, j: i64| -> Option<i64> {
        match (kk(n,j), dd.get(&(n,j))) { (Some(k), Some(&d0)) => Some(2*d0 - k), _ => None }
    };
    let mut bad = 0; let mut tot = 0;
    for j in -50..=50i64 { for n in -50..=50i64 {
        if let Some(e0) = eps(n,j) {
            tot += 1;
            // candidate rule: epsilon = 1 iff (n + 2j) mod 3 == 2   (to be judged by the count)
            let pred = if ((n + 2*j) % 3 + 3) % 3 == 2 { 1 } else { 0 };
            if e0 != pred { bad += 1; }
        }
    }}
    println!("  candidate (n+2j)%3==2 : {} mismatches out of {}", bad, tot);

    // ---- candidate closed form for k(n,j) ----
    println!("\n[3d] left branch of the negative rows, measured");
    for j in [-1i64,-2,-3,-4] {
        print!("  j={:3}: ", j);
        for n in -6..=1i64 { if let Some(v) = kk(n,j) { print!("n={:2}:{:3}  ", n, v); } }
        println!();
    }
    println!("\n[3e] candidate closed form, tested on |n|<=60, |j|<=60");
    let cand = |n: i64, j: i64| -> i64 {
        if j >= 1 {
            if n >= 0 { 2*n + 2*j - 1 } else if n >= -j { 2*j - 2 } else { -2*n - 3 }
        } else {
            // j <= -1 ; valley [0, -j-1] at value -2j-1
            if n >= -j { 2*n } else if n >= 0 { -2*j - 1 } else { -2*n - 2*j - 2 }
        }
    };
    let mut bad2 = 0; let mut tot2 = 0; let mut shown = 0;
    for j in -60..=60i64 { for n in -60..=60i64 {
        if let Some(k) = kk(n,j) { tot2 += 1;
            if k != cand(n,j) { bad2 += 1;
                if shown < 8 { println!("    MISMATCH (n,j)=({:3},{:3}) measured {:3} candidate {:3}", n, j, k, cand(n,j)); shown += 1; } } }
    }}
    println!("  mismatches: {} of {}", bad2, tot2);
    // the antipair bound, evaluated on the CLOSED FORM over a wide range
    let mut worst: Vec<(i64,i64)> = Vec::new();
    for h in 2..=60i64 {
        let mut best = i64::MAX;
        for j in -80..=80i64 { for n in -160..=160i64 {
            let m = cand(n,j).max(cand(n+h,j));
            if m < best { best = m; }
        }}
        if best != h-1 { worst.push((h,best)); }
    }
    println!("  closed-form antipair min over h=2..60, |j|<=80, |n|<=160: {}",
             if worst.is_empty() { "= h-1 in EVERY case".to_string() } else { format!("deviations {:?}", worst) });

    // ---- the antipair quantity ----
    println!("\n[4] cor:antipair  min_(n,j) max(k(n,j), k(n+h,j))  against h-1");
    for h in 2..=20i64 {
        let mut best = i64::MAX; let mut arg = (0i64, 0i64);
        for j in -40..=40i64 {
            for n in -70..=70i64 {
                if let (Some(x), Some(y)) = (kk(n, j), kk(n + h, j)) {
                    let m = x.max(y);
                    if m < best { best = m; arg = (n, j); }
                }
            }
        }
        println!("  h={:2}: min max = {:3}  (h-1 = {:3})  {}   attained at (n,j)={:?}",
                 h, best, h - 1, if best == h - 1 { "OK" } else { "DIFFERS" }, arg);
    }
}
