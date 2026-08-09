// pkernel: p-kernel census of a mod-p sequence, with an explicit support threshold.
//
// The p-kernel of (u_n mod p) is the set of distinct subsequences n -> u_{p^k n + r},
// k >= 0, 0 <= r < p^k.  By Eilenberg's theorem the sequence is p-automatic iff this set
// is finite, so kernel growth is the automaticity obstruction.
//
// HONESTY ABOUT TRUNCATION.  With only N+1 terms available, the subsequence (k, r) is
// defined at n = 0 .. floor((N-r)/p^k), so deep classes are compared on very few terms and
// can appear equal purely for lack of evidence.  Every count below is therefore reported
// together with MINSUP, the least number of terms any compared class had.  A count is
// trustworthy only while MINSUP is comfortably large; a collapse seen at MINSUP = 2 is not
// evidence of a collapse.  Distinctness is monotone in evidence: two classes found DISTINCT
// stay distinct as N grows, so the counts are lower bounds.  Coincidences are the fragile
// direction, so any reported deficit from the full tree is flagged with its witness.
//
// Usage: pkernel <file> <p> <maxdepth> [minsup]

use std::collections::HashMap;
use std::env;
use std::fs;

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() < 4 { eprintln!("usage: pkernel <file> <p> <maxdepth> [minsup]"); std::process::exit(1); }
    let txt = fs::read_to_string(&a[1]).expect("read");
    let u: Vec<i64> = txt.split_whitespace().filter_map(|s| s.parse().ok()).collect();
    let p: usize = a[2].parse().unwrap();
    let maxd: usize = a[3].parse().unwrap();
    let minsup: usize = if a.len() > 4 { a[4].parse().unwrap() } else { 4 };
    let n = u.len();
    println!("terms: {}   p = {}   max depth = {}   support threshold = {}", n, p, maxd, minsup);

    // A class is keyed by its value vector, truncated to a COMMON length so that classes at
    // the same depth are compared on the same evidence.
    let mut seen: HashMap<Vec<i64>, (usize, usize)> = HashMap::new(); // key -> (depth, r)
    let mut cumulative = 0usize;
    let mut pk = 1usize;

    for k in 0..=maxd {
        // common support at this depth: every r in 0..pk must supply this many terms
        let common = (0..pk).map(|r| if n > r { (n - r + pk - 1) / pk } else { 0 }).min().unwrap_or(0);
        if common < minsup {
            println!("depth {:2}: SKIPPED, common support {} < threshold {} (need N >= about {})",
                     k, common, minsup, pk * minsup);
            pk = pk.saturating_mul(p);
            continue;
        }
        let mut fresh = 0usize;
        let mut dup_witness: Vec<(usize, usize, usize, usize)> = Vec::new();
        for r in 0..pk {
            let key: Vec<i64> = (0..common).map(|i| u[i * pk + r]).collect();
            match seen.get(&key) {
                None => { seen.insert(key, (k, r)); fresh += 1; }
                Some(&(dk, dr)) => { if dup_witness.len() < 6 { dup_witness.push((k, r, dk, dr)); } }
            }
        }
        cumulative += fresh;
        let full = if k == 0 { 1 } else { pk };
        print!("depth {:2}: classes at this depth {:4} of {:4} possible, fresh {:4}, cumulative {:5}, support {:4}",
               k, pk - dup_witness.len().min(pk), full, fresh, cumulative, common);
        if !dup_witness.is_empty() {
            print!("   DEFICIT {}", dup_witness.len());
        }
        println!();
        for (k1, r1, k2, r2) in &dup_witness {
            println!("        collapse: (k={}, r={}) equals earlier (k={}, r={}) on {} terms",
                     k1, r1, k2, r2, common);
        }
        pk = pk.saturating_mul(p);
    }
    println!("\nCumulative kernel size seen: {}", cumulative);
    println!("NOTE: counts are LOWER bounds; collapses at small support are not evidence.");
}
