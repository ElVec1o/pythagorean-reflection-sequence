// reach_check -- does the deposit engine (s1/s2/s3, as generators of Elt) accumulate
// magnitude at a FIXED cursor position?  Rule 3 falsification for the H1a crux logged
// 2026-09-05: two applications of `reachable_deposit_step` at fixed kstar cancel
// exactly, so it is not obvious the group can reach kstar=0, d(0)=2k for k>1 without
// visiting other positions.  BFS from `one`, record word length to every element
// reached by depth, then look up the targets directly.
//
// Same generator rules as ../src/main.rs's nogap BFS (Elt = eps, delta, kstar, sparse
// deposits), duplicated standalone here rather than shared, matching this tool
// directory's existing convention of one self-contained main.rs per question.

use std::collections::HashMap;
use std::io::Write;
use std::time::Instant;

type Lamps = Vec<(i32, i32)>;
#[derive(Clone, PartialEq, Eq, Hash)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }

fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}

fn target(k: i32, val: i32) -> Elt {
    let lamps: Lamps = if val == 0 { vec![] } else { vec![(k, val)] };
    Elt { eps: 1, dl: 0, k: 0, lamps }
}

// generator labels, matching EltBridge.lean: s1 toggles delta, s2 toggles delta AND
// flips eps, s3 moves the cursor and deposits (branch depends on delta).
fn gens(e: &Elt) -> [(&'static str, Elt); 3] {
    let s1 = Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() };
    let s2 = Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() };
    let s3 = if e.dl == 0 {
        Elt { eps: e.eps, dl: 1, k: e.k - 1,
              lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) }
    } else {
        Elt { eps: e.eps, dl: 0, k: e.k + 1,
              lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) }
    };
    [("s1", s1), ("s2", s2), ("s3", s3)]
}

fn main() {
    let depth: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(16);
    eprintln!("[reach_check] BFS to depth {depth} from `one`");

    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    let mut dist: HashMap<Elt, u32> = HashMap::new();
    let mut parent: HashMap<Elt, (Elt, &'static str)> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    let t0 = Instant::now();

    for d in 0..depth {
        let mut next = Vec::new();
        for e in &frontier {
            for (label, c) in gens(e) {
                if !dist.contains_key(&c) {
                    dist.insert(c.clone(), d + 1);
                    parent.insert(c.clone(), (e.clone(), label));
                    next.push(c);
                }
            }
        }
        frontier = next;
        let el = t0.elapsed().as_secs_f64();
        eprintln!("[reach_check] layer {:2}/{}: frontier {:>9}  total {:>10}  {:6.1}s",
                  d + 1, depth, frontier.len(), dist.len(), el);
        std::io::stderr().flush().ok();
    }

    println!("[reach_check] depth {depth}, {} elements enumerated", dist.len());
    println!("[reach_check] checking kstar=0, d(0)=2k, else matching `one` (eps=1,delta=false):");
    for k in 0..=6 {
        let t = target(0, 2 * k);
        match dist.get(&t) {
            Some(&len) if len < depth => println!("  d(0)={:>3}: REACHABLE, word length {}", 2 * k, len),
            Some(&len) => println!("  d(0)={:>3}: seen at frontier depth {} (== search bound; may be incomplete)", 2 * k, len),
            None => println!("  d(0)={:>3}: NOT FOUND within depth {}", 2 * k, depth),
        }
    }
    // also check the odd/negative and the k != 0 sibling family (near kstar - 1, matching
    // the deposit engine's actual touched position, delta=false).
    println!("[reach_check] checking kstar=0, d(-1)=2k, else matching `one`:");
    for k in 0..=6 {
        let t = target(-1, 2 * k);
        match dist.get(&t) {
            Some(&len) if len < depth => println!("  d(-1)={:>3}: REACHABLE, word length {}", 2 * k, len),
            Some(&len) => println!("  d(-1)={:>3}: seen at frontier depth {} (== search bound; may be incomplete)", 2 * k, len),
            None => println!("  d(-1)={:>3}: NOT FOUND within depth {}", 2 * k, depth),
        }
    }

    // reconstruct the actual witnessing word for d(0) = 2 and d(0) = 4, to see the
    // real construction (not the naive repeated-roundtrip guess, which cancels).
    for k in [1i32, 2] {
        let t = target(0, 2 * k);
        if let Some(&len) = dist.get(&t) {
            if len >= depth { continue; }
            let mut word = Vec::new();
            let mut cur = t.clone();
            while let Some((p, label)) = parent.get(&cur) {
                word.push(label);
                cur = p.clone();
            }
            word.reverse();
            println!("[reach_check] witness word for d(0)={} (length {}): {:?}", 2 * k, len, word);
        }
    }
}
