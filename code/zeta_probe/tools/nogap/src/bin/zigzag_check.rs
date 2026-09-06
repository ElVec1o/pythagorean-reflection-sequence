// zigzag_check -- falsify-or-confirm the "zigzag turn" construction on a linear
// chain of sites 0..L with m_j (even, > 0) parallel strands on edge j.
//
// A turn is a fixed-point-free involution on strand ends that only pairs ends at
// the SAME site.  Pairing two ends of the same edge is a BOUNCE, pairing an end of
// edge j-1 with an end of edge j is a PASS.  `hturn`: at a cut site (set Z, plus
// the two chain ends 0 and L) no pass is allowed -- everything bounces there.
// A "run" is a maximal stretch of consecutive edges between cut sites.  The design
// question: does the zigzag put every run's strands into ONE closed walk?
//
// Component counting is done TWICE by independent methods (union-find on strands,
// and explicit walk tracing over ends) and the two are asserted equal, so a bug in
// one does not produce a false verdict.  A third, exhaustive, matching enumerator
// checks small cases against brute force.
//
// Self-contained, matching this tool directory's convention of one file per
// question.  No dependencies, no large frontier structures.

// ---------------------------------------------------------------- edge wirings

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Wiring {
    /// plain zigzag with the two loose ends at the LEFT site
    ZigLeft,
    /// plain zigzag with the two loose ends at the RIGHT site
    ZigRight,
    /// strand 0 straight through + zigzag on strands 1..m-1;
    /// two loose ends on each side  (the repaired convention)
    Through2,
    /// no loose ends at all: left matching (2i,2i+1), right matching (2i+1,2i+2 mod m)
    Closed,
}

struct EdgeWire {
    lb: Vec<(usize, usize)>, // local strand pairs bounced at the LEFT site
    rb: Vec<(usize, usize)>, // local strand pairs bounced at the RIGHT site
    ll: Vec<usize>,          // local strands with a loose LEFT end
    lr: Vec<usize>,          // local strands with a loose RIGHT end
}

fn wire(w: Wiring, m: usize) -> EdgeWire {
    assert!(m >= 2 && m % 2 == 0);
    let h = m / 2;
    match w {
        Wiring::ZigLeft => EdgeWire {
            rb: (0..h).map(|i| (2 * i, 2 * i + 1)).collect(),
            lb: (0..h.saturating_sub(1)).map(|i| (2 * i + 1, 2 * i + 2)).collect(),
            ll: vec![0, m - 1],
            lr: vec![],
        },
        Wiring::ZigRight => EdgeWire {
            lb: (0..h).map(|i| (2 * i, 2 * i + 1)).collect(),
            rb: (0..h.saturating_sub(1)).map(|i| (2 * i + 1, 2 * i + 2)).collect(),
            ll: vec![],
            lr: vec![0, m - 1],
        },
        Wiring::Through2 => EdgeWire {
            lb: (1..h).map(|i| (2 * i, 2 * i + 1)).collect(),
            rb: (0..h.saturating_sub(1)).map(|i| (2 * i + 1, 2 * i + 2)).collect(),
            ll: vec![0, 1],
            lr: vec![0, m - 1],
        },
        Wiring::Closed => EdgeWire {
            lb: (0..h).map(|i| (2 * i, 2 * i + 1)).collect(),
            rb: (0..h).map(|i| (2 * i + 1, (2 * i + 2) % m)).collect(),
            ll: vec![],
            lr: vec![],
        },
    }
}

// ---------------------------------------------------------------- the chain

struct Chain {
    m: Vec<usize>,
    off: Vec<usize>,    // off[j] = first global strand index of edge j
    cut: Vec<bool>,     // per site 0..=L; sites 0 and L are always cut
    strand_edge: Vec<usize>,
}

impl Chain {
    fn new(m: &[usize], interior_cuts: &[bool]) -> Chain {
        let l = m.len();
        assert_eq!(interior_cuts.len(), l.saturating_sub(1));
        let mut off = vec![0usize; l + 1];
        for j in 0..l {
            off[j + 1] = off[j] + m[j];
        }
        let mut cut = vec![false; l + 1];
        cut[0] = true;
        cut[l] = true;
        for s in 1..l {
            cut[s] = interior_cuts[s - 1];
        }
        let mut strand_edge = vec![0usize; off[l]];
        for j in 0..l {
            for k in off[j]..off[j + 1] {
                strand_edge[k] = j;
            }
        }
        Chain { m: m.to_vec(), off, cut, strand_edge }
    }
    fn l(&self) -> usize { self.m.len() }
    fn nstrands(&self) -> usize { self.off[self.l()] }
    fn nends(&self) -> usize { 2 * self.nstrands() }
    fn site_of_end(&self, e: usize) -> usize {
        let s = e / 2;
        let j = self.strand_edge[s];
        if e % 2 == 0 { j } else { j + 1 }
    }
    /// runs as (a, b) inclusive edge ranges between cut sites
    fn runs(&self) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        let mut a = 0usize;
        for s in 1..=self.l() {
            if self.cut[s] {
                out.push((a, s - 1));
                a = s;
            }
        }
        out
    }
}

// ---------------------------------------------------------------- turn builder

/// Build the turn from a per-edge wiring choice.  Loose ends left over at a site
/// are passed across when the site is not cut (as many as possible, pairwise) and
/// otherwise bounced back within their own edge.
fn build_turn(ch: &Chain, wirings: &[Wiring], cross_pass: bool) -> Vec<usize> {
    let l = ch.l();
    let mut partner = vec![usize::MAX; ch.nends()];
    // per site: loose ends contributed by the edge on the left / on the right
    let mut from_left: Vec<Vec<usize>> = vec![Vec::new(); l + 1];
    let mut from_right: Vec<Vec<usize>> = vec![Vec::new(); l + 1];

    for j in 0..l {
        let w = wire(wirings[j], ch.m[j]);
        let base = ch.off[j];
        for &(a, b) in &w.lb {
            let (ea, eb) = (2 * (base + a), 2 * (base + b));
            partner[ea] = eb;
            partner[eb] = ea;
        }
        for &(a, b) in &w.rb {
            let (ea, eb) = (2 * (base + a) + 1, 2 * (base + b) + 1);
            partner[ea] = eb;
            partner[eb] = ea;
        }
        for &a in &w.ll {
            from_right[j].push(2 * (base + a));
        }
        for &a in &w.lr {
            from_left[j + 1].push(2 * (base + a) + 1);
        }
    }

    for s in 0..=l {
        let a = &from_left[s];   // loose right-ends of edge s-1
        let b = &from_right[s];  // loose left-ends of edge s
        let (mut ra, mut rb): (Vec<usize>, Vec<usize>) = (a.clone(), b.clone());
        if !ch.cut[s] {
            let k = ra.len().min(rb.len());
            let k = k - (k % 2); // passes come in pairs (parity of even m)
            for i in 0..k {
                let x = ra[i];
                let y = if cross_pass { rb[k - 1 - i] } else { rb[i] };
                partner[x] = y;
                partner[y] = x;
            }
            // both pairings consume rb[0..k]; only the bijection differs
            ra = ra[k..].to_vec();
            rb = rb[k..].to_vec();
        }
        // leftovers bounce within their own edge
        for grp in [&ra, &rb] {
            assert!(grp.len() % 2 == 0, "odd leftover group at site {}", s);
            for c in grp.chunks(2) {
                partner[c[0]] = c[1];
                partner[c[1]] = c[0];
            }
        }
    }
    partner
}

// ---------------------------------------------------------------- validation

fn validate_turn(ch: &Chain, p: &[usize]) -> Result<(), String> {
    for e in 0..ch.nends() {
        let q = p[e];
        if q == usize::MAX { return Err(format!("end {} unpaired", e)); }
        if q == e { return Err(format!("end {} is a fixed point", e)); }
        if p[q] != e { return Err(format!("not an involution at {}", e)); }
        if ch.site_of_end(e) != ch.site_of_end(q) {
            return Err(format!("pair ({},{}) spans two sites", e, q));
        }
    }
    // hturn: no pass at a cut site
    for e in 0..ch.nends() {
        let q = p[e];
        let (je, jq) = (ch.strand_edge[e / 2], ch.strand_edge[q / 2]);
        if je != jq {
            let s = ch.site_of_end(e);
            if ch.cut[s] {
                return Err(format!("PASS at cut site {} (ends {},{})", s, e, q));
            }
        }
    }
    Ok(())
}

// component count #1: union-find over strands
fn uf_find(f: &mut Vec<usize>, x: usize) -> usize {
    let mut r = x;
    while f[r] != r { r = f[r]; }
    let mut c = x;
    while f[c] != c { let n = f[c]; f[c] = r; c = n; }
    r
}

fn components_uf(ch: &Chain, p: &[usize]) -> (usize, Vec<usize>) {
    let n = ch.nstrands();
    let mut f: Vec<usize> = (0..n).collect();
    for e in 0..ch.nends() {
        let q = p[e];
        let (a, b) = (e / 2, q / 2);
        let (ra, rb) = (uf_find(&mut f, a), uf_find(&mut f, b));
        if ra != rb { f[ra] = rb; }
    }
    let roots: Vec<usize> = (0..n).map(|x| uf_find(&mut f, x)).collect();
    let mut seen: Vec<usize> = roots.clone();
    seen.sort_unstable();
    seen.dedup();
    (seen.len(), roots)
}

// component count #2: explicit walk tracing over ends
fn components_walk(ch: &Chain, p: &[usize]) -> usize {
    let n = ch.nends();
    let mut vis = vec![false; n];
    let mut cyc = 0usize;
    for start in 0..n {
        if vis[start] { continue; }
        cyc += 1;
        let mut e = start;
        loop {
            vis[e] = true;
            let other = e ^ 1; // the far end of the same strand
            vis[other] = true;
            e = p[other];
            if e == start { break; }
            assert!(!vis[e], "walk re-entered a visited end -- turn is not an involution");
        }
    }
    cyc
}

fn count_components(ch: &Chain, p: &[usize]) -> usize {
    let (c1, _) = components_uf(ch, p);
    let c2 = components_walk(ch, p);
    assert_eq!(c1, c2, "union-find and walk tracing disagree");
    c1
}

/// per-run connectivity: every run's strands in exactly one component,
/// and the total number of components equals the number of runs.
fn per_run_ok(ch: &Chain, p: &[usize]) -> bool {
    let (nc, roots) = components_uf(ch, p);
    let runs = ch.runs();
    if nc != runs.len() { return false; }
    for &(a, b) in &runs {
        let r0 = roots[ch.off[a]];
        for k in ch.off[a]..ch.off[b + 1] {
            if roots[k] != r0 { return false; }
        }
    }
    true
}

// ---------------------------------------------------------------- variants

#[derive(Clone, Copy)]
struct Variant { name: &'static str, cross: bool, kind: u8 }

fn wirings_for(v: Variant, ch: &Chain) -> Vec<Wiring> {
    let l = ch.l();
    match v.kind {
        0 => vec![Wiring::ZigLeft; l],
        1 => vec![Wiring::ZigRight; l],
        2 => (0..l).map(|j| if j % 2 == 0 { Wiring::ZigLeft } else { Wiring::ZigRight }).collect(),
        3 => {
            // run-aware: single-edge runs Closed, else ZigRight | Through2* | ZigLeft
            let mut w = vec![Wiring::Closed; l];
            for (a, b) in ch.runs() {
                if a == b { w[a] = Wiring::Closed; }
                else {
                    w[a] = Wiring::ZigRight;
                    w[b] = Wiring::ZigLeft;
                    for j in a + 1..b { w[j] = Wiring::Through2; }
                }
            }
            w
        }
        4 => vec![Wiring::Through2; l],
        _ => unreachable!(),
    }
}

const VARIANTS: [Variant; 6] = [
    Variant { name: "V1 plain zigzag, loose ends LEFT ", cross: false, kind: 0 },
    Variant { name: "V2 plain zigzag, loose ends RIGHT", cross: false, kind: 1 },
    Variant { name: "V3 zigzag alternating by edge par", cross: false, kind: 2 },
    Variant { name: "V4 run-aware Closed/Zig/Through2 ", cross: false, kind: 3 },
    Variant { name: "V5 uniform Through2 (parallel)   ", cross: false, kind: 4 },
    Variant { name: "V6 uniform Through2 (crossed)    ", cross: true,  kind: 4 },
];

// ---------------------------------------------------------------- brute force

/// all perfect matchings of `ends`, restricted so that a pair is allowed only if
/// `allow(a,b)` holds.  Returns at most `cap` matchings.
fn all_matchings<F: Fn(usize, usize) -> bool>(
    ends: &[usize], allow: &F, out: &mut Vec<Vec<(usize, usize)>>, cur: &mut Vec<(usize, usize)>,
    used: &mut Vec<bool>, cap: usize,
) {
    if out.len() >= cap { return; }
    let first = (0..ends.len()).find(|&i| !used[i]);
    let i = match first { None => { out.push(cur.clone()); return; } Some(i) => i };
    used[i] = true;
    for j in i + 1..ends.len() {
        if used[j] || !allow(ends[i], ends[j]) { continue; }
        used[j] = true;
        cur.push((ends[i], ends[j]));
        all_matchings(ends, allow, out, cur, used, cap);
        cur.pop();
        used[j] = false;
        if out.len() >= cap { break; }
    }
    used[i] = false;
}

/// exhaustive: how many hturn-legal turns give per-run connectivity?
fn brute(ch: &Chain, cap: usize) -> Option<(u64, u64)> {
    let l = ch.l();
    let mut per_site: Vec<Vec<Vec<(usize, usize)>>> = Vec::new();
    let mut prod: u128 = 1;
    for s in 0..=l {
        let mut ends: Vec<usize> = Vec::new();
        if s >= 1 { for k in ch.off[s - 1]..ch.off[s] { ends.push(2 * k + 1); } }
        if s < l { for k in ch.off[s]..ch.off[s + 1] { ends.push(2 * k); } }
        let cut = ch.cut[s];
        let se = &ch.strand_edge;
        let allow = |a: usize, b: usize| !cut || se[a / 2] == se[b / 2];
        let mut out = Vec::new();
        let mut cur = Vec::new();
        let mut used = vec![false; ends.len()];
        all_matchings(&ends, &allow, &mut out, &mut cur, &mut used, cap);
        if out.len() >= cap { return None; }
        prod *= out.len() as u128;
        if prod > cap as u128 { return None; }
        per_site.push(out);
    }
    let mut partner = vec![usize::MAX; ch.nends()];
    let mut total = 0u64;
    let mut good = 0u64;
    fn rec(
        ch: &Chain, per_site: &[Vec<Vec<(usize, usize)>>], s: usize,
        partner: &mut Vec<usize>, total: &mut u64, good: &mut u64,
    ) {
        if s == per_site.len() {
            *total += 1;
            let _ = count_components(ch, partner); // cross-check both methods
            if per_run_ok(ch, partner) { *good += 1; }
            return;
        }
        for mt in &per_site[s] {
            for &(a, b) in mt { partner[a] = b; partner[b] = a; }
            rec(ch, per_site, s + 1, partner, total, good);
        }
    }
    rec(ch, &per_site, 0, &mut partner, &mut total, &mut good);
    Some((total, good))
}

// ---------------------------------------------------------------- sweep

fn main() {
    let ms = [2usize, 4, 6];
    println!("== sweep: m in {{2,4,6}}, L = 1..5, all interior cut-sets ==\n");

    let mut tot = 0u64;
    let mut pass = vec![0u64; VARIANTS.len()];
    let mut first_bad: Vec<Option<(Vec<usize>, Vec<usize>, usize, usize)>> =
        vec![None; VARIANTS.len()];

    for l in 1..=5usize {
        let nvec = ms.len().pow(l as u32);
        for vi in 0..nvec {
            let mut m = Vec::with_capacity(l);
            let mut t = vi;
            for _ in 0..l { m.push(ms[t % ms.len()]); t /= ms.len(); }
            for zmask in 0..(1usize << l.saturating_sub(1)) {
                let cuts: Vec<bool> = (0..l.saturating_sub(1))
                    .map(|i| (zmask >> i) & 1 == 1).collect();
                let ch = Chain::new(&m, &cuts);
                tot += 1;
                for (k, v) in VARIANTS.iter().enumerate() {
                    let w = wirings_for(*v, &ch);
                    let p = build_turn(&ch, &w, v.cross);
                    if let Err(e) = validate_turn(&ch, &p) {
                        panic!("variant {} produced an illegal turn: {}", v.name, e);
                    }
                    let nc = count_components(&ch, &p);
                    if per_run_ok(&ch, &p) { pass[k] += 1; }
                    else if first_bad[k].is_none() {
                        let z: Vec<usize> = (1..l).filter(|&s| ch.cut[s]).collect();
                        first_bad[k] = Some((m.clone(), z, nc, ch.runs().len()));
                    }
                }
            }
        }
    }

    println!("configurations tested: {}\n", tot);
    println!("{:<34} {:>8} {:>8}  first counterexample", "variant", "pass", "fail");
    for (k, v) in VARIANTS.iter().enumerate() {
        let f = tot - pass[k];
        let ce = match &first_bad[k] {
            None => "-- none --".to_string(),
            Some((m, z, nc, nr)) =>
                format!("m={:?} Z={:?}  components={} runs={}", m, z, nc, nr),
        };
        println!("{:<34} {:>8} {:>8}  {}", v.name, pass[k], f, ce);
    }

    // ---- where exactly does the plain zigzag fail? ----
    println!("\n== V1 (plain zigzag) pass rate split by max run length ==");
    for maxrun in 1..=5usize {
        let (mut a, mut b) = (0u64, 0u64);
        for l in 1..=5usize {
            let nvec = ms.len().pow(l as u32);
            for vi in 0..nvec {
                let mut m = Vec::with_capacity(l);
                let mut t = vi;
                for _ in 0..l { m.push(ms[t % ms.len()]); t /= ms.len(); }
                for zmask in 0..(1usize << l.saturating_sub(1)) {
                    let cuts: Vec<bool> = (0..l.saturating_sub(1))
                        .map(|i| (zmask >> i) & 1 == 1).collect();
                    let ch = Chain::new(&m, &cuts);
                    let mr = ch.runs().iter().map(|&(x, y)| y - x + 1).max().unwrap();
                    if mr != maxrun { continue; }
                    a += 1;
                    let w = wirings_for(VARIANTS[0], &ch);
                    let p = build_turn(&ch, &w, false);
                    if per_run_ok(&ch, &p) { b += 1; }
                }
            }
        }
        if a > 0 { println!("  max run length {}: {} / {} pass", maxrun, b, a); }
    }

    // ---- degenerate / boundary cases, spelled out ----
    println!("\n== degenerate cases (V5 uniform Through2) ==");
    let cases: Vec<(Vec<usize>, Vec<bool>)> = vec![
        (vec![2], vec![]),
        (vec![4], vec![]),
        (vec![6], vec![]),
        (vec![2, 2], vec![false]),
        (vec![2, 2], vec![true]),
        (vec![2, 2, 2], vec![false, false]),
        (vec![6, 2, 6], vec![false, false]),
        (vec![2, 4, 6, 4, 2], vec![false, false, false, false]),
        (vec![2, 4, 6, 4, 2], vec![false, true, false, false]),
        (vec![6, 6, 6, 6, 6], vec![true, false, true, false]),
    ];
    for (m, cuts) in &cases {
        let ch = Chain::new(m, cuts);
        let w = wirings_for(VARIANTS[4], &ch);
        let p = build_turn(&ch, &w, false);
        validate_turn(&ch, &p).expect("illegal turn");
        let nc = count_components(&ch, &p);
        let runs = ch.runs();
        println!("  m={:?} runs={:?} -> components={} per-run-ok={}",
                 m, runs, nc, per_run_ok(&ch, &p));
    }

    // ---- all-m=2 sanity (the project's existing special case) ----
    {
        let mut n = 0u64;
        let mut ok = 0u64;
        for l in 1..=7usize {
            for zmask in 0..(1usize << l.saturating_sub(1)) {
                let cuts: Vec<bool> = (0..l.saturating_sub(1))
                    .map(|i| (zmask >> i) & 1 == 1).collect();
                let ch = Chain::new(&vec![2usize; l], &cuts);
                let w = wirings_for(VARIANTS[4], &ch);
                let p = build_turn(&ch, &w, false);
                n += 1;
                if per_run_ok(&ch, &p) { ok += 1; }
            }
        }
        println!("\n== m_j = 2 everywhere, L = 1..7, all cut-sets: {} / {} pass (V5) ==", ok, n);
    }

    // ---- stress: larger L, larger m, still exhaustive over cut-sets ----
    {
        let ms2 = [2usize, 4, 6, 8];
        let (mut n, mut ok) = (0u64, 0u64);
        let mut bad: Option<(Vec<usize>, Vec<usize>)> = None;
        for l in 1..=6usize {
            let nvec = ms2.len().pow(l as u32);
            for vi in 0..nvec {
                let mut m = Vec::with_capacity(l);
                let mut t = vi;
                for _ in 0..l { m.push(ms2[t % ms2.len()]); t /= ms2.len(); }
                for zmask in 0..(1usize << l.saturating_sub(1)) {
                    let cuts: Vec<bool> = (0..l.saturating_sub(1))
                        .map(|i| (zmask >> i) & 1 == 1).collect();
                    let ch = Chain::new(&m, &cuts);
                    let w = wirings_for(VARIANTS[4], &ch);
                    let p = build_turn(&ch, &w, false);
                    validate_turn(&ch, &p).expect("illegal turn");
                    let _ = count_components(&ch, &p);
                    n += 1;
                    if per_run_ok(&ch, &p) { ok += 1; }
                    else if bad.is_none() {
                        let z: Vec<usize> = (1..l).filter(|&s| ch.cut[s]).collect();
                        bad = Some((m.clone(), z));
                    }
                }
            }
        }
        println!("\n== stress V5: m in {{2,4,6,8}}, L = 1..6, all cut-sets: {} / {} pass ==", ok, n);
        if let Some((m, z)) = bad { println!("   first failure m={:?} Z={:?}", m, z); }
    }
    {
        // wide edges and a long chain
        let m: Vec<usize> = (0..12).map(|i| 2 + 2 * (i % 20)).collect();
        for zmask in [0usize, 0b010101010101, 0b111111111111, 0b100000000001] {
            let cuts: Vec<bool> = (0..m.len() - 1).map(|i| (zmask >> i) & 1 == 1).collect();
            let ch = Chain::new(&m, &cuts);
            let w = wirings_for(VARIANTS[4], &ch);
            let p = build_turn(&ch, &w, false);
            validate_turn(&ch, &p).expect("illegal turn");
            println!("   L=12 strands={} runs={} components={} ok={}",
                     ch.nstrands(), ch.runs().len(), count_components(&ch, &p),
                     per_run_ok(&ch, &p));
        }
    }

    // ---- exhaustive cross-check on small cases ----
    println!("\n== brute force: hturn-legal turns achieving per-run connectivity ==");
    let mut bf_cases = 0u64;
    let mut bf_nonzero = 0u64;
    for l in 1..=3usize {
        for vi in 0..2usize.pow(l as u32) {
            let mut m = Vec::with_capacity(l);
            let mut t = vi;
            for _ in 0..l { m.push([2usize, 4][t % 2]); t /= 2; }
            for zmask in 0..(1usize << l.saturating_sub(1)) {
                let cuts: Vec<bool> = (0..l.saturating_sub(1))
                    .map(|i| (zmask >> i) & 1 == 1).collect();
                let ch = Chain::new(&m, &cuts);
                match brute(&ch, 400_000) {
                    None => println!("  m={:?} cuts={:?}: skipped (too many turns)", m, cuts),
                    Some((total, good)) => {
                        bf_cases += 1;
                        if good > 0 { bf_nonzero += 1; }
                        let z: Vec<usize> = (1..l).filter(|&s| ch.cut[s]).collect();
                        println!("  m={:?} Z={:?}: {} / {} legal turns give per-run connectivity",
                                 m, z, good, total);
                    }
                }
            }
        }
    }
    println!("  brute-forced {} configurations, {} admit at least one good turn",
             bf_cases, bf_nonzero);
}
