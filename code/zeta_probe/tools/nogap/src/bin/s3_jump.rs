// s3_jump -- isolate the max |dPhi| caused by s3 ALONE, on the correct (nogapBS)
// potential.  Prior blocks measured the combined max over all three generators;
// this checks s3 specifically before committing to a Lean proof strategy for it.

use std::collections::HashMap;

type Lamps = Vec<(i32, i32)>;
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Elt { eps: i8, dl: u8, k: i32, lamps: Lamps }

#[inline]
fn travel(k: i32, j: i32) -> i32 {
    if 0 <= j && j < k { 1 } else if k <= j && j < 0 { -1 } else { 0 }
}
#[inline]
fn dep(l: &Lamps, j: i32) -> i32 {
    match l.binary_search_by_key(&j, |&(x, _)| x) { Ok(i) => l[i].1, Err(_) => 0 }
}
fn span_nogap(e: &Elt) -> (i32, i32) {
    let (mut lo, mut hi) = (0.min(e.k), 0.max(e.k));
    for &(j, v) in &e.lamps { if v != 0 { lo = lo.min(j); hi = hi.max(j + 1); } }
    if e.k > 0 { lo = lo.min(0); hi = hi.max(e.k); }
    if e.k < 0 { lo = lo.min(e.k); hi = hi.max(0); }
    (lo, hi - 1)
}
fn abphi(e: &Elt, s: i32) -> (i32, i32, i32) {
    let varr = if s == 0 { 1 } else { 0 };
    let vd = if s == e.k { 1 } else { 0 };
    let (vl, vr) = if e.dl == 0 { (vd, 0) } else { (0, vd) };
    let eps = e.eps as i32;
    (dep(&e.lamps, s - 1) - varr + eps * vl, dep(&e.lamps, s) - eps * vr, 0)
}
fn mu(e: &Elt, j: i32) -> i64 {
    let (d, f) = (dep(&e.lamps, j), travel(e.k, j));
    if d == 0 && f == 0 { 2 } else { d.abs().max(f.abs()) as i64 }
}
fn lr_on(e: &Elt, a: i32, b: i32) -> i64 {
    let mut t = 0i64;
    for j in a..=b { t += mu(e, j); }
    for s in a..=b + 1 {
        let (al, be, _) = abphi(e, s);
        t += al.abs().max(be.abs()) as i64;
    }
    t
}
fn is_cut(e: &Elt, s: i32) -> bool { let (a, b, _) = abphi(e, s); a == 0 && b == 0 }
fn cuts_on(e: &Elt, a: i32, b: i32) -> i64 {
    let mut n = 0i64;
    for s in a + 1..b + 1 { if is_cut(e, s) { n += 1; } }
    if e.k == 0 && e.dl == 0 && a == 0 && b + 1 > 0 && is_cut(e, 0) { n += 1; }
    n
}
fn phi(e: &Elt) -> i64 {
    let (a, b) = span_nogap(e);
    lr_on(e, a, b) + 2 * cuts_on(e, a, b)
}
fn set_lamp(l: &Lamps, j: i32, delta: i32) -> Lamps {
    let mut out = l.clone();
    match out.binary_search_by_key(&j, |&(x, _)| x) {
        Ok(i) => { out[i].1 += delta; if out[i].1 == 0 { out.remove(i); } }
        Err(i) => { if delta != 0 { out.insert(i, (j, delta)); } }
    }
    out
}
fn s3(e: &Elt) -> Elt {
    if e.dl == 0 {
        Elt { eps: e.eps, dl: 1, k: e.k - 1, lamps: set_lamp(&e.lamps, e.k - 1, e.eps as i32) }
    } else {
        Elt { eps: e.eps, dl: 0, k: e.k + 1, lamps: set_lamp(&e.lamps, e.k, -(e.eps as i32)) }
    }
}
fn gens_all(e: &Elt) -> [Elt; 3] {
    [Elt { eps: e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     Elt { eps: -e.eps, dl: 1 - e.dl, k: e.k, lamps: e.lamps.clone() },
     s3(e)]
}
fn size(e: &Elt) -> i64 { e.k.abs() as i64 + e.lamps.iter().map(|&(_, v)| v.abs() as i64).sum::<i64>() }
fn show(e: &Elt) -> String {
    format!("k={} eps={} delta={} d={:?}", e.k, e.eps, if e.dl == 0 { "false" } else { "true" }, e.lamps)
}

fn main() {
    probe_empty_occ(); probe_empty_occ_s3g();
    let depth: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(20);
    let cap: usize = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(6_000_000);

    let ident = Elt { eps: 1, dl: 0, k: 0, lamps: vec![] };
    let mut dist: HashMap<Elt, u8> = HashMap::new();
    dist.insert(ident.clone(), 0);
    let mut frontier = vec![ident];
    for d in 0..depth {
        let mut next = Vec::new();
        for e in &frontier {
            for c in gens_all(e) {
                if !dist.contains_key(&c) { dist.insert(c.clone(), (d + 1) as u8); next.push(c); }
            }
        }
        frontier = next;
        if dist.len() > cap { eprintln!("[s3] cap hit at depth {}", d + 1); break; }
    }
    eprintln!("[s3] enumerated {} elements", dist.len());
    let mut ub_violations = 0u64;
    let mut ub_checked = 0u64;
    let mut ub_witness: Option<(Elt, u8, i64)> = None;
    for (e, &wl) in dist.iter() {
        let ph = phi(e);
        ub_checked += 1;
        if (wl as i64) > ph {
            ub_violations += 1;
            if ub_witness.is_none() { ub_witness = Some((e.clone(), wl, ph)); }
        }
    }
    eprintln!("[s3] UPPER BOUND CHECK: wordLength <= phi (=lRTrue+2*cTrue) violated in {ub_violations} / {ub_checked} elements");
    if let Some((e, wl, ph)) = &ub_witness {
        eprintln!("[s3] UB witness: {} wordLength={} phi={}", show(e), wl, ph);
    }
    let mut descent_checked = 0u64;
    let mut descent_found = 0u64;
    let mut descent_missing_witness: Option<Elt> = None;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        descent_checked += 1;
        let mut found = false;
        for c in gens_all(e) {
            if phi(&c) < ph { found = true; break; }
        }
        if found { descent_found += 1; }
        else if descent_missing_witness.is_none() { descent_missing_witness = Some(e.clone()); }
    }
    eprintln!("[s3] DESCENT CHECK: strict-decrease generator exists in {descent_found} / {descent_checked} non-identity elements");
    if let Some(e) = &descent_missing_witness {
        eprintln!("[s3] descent-missing witness: {} phi={}", show(e), phi(e));
    }
    // Characterize WHICH generator descends, by case: trivial (occTrue empty) vs not,
    // and (for nontrivial) whether s3 alone suffices.
    let mut trivial_nonone_count = 0u64;
    let mut trivial_s1_works = 0u64;
    let mut trivial_s2_works = 0u64;
    let mut nontrivial_count = 0u64;
    let mut nontrivial_s3_works = 0u64;
    let mut nontrivial_s3_fails_other_works = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        let is_trivial = a == 0 && b == -1; // occTrue empty <=> ATrue=0,BTrue=-1
        if is_trivial {
            trivial_nonone_count += 1;
            let g1 = gens_all(e)[0].clone();
            let g2 = gens_all(e)[1].clone();
            if phi(&g1) < ph { trivial_s1_works += 1; }
            if phi(&g2) < ph { trivial_s2_works += 1; }
        } else {
            nontrivial_count += 1;
            let g3 = s3(e);
            if phi(&g3) < ph { nontrivial_s3_works += 1; }
            else {
                let g1 = gens_all(e)[0].clone();
                let g2 = gens_all(e)[1].clone();
                if phi(&g1) < ph || phi(&g2) < ph { nontrivial_s3_fails_other_works += 1; }
            }
        }
    }
    eprintln!("[s3] trivial non-one: {trivial_nonone_count}, s1 descends: {trivial_s1_works}, s2 descends: {trivial_s2_works}");
    eprintln!("[s3] nontrivial: {nontrivial_count}, s3 descends: {nontrivial_s3_works}, (s3 fails but s1/s2 works): {nontrivial_s3_fails_other_works}");
    // When s3 fails, characterize s1/s2 exactly, and check siteCost(kstar) relationship.
    let mut s3fail_s1only = 0u64;
    let mut s3fail_s2only = 0u64;
    let mut s3fail_both = 0u64;
    let mut s3fail_neither = 0u64;
    let mut s3fail_neither_examples = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        let is_trivial = a == 0 && b == -1;
        if is_trivial { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        match (w1, w2) {
            (true, false) => s3fail_s1only += 1,
            (false, true) => s3fail_s2only += 1,
            (true, true) => s3fail_both += 1,
            (false, false) => {
                s3fail_neither += 1;
                if s3fail_neither_examples < 5 {
                    eprintln!("[descent-fail] {} phi={} k={}", show(e), ph, e.k);
                    s3fail_neither_examples += 1;
                }
            }
        }
    }
    eprintln!("[s3] s3-fails cases: s1-only={s3fail_s1only} s2-only={s3fail_s2only} both={s3fail_both} neither={s3fail_neither}");
    // Correlate which of s1/s2 works with (delta, eps, siteCost(kstar) parity) in the
    // s3-fails cases, to find a by-hand rule.
    let mut corr: std::collections::HashMap<(u8,i8,i64,i64,i64),(u64,u64,u64)> = std::collections::HashMap::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        let is_trivial = a == 0 && b == -1;
        if is_trivial { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        let (al, be, _) = abphi(e, e.k);
        let site_kstar = al.abs().max(be.abs());
        let dk = dep(&e.lamps, e.k);
        let key = (e.dl, e.eps, site_kstar as i64, dk.signum() as i64, (site_kstar % 2) as i64);
        let ent = corr.entry(key).or_insert((0,0,0));
        if w1 { ent.0 += 1; }
        if w2 { ent.1 += 1; }
        ent.2 += 1;
    }
    let mut keys: Vec<_> = corr.keys().cloned().collect();
    keys.sort();
    for k in keys.iter() {
        let v = corr[k];
        eprintln!("[corr] delta={} eps={} siteCostKstar={} sign_dk={} parity={} -> s1_works={} s2_works={} total={}",
            k.0, k.1, k.2, k.3, k.4, v.0, v.1, v.2);
    }
    // Check the exact parity relationship between alphaAt(kstar) and betaAt(kstar).
    let mut parity_match = 0u64;
    let mut parity_mismatch = 0u64;
    let mut parity_mismatch_example: Option<(Elt, i32, i32)> = None;
    for e in dist.keys() {
        let (al, be, _) = abphi(e, e.k);
        if (al.rem_euclid(2)) == (be.rem_euclid(2)) { parity_match += 1; }
        else {
            parity_mismatch += 1;
            if parity_mismatch_example.is_none() { parity_mismatch_example = Some((e.clone(), al, be)); }
        }
    }
    eprintln!("[parity] alpha(kstar)%2 == beta(kstar)%2: {parity_match} match, {parity_mismatch} mismatch");
    if let Some((e, al, be)) = &parity_mismatch_example {
        eprintln!("[parity] mismatch example: {} alpha={} beta={}", show(e), al, be);
    }
    // Precise implication check: for delta=false, does b*eps>=0 imply s1 strictly
    // decreases siteCost(kstar)? And b*eps<0 imply s2 does? (independent of window movement,
    // i.e. checking the FULL PhiZ descent, not just siteCost, to match the real target.)
    let mut impl_checked = 0u64;
    let mut impl_violated = 0u64;
    let mut impl_violation_example: Option<Elt> = None;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; } // skip trivial
        if e.dl != 0 { continue; } // delta=false ONLY for this precise check
        if e.k == 0 { continue; } // exclude kstar=0 (vArr active, different mechanism)
        let (al, be, _) = abphi(e, e.k);
        let m = al.abs().max(be.abs());
        if m == 0 { continue; }
        impl_checked += 1;
        let e_eps = e.eps as i32;
        let dk = dep(&e.lamps, e.k);
        let want_s1 = dk.signum() * e_eps >= 0;
        let cand = if want_s1 { gens_all(e)[0].clone() } else { gens_all(e)[1].clone() };
        if !(phi(&cand) < ph) {
            impl_violated += 1;
            if impl_violation_example.is_none() { impl_violation_example = Some(e.clone()); }
        }
    }
    eprintln!("[impl] sign(beta)*eps>=0 => s1 else s2 descends: {impl_violated} violations / {impl_checked} checked");
    if let Some(e) = &impl_violation_example {
        let (al, be, _) = abphi(e, e.k);
        eprintln!("[impl] violation: {} alpha={} beta={}", show(e), al, be);
    }
    // RETRY: restrict to the actual relevant scenario -- kstar at the window BOUNDARY
    // (matching Bincrease/Aincrease's structural requirement), kstar != 0, delta=false only
    // for now (mirrors the original clean-looking correlation table).
    let mut impl2_checked = 0u64;
    let mut impl2_violated = 0u64;
    let mut impl2_violation_example: Option<Elt> = None;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        let is_boundary = e.k == a || e.k == b + 1;
        if !is_boundary { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; } // s3 already descends; not the relevant case
        let (al, be, _) = abphi(e, e.k);
        let m = al.abs().max(be.abs());
        if m == 0 { continue; }
        impl2_checked += 1;
        let e_eps = e.eps as i32;
        let want_s1 = if e.dl == 0 { be.signum() * e_eps >= 0 } else { al.signum() * e_eps <= 0 };
        let cand = if want_s1 { gens_all(e)[0].clone() } else { gens_all(e)[1].clone() };
        if !(phi(&cand) < ph) {
            impl2_violated += 1;
            if impl2_violation_example.is_none() { impl2_violation_example = Some(e.clone()); }
        }
    }
    eprintln!("[impl2] boundary-only, kstar!=0, DELTA-DEPENDENT rule violations: {impl2_violated} / {impl2_checked}");
    if let Some(e) = &impl2_violation_example {
        let (al, be, _) = abphi(e, e.k);
        eprintln!("[impl2] violation: {} alpha={} beta={}", show(e), al, be);
    }
    let mut max_ab_gap = 0i32;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        let is_boundary = e.k == a || e.k == b + 1;
        if !is_boundary { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (al, be, _) = abphi(e, e.k);
        let gap = (al - be).abs();
        if gap > max_ab_gap { max_ab_gap = gap; }
    }
    eprintln!("[gap] max |alpha(kstar)-beta(kstar)| in the relevant regime: {max_ab_gap}");
    // Check: whenever s3 fails AND we're at left-boundary+delta=true, is beta*eps < 0 always?
    // And right-boundary+delta=false: alpha*eps > 0 always?
    let mut lt_checked = 0u64; let mut lt_ok = 0u64;
    let mut rf_checked = 0u64; let mut rf_ok = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (al, be, _) = abphi(e, e.k);
        if al.abs().max(be.abs()) == 0 { continue; }
        let eps = e.eps as i32;
        if e.dl == 1 && e.k == a {
            lt_checked += 1;
            if be * eps < 0 { lt_ok += 1; }
        }
        if e.dl == 0 && e.k == b + 1 {
            rf_checked += 1;
            if al * eps > 0 { rf_ok += 1; }
        }
    }
    eprintln!("[sign-check] left+delta=true: beta*eps<0 holds in {lt_ok}/{lt_checked}");
    eprintln!("[sign-check] right+delta=false: alpha*eps>0 holds in {rf_ok}/{rf_checked}");
    // Nail the EXACT boundary relation for delta=true "s3-fails" cases: is kstar == ATrue,
    // ATrue-1, BTrue, or BTrue+1?
    let mut rel_counts: std::collections::HashMap<&str, u64> = std::collections::HashMap::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        if e.dl != 1 { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (al, be, _) = abphi(e, e.k);
        if al.abs().max(be.abs()) == 0 { continue; }
        let rel = if e.k == a { "k=A" } else if e.k == a - 1 { "k=A-1" }
            else if e.k == b { "k=B" } else if e.k == b + 1 { "k=B+1" } else { "other" };
        *rel_counts.entry(rel).or_insert(0) += 1;
    }
    eprintln!("[rel-delta1] {:?}", rel_counts);
    // Check: in the window-UNCHANGED + s3-ascent case, is kstar always at the boundary
    // of the mu-window [ATrue,BTrue]?
    let mut wu_ascent_checked = 0u64;
    let mut wu_ascent_boundary = 0u64;
    let mut wu_ascent_kstar0 = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        let g3 = s3(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; } // window must be unchanged
        let dlr = lr_on(&g3, a2, b2) - lr_on(e, a, b);
        if dlr <= 0 { continue; } // only the ascent sub-case
        wu_ascent_checked += 1;
        if e.k == 0 { wu_ascent_kstar0 += 1; continue; }
        if e.k == a || e.k == b { wu_ascent_boundary += 1; }
    }
    eprintln!("[wu-ascent] checked={wu_ascent_checked} kstar=0:{wu_ascent_kstar0} at boundary(A or B):{wu_ascent_boundary}");
    // For the genuinely INTERIOR window-unchanged-ascent cases, does phi(s1) or phi(s2) < phi(g)?
    let mut int_checked = 0u64;
    let mut int_s1_or_s2 = 0u64;
    let mut int_neither = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        let g3 = s3(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; }
        let dlr = lr_on(&g3, a2, b2) - lr_on(e, a, b);
        if dlr <= 0 { continue; }
        if e.k == 0 || e.k == a || e.k == b { continue; } // skip boundary/zero, already handled
        int_checked += 1;
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        if phi(&g1) < ph || phi(&g2) < ph { int_s1_or_s2 += 1; }
        else { int_neither += 1; }
    }
    eprintln!("[wu-ascent-interior] checked={int_checked} s1-or-s2-works={int_s1_or_s2} neither={int_neither}");
    // Does siteCost(kstar)==1 ever occur in the interior-ascent regime?
    let mut sc1_count = 0u64;
    let mut sc_dist: std::collections::HashMap<i64,u64> = std::collections::HashMap::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        let g3 = s3(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; }
        let dlr = lr_on(&g3, a2, b2) - lr_on(e, a, b);
        if dlr <= 0 { continue; }
        if e.k == 0 || e.k == a || e.k == b { continue; }
        let (al, be, _) = abphi(e, e.k);
        let sc = al.abs().max(be.abs()) as i64;
        *sc_dist.entry(sc).or_insert(0) += 1;
        if sc == 1 { sc1_count += 1; }
    }
    eprintln!("[sc-dist-interior] siteCost(kstar)==1 count: {sc1_count}, full dist: {:?}", sc_dist);
    // Check: is siteCost(kstar) ALWAYS >0 whenever mu ascends at the crossed site (window
    // unchanged or not)?
    let mut hm_checked = 0u64;
    let mut hm_violated = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let g3 = s3(e);
        let p = if e.dl == 1 { e.k } else { e.k - 1 };
        let (a, b) = span_nogap(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; } // window must be unchanged
        let mu_before = mu(e, p);
        let mu_after = mu(&g3, p);
        if mu_after != mu_before + 1 { continue; } // only the ascent disjunct
        hm_checked += 1;
        let (al, be, _) = abphi(e, e.k);
        let sc = al.abs().max(be.abs());
        if sc == 0 { hm_violated += 1; }
    }
    eprintln!("[hM-check] siteCost(kstar)==0 while mu ascends: {hm_violated} / {hm_checked}");
    // For the siteCost==0 sub-case (window unchanged, ascent), is kstar always INTERIOR
    // to (ATrue, BTrue+1), i.e. counted by cTrue's filter?
    let mut sc0_checked = 0u64;
    let mut sc0_interior = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        let g3 = s3(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; }
        let p = if e.dl == 1 { e.k } else { e.k - 1 };
        let mu_before = mu(e, p);
        let mu_after = mu(&g3, p);
        if mu_after != mu_before + 1 { continue; }
        let (al, be, _) = abphi(e, e.k);
        let sc = al.abs().max(be.abs());
        if sc != 0 { continue; }
        sc0_checked += 1;
        if a < e.k && e.k < b + 1 { sc0_interior += 1; }
    }
    eprintln!("[sc0-interior] siteCost==0 cases: {sc0_checked}, interior to (A,B+1): {sc0_interior}");
    // Check: kstar=0, nontrivial (d not all zero) -- does some generator still descend?
    let mut k0nt_checked = 0u64;
    let mut k0nt_works = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 { continue; }
        if e.lamps.iter().all(|&(_,v)| v == 0) { continue; } // skip trivial (d==0 everywhere)
        k0nt_checked += 1;
        let g3 = s3(e);
        if phi(&g3) < ph { k0nt_works += 1; }
    }
    eprintln!("[k0-nontrivial] kstar=0 nontrivial descent via s3 ALONE: {k0nt_works} / {k0nt_checked}");
    // When s3 fails at kstar=0 nontrivial, does s1 or s2 work?
    let mut k0f_checked = 0u64;
    let mut k0f_s1 = 0u64;
    let mut k0f_s2 = 0u64;
    let mut k0f_neither = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 { continue; }
        if e.lamps.iter().all(|&(_,v)| v == 0) { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        k0f_checked += 1;
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        if w1 { k0f_s1 += 1; }
        if w2 { k0f_s2 += 1; }
        if !w1 && !w2 { k0f_neither += 1; }
    }
    eprintln!("[k0-fail] s3 fails: {k0f_checked}, s1 works: {k0f_s1}, s2 works: {k0f_s2}, neither: {k0f_neither}");
    // Does ShieldFires ever activate for s1(g) or s2(g) in the kstar=0 nontrivial s3-fails regime?
    fn shield_fires(e: &Elt) -> bool {
        e.k == 0 && e.dl == 0
            && e.lamps.iter().all(|&(j, v)| v == 0 || j >= 0)
            && e.lamps.iter().any(|&(j, v)| j >= 0 && v != 0)
    }
    let mut sf_checked = 0u64;
    let mut sf_g = 0u64;
    let mut sf_s1 = 0u64;
    let mut sf_s2 = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 { continue; }
        if e.lamps.iter().all(|&(_,v)| v == 0) { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        sf_checked += 1;
        if shield_fires(e) { sf_g += 1; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        if shield_fires(&g1) { sf_s1 += 1; }
        if shield_fires(&g2) { sf_s2 += 1; }
    }
    eprintln!("[shield-check] checked={sf_checked} shield(g)={sf_g} shield(s1)={sf_s1} shield(s2)={sf_s2}");
    // Combined: for kstar=0 nontrivial s3-fails cases, correlate delta, shield(g), shield(s1),
    // cut(0) status with which generator (s1/s2) works.
    let mut combo: std::collections::HashMap<(u8,bool,bool,bool,bool),(u64,u64,u64)> = std::collections::HashMap::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 { continue; }
        if e.lamps.iter().all(|&(_,v)| v == 0) { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        let sfg = shield_fires(e);
        let sf1 = shield_fires(&g1);
        let cut0g = is_cut(e, 0);
        let cut0s1 = is_cut(&g1, 0);
        let key = (e.dl, sfg, sf1, cut0g, cut0s1);
        let ent = combo.entry(key).or_insert((0,0,0));
        if w1 { ent.0 += 1; }
        if w2 { ent.1 += 1; }
        ent.2 += 1;
    }
    let mut keys: Vec<_> = combo.keys().cloned().collect();
    keys.sort();
    for k in keys {
        let v = combo[&k];
        eprintln!("[k0-combo] dl={} sfg={} sf1={} cut0g={} cut0s1={} -> s1={} s2={} total={}",
            k.0, k.1, k.2, k.3, k.4, v.0, v.1, v.2);
    }
    // How many of the "kstar=0 nontrivial" cases are genuine growth-transitions (window
    // moves) vs window-unchanged-ascent (already closed)?
    let mut growth_checked = 0u64;
    let mut wu_checked = 0u64;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 { continue; }
        if e.lamps.iter().all(|&(_,v)| v == 0) { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (a, b) = span_nogap(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 == a && b2 == b { wu_checked += 1; } else { growth_checked += 1; }
    }
    eprintln!("[k0-split] window-unchanged-ascent: {wu_checked}, genuine growth-transition: {growth_checked}");
    // Adecrease, delta=false, eps=1, kstar=0: is the alpha=0,beta=0 residual (siteCost(kstar)=0)
    // actually reachable, and if so, which generator (or generator pair) closes it?
    let mut adecr_f_eps1 = 0u64;
    let mut adecr_f_eps1_beta0 = 0u64;
    let mut beta0_examples: Vec<Elt> = vec![];
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        if e.k != 0 || e.dl != 0 || e.eps != 1 { continue; }
        if e.lamps.iter().all(|&(_, v)| v == 0) { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (a, b) = span_nogap(e);
        let (a2, _b2) = span_nogap(&g3);
        if a2 != a - 1 { continue; }
        adecr_f_eps1 += 1;
        let (al, be, _) = abphi(e, 0);
        if al == 0 && be == 0 {
            adecr_f_eps1_beta0 += 1;
            if !shield_fires(e) && beta0_examples.len() < 20 { beta0_examples.push(e.clone()); }
        }
    }
    let sf_count = {
        let mut c = 0u64;
        for e in dist.keys() {
            let ph = phi(e);
            if ph == 0 { continue; }
            if e.k != 0 || e.dl != 0 || e.eps != 1 { continue; }
            if e.lamps.iter().all(|&(_, v)| v == 0) { continue; }
            let g3 = s3(e);
            if phi(&g3) < ph { continue; }
            let (a, _b) = span_nogap(e);
            let (a2, _b2) = span_nogap(&g3);
            if a2 != a - 1 { continue; }
            let (al, be, _) = abphi(e, 0);
            if al == 0 && be == 0 && shield_fires(e) { c += 1; }
        }
        c
    };
    eprintln!("[adecr-eps1] delta=false eps=1 genuine-Adecrease count={adecr_f_eps1}, alpha=beta=0 residual={adecr_f_eps1_beta0}, of which ShieldFires={sf_count}, shield-absent-examples-found={}", beta0_examples.len());
    for e in &beta0_examples {
        let ph = phi(e);
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let g3 = s3(e);
        eprintln!("  example k={} dl={} eps={} lamps={:?} phi={} phi(s1)={} phi(s2)={} phi(s3)={}",
            e.k, e.dl, e.eps, e.lamps, ph, phi(&g1), phi(&g2), phi(&g3));
    }
    // Print raw (alpha,beta,d(kstar-1),d(kstar)) for delta=true interior-ascent cases.
    let mut printed3 = 0;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        let g3 = s3(e);
        let (a2, b2) = span_nogap(&g3);
        if a2 != a || b2 != b { continue; }
        let dlr = lr_on(&g3, a2, b2) - lr_on(e, a, b);
        if dlr <= 0 { continue; }
        if e.k == 0 || e.k == a || e.k == b { continue; }
        if e.dl != 1 { continue; }
        let (al, be, _) = abphi(e, e.k);
        let dkm1 = dep(&e.lamps, e.k - 1);
        let dk = dep(&e.lamps, e.k);
        if printed3 < 20 {
            eprintln!("[raw-interior] alpha={} beta={} d(k-1)={} d(k)={} eps={} k={} A={} B={}",
                al, be, dkm1, dk, e.eps, e.k, a, b);
            printed3 += 1;
        }
    }
    // Dump raw truth table for delta=true, boundary, kstar!=0, s3-fails cases.
    let mut seen: std::collections::HashSet<(i32,i32,i8,bool,bool,bool)> = std::collections::HashSet::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.dl != 1 { continue; }
        if e.k == 0 { continue; }
        let is_boundary = e.k == a || e.k == b + 1;
        if !is_boundary { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (al, be, _) = abphi(e, e.k);
        let m = al.abs().max(be.abs());
        if m == 0 || m > 3 { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        let is_left = e.k == a;
        let key = (al, be, e.eps, w1, w2, is_left);
        if seen.insert(key) {
            eprintln!("[truth-delta1] alpha={} beta={} eps={} s1={} s2={} is_left={}", al, be, e.eps, w1, w2, is_left);
        }
    }
    // Check delta=true specifically: does sign(kstar) matter too?
    let mut corr2: std::collections::HashMap<(i8,i32,i32),(u64,u64,u64)> = std::collections::HashMap::new();
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.dl != 1 { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        let dk = dep(&e.lamps, e.k);
        let key = (e.eps, dk.signum(), e.k.signum());
        let ent = corr2.entry(key).or_insert((0,0,0));
        if w1 { ent.0 += 1; }
        if w2 { ent.1 += 1; }
        ent.2 += 1;
    }
    let mut keys2: Vec<_> = corr2.keys().cloned().collect();
    keys2.sort();
    for k in keys2.iter() {
        let v = corr2[k];
        eprintln!("[corr2-delta1] eps={} sign_dk={} sign_kstar={} -> s1={} s2={} total={}", k.0, k.1, k.2, v.0, v.1, v.2);
    }
    // Directly verify the exchange-formula sign-flip claim: at siteCost=1, does s1/s2 EVER
    // achieve a strict phi decrease? Print c, c', and actual phi delta for siteCost=1 cases.
    let mut printed2 = 0;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        if e.k == 0 { continue; }
        let (al, be, _) = abphi(e, e.k);
        let c = al.abs().max(be.abs());
        if c != 1 { continue; }
        let g1 = gens_all(e)[0].clone();
        let (al1, be1, _) = abphi(&g1, g1.k);
        let c1 = al1.abs().max(be1.abs());
        let ph1 = phi(&g1);
        if ph1 < ph && printed2 < 10 {
            let is_boundary = e.k == a || e.k == b + 1;
            eprintln!("[c1check] {} c={} c'={} phi={} phi'={} A={} B={} is_boundary={}", show(e), c, c1, ph, ph1, a, b, is_boundary);
            printed2 += 1;
        }
    }
    // Print raw (alpha,beta) examples for the mixed siteCost=3 case to check hand-derived
    // shift formulas: s1 shifts (a,b) by (+/-eps,+/-eps) same sign; s2 shifts by (-eps,+eps).
    let mut printed = 0;
    for e in dist.keys() {
        let ph = phi(e);
        if ph == 0 { continue; }
        let (a, b) = span_nogap(e);
        if a == 0 && b == -1 { continue; }
        let g3 = s3(e);
        if phi(&g3) < ph { continue; }
        let (al, be, _) = abphi(e, e.k);
        let site_kstar = al.abs().max(be.abs());
        if site_kstar != 3 || e.dl != 0 || e.eps != -1 { continue; }
        let dk = dep(&e.lamps, e.k);
        if dk.signum() != -1 { continue; }
        let g1 = gens_all(e)[0].clone();
        let g2 = gens_all(e)[1].clone();
        let (al1, be1, _) = abphi(&g1, g1.k);
        let (al2, be2, _) = abphi(&g2, g2.k);
        let w1 = phi(&g1) < ph;
        let w2 = phi(&g2) < ph;
        if printed < 15 {
            eprintln!("[raw] delta={} eps={} a={} b={} -> s1(a={},b={},works={}) s2(a={},b={},works={})",
                e.dl, e.eps, al, be, al1, be1, w1, al2, be2, w2);
            printed += 1;
        }
    }

    let (mut max_jump, mut wsize, mut wit): (i64, i64, Option<(Elt, Elt, i64, i64)>) = (0, i64::MAX, None);
    let mut max_lr: i64 = 0;
    let mut max_cut: i64 = 0;
    let mut max_awin: i32 = 0;
    let mut max_bwin: i32 = 0;
    let mut both_nonempty_cut_violation = 0u64;
    let mut both_nonempty_count = 0u64;
    let mut newly_interior_is_cut = 0u64;
    let mut newly_interior_checked = 0u64;
    let mut shield_compensates = 0u64;
    let mut cut_examples = 0u64;
    let mut nonzero_kstar_cut_case = 0u64;
    let mut shift_with_nonzero_kstar_both = 0u64;
    let mut window_unchanged_shield_eligible = 0u64;
    let mut window_unchanged_shield_and_cut0 = 0u64;
    let mut b_growth_delta_false = 0u64;
    let mut a_growth_delta_true = 0u64;
    let mut b_decrease_delta_true = 0u64;
    let mut a_increase_delta_false = 0u64;
    let mut b_incr_nonzero_boundary_site = 0u64;
    let mut b_incr_checked = 0u64;
    let mut b_incr_g_kstar_zero = 0u64;
    let mut b_incr_s3g_kstar_zero = 0u64;
    let mut b_decr_g_kstar_zero = 0u64;
    let mut b_decr_s3g_kstar_zero = 0u64;
    let mut b_decr_nonzero_dkstar = 0u64;
    let mut b_decr_checked = 0u64;
    let mut b_incr_false_kstar0 = 0u64;
    let mut a_decr_true_kstar0 = 0u64;
    let mut window_unchanged_count = 0u64;
    let mut max_lr_window_unchanged = 0i64;
    let mut window_unchanged_lr_nonzero = 0u64;
    let mut wu_p1_true = 0u64;
    let mut wu_p1_false = 0u64;
    let mut wu_m1_true = 0u64;
    let mut wu_m1_false = 0u64;
    let mut window_unchanged_p_unoccupied = 0u64;
    let mut window_unchanged_p_outside_mu_window = 0u64;
    let mut a_incr_kstar0_count = 0u64;
    let mut a_incr_kstar0_lr_p1 = 0u64;
    let mut a_incr_kstar0_lr_other: Vec<i64> = vec![];
    let mut a_decr_kstar0_count = 0u64;
    let mut a_decr_kstar0_lr_m1 = 0u64;
    let mut a_decr_kstar0_lr_other: Vec<i64> = vec![];
    for e in dist.keys() {
        let e2 = s3(e);
        let (p1, p2) = (phi(e), phi(&e2));
        let jump = (p2 - p1).abs();
        let sz = size(e);
        let (a1, b1) = span_nogap(e);
        let (a2, b2) = span_nogap(&e2);
        let dlr = (lr_on(&e2, a2, b2) - lr_on(e, a1, b1)).abs();
        let dcut = (cuts_on(&e2, a2, b2) - cuts_on(e, a1, b1)).abs();
        if dlr > max_lr { max_lr = dlr; }
        if dcut > max_cut { max_cut = dcut; }
        if (a2 - a1).abs() > max_awin { max_awin = (a2 - a1).abs(); }
        if (b2 - b1).abs() > max_bwin { max_bwin = (b2 - b1).abs(); }
        if a1 == a2 && b1 == b2 {
            window_unchanged_count += 1;
            let p = if e.dl == 1 { e.k } else { e.k - 1 };
            let dp = dep(&e.lamps, p);
            if dp == 0 { window_unchanged_p_unoccupied += 1; }
            if !(a1 <= p && p <= b1) { window_unchanged_p_outside_mu_window += 1; }

            let lr_delta = lr_on(&e2, a2, b2) - lr_on(e, a1, b1);
            if lr_delta.abs() > max_lr_window_unchanged { max_lr_window_unchanged = lr_delta.abs(); }
            if lr_delta != 0 { window_unchanged_lr_nonzero += 1; }
            if lr_delta == 1 && e.dl == 1 { wu_p1_true += 1; }
            if lr_delta == 1 && e.dl == 0 { wu_p1_false += 1; }
            if lr_delta == -1 && e.dl == 1 { wu_m1_true += 1; }
            if lr_delta == -1 && e.dl == 0 { wu_m1_false += 1; }
        }
        // "both nonempty" proxy: span nonempty (a<=b) on both sides, i.e. not the
        // degenerate empty-occTrue case (which shows up as a==0,b==-1 with no deposits).
        let e_nonempty = !(a1 == 0 && b1 == -1 && e.lamps.is_empty());
        let e2_nonempty = !(a2 == 0 && b2 == -1 && e2.lamps.is_empty());
        if e_nonempty && e2_nonempty {
            both_nonempty_count += 1;
            fn shield_fires(e: &Elt) -> bool {
                e.k == 0 && e.dl == 0
                    && e.lamps.iter().all(|&(j, v)| v == 0 || j >= 0)
                    && e.lamps.iter().any(|&(j, v)| j >= 0 && v != 0)
            }
            let shield1_any = shield_fires(e);
            let shield2_any = shield_fires(&e2);
            if (shield1_any || shield2_any) && a1 == a2 && b1 == b2 {
                window_unchanged_shield_eligible += 1;
                if is_cut(e, 0) { window_unchanged_shield_and_cut0 += 1; }
            }
            if a1 != a2 && b1 != b2 {
                // both endpoints moved simultaneously -- would refute the "only one
                // moves" hypothesis
                both_nonempty_cut_violation += 1;
            }
            // if a boundary moved, check whether the newly-interior site is a cut site
            // (if it ever is, cTrue's invariance needs a compensating shield flip, not
            // just "the new site is never a cut")
            let shield1 = e.k == 0 && e.dl == 0 && a1 == 0 && b1 + 1 > 0 && is_cut(e, 0);
            let shield2 = e2.k == 0 && e2.dl == 0 && a2 == 0 && b2 + 1 > 0 && is_cut(&e2, 0);
            let mut new_site_cut = false;
            let mut shift_happened = false;
            if b2 == b1 + 1 && e.dl == 0 { b_growth_delta_false += 1; }
            if a2 == a1 - 1 && e.dl == 1 { a_growth_delta_true += 1; }
            if b2 == b1 - 1 && e.dl == 1 { b_decrease_delta_true += 1; }
            if a2 == a1 + 1 && e.dl == 0 { a_increase_delta_false += 1; }
            if b2 == b1 + 1 && e.dl == 1 {
                let p = b2; // new BTrue
                let dep_p1 = dep(&e.lamps, p + 1);
                if dep_p1 != 0 { b_incr_nonzero_boundary_site += 1; }
                b_incr_checked += 1;
            }
            if b2 == b1 + 1 && e.dl == 1 && e.k == 0 { b_incr_g_kstar_zero += 1; }
            if b2 == b1 + 1 && e.dl == 1 && e2.k == 0 { b_incr_s3g_kstar_zero += 1; }
            if b2 == b1 - 1 && e.dl == 0 && e.k == 0 { b_decr_g_kstar_zero += 1; }
            if b2 == b1 - 1 && e.dl == 0 && e2.k == 0 { b_decr_s3g_kstar_zero += 1; }
            if b2 == b1 - 1 && e.dl == 0 {
                let dep_kstar = dep(&e.lamps, e.k);
                if dep_kstar != 0 { b_decr_nonzero_dkstar += 1; }
                b_decr_checked += 1;
            }
            if b2 == b1 + 1 && e.dl == 0 && e.k == 0 { b_incr_false_kstar0 += 1; }
            if a2 == a1 - 1 && e.dl == 1 && e2.k == 0 { a_decr_true_kstar0 += 1; }
            // Aincrease (delta=true, ATrue increases by 1): kstar=0 sub-case for lRTrue
            if a2 == a1 + 1 && e.dl == 1 && e.k == 0 {
                a_incr_kstar0_count += 1;
                let dlr2 = lr_on(&e2, a2, b2) - lr_on(e, a1, b1);
                if dlr2 == -1 { a_incr_kstar0_lr_p1 += 1; } else { a_incr_kstar0_lr_other.push(dlr2); }
            }
            // Adecrease (delta=false, ATrue decreases by 1): kstar=0 sub-case for lRTrue
            if a2 == a1 - 1 && e.dl == 0 && e2.k == 0 {
                a_decr_kstar0_count += 1;
                let dlr2 = lr_on(&e2, a2, b2) - lr_on(e, a1, b1);
                if dlr2 == 1 { a_decr_kstar0_lr_m1 += 1; } else { a_decr_kstar0_lr_other.push(dlr2); }
            }
            if b2 == b1 + 1 { new_site_cut = is_cut(e, b1 + 1); shift_happened = true; }
            if b1 == b2 + 1 { new_site_cut = is_cut(&e2, b2 + 1); shift_happened = true; }
            if a2 == a1 - 1 { new_site_cut = is_cut(e, a1); shift_happened = true; }
            if a1 == a2 - 1 { new_site_cut = is_cut(&e2, a2); shift_happened = true; }
            if shift_happened {
                newly_interior_checked += 1;
                if e.k != 0 && e2.k != 0 { shift_with_nonzero_kstar_both += 1; }
                if new_site_cut {
                    newly_interior_is_cut += 1;
                    if shield1 != shield2 { shield_compensates += 1; }
                    if e.k != 0 && e2.k != 0 { nonzero_kstar_cut_case += 1; }
                    if cut_examples < 6 {
                        let dir = if b2 == b1 + 1 { "B+1" } else if b1 == b2 + 1 { "B-1" }
                            else if a2 == a1 - 1 { "A-1" } else { "A+1" };
                        eprintln!("[cutcase] dir={dir} delta={} k={} eps={} a1={a1} b1={b1} a2={a2} b2={b2} shield1={shield1} shield2={shield2}", e.dl, e.k, e.eps);
                        cut_examples += 1;
                    }
                }
            }
        }
        if jump > max_jump || (jump == max_jump && sz < wsize) {
            max_jump = jump; wsize = sz; wit = Some((e.clone(), e2, p1, p2));
        }
    }
    println!("[s3] max |dPhi| under s3 ALONE (nogapBS potential) = {max_jump}");
    println!("[s3] max |d(lRTrue)| = {max_lr}, max |d(cTrue)| = {max_cut}");
    println!("[s3] max |d(ATrue)| = {max_awin}, max |d(BTrue)| = {max_bwin}");
    println!("[s3] both-endpoints-moved-simultaneously count = {both_nonempty_cut_violation} / {both_nonempty_count} both-nonempty pairs checked");
    println!("[s3] newly-interior site IS a cut site: {newly_interior_is_cut} / {newly_interior_checked} boundary-shift cases");
    println!("[s3] of those, shield flips to compensate: {shield_compensates} / {newly_interior_is_cut}");
    println!("[s3] of the cut cases, kstar!=0 on BOTH sides: {nonzero_kstar_cut_case} / {newly_interior_is_cut}");
    println!("[s3] boundary shifts with kstar!=0 on BOTH sides: {shift_with_nonzero_kstar_both} / {newly_interior_checked}");
    println!("[s3] window UNCHANGED but shield-eligible (kstar=0,delta=false on either side): {window_unchanged_shield_eligible}");
    println!("[s3] of those, cut(0) is true: {window_unchanged_shield_and_cut0}");
    println!("[s3] B-growth with delta=false: {b_growth_delta_false}; A-growth with delta=true: {a_growth_delta_true}");
    println!("[s3] B-decrease with delta=true: {b_decrease_delta_true}; A-increase with delta=false: {a_increase_delta_false}");
    println!("[s3] Bincrease: d(p+1) nonzero: {b_incr_nonzero_boundary_site} / {b_incr_checked}");
    println!("[s3] Bincrease at g.kstar=0: {b_incr_g_kstar_zero}; at s3g.kstar=0: {b_incr_s3g_kstar_zero}");
    println!("[s3] Bdecrease at g.kstar=0: {b_decr_g_kstar_zero}; at s3g.kstar=0: {b_decr_s3g_kstar_zero}");
    println!("[s3] Bdecrease: d(kstar) nonzero: {b_decr_nonzero_dkstar} / {b_decr_checked}");
    println!("[s3] Bincrease-delta-false at g.kstar=0: {b_incr_false_kstar0}; Adecrease-delta-true at s3g.kstar=0: {a_decr_true_kstar0}");
    println!("[s3] window-unchanged: count={window_unchanged_count}, max|d(lRTrue)|={max_lr_window_unchanged}, nonzero cases={window_unchanged_lr_nonzero}");
    println!("[s3] window-unchanged by sign/delta: +1&true={wu_p1_true} +1&false={wu_p1_false} -1&true={wu_m1_true} -1&false={wu_m1_false}");
    println!("[s3] window-unchanged with p unoccupied (d(p)=0): {window_unchanged_p_unoccupied}");
    println!("[s3] window-unchanged with p outside mu window [A,B]: {window_unchanged_p_outside_mu_window}");
    println!("[s3] Aincrease(delta=true) at g.kstar=0: count={a_incr_kstar0_count}, d(lRTrue)=-1 in {a_incr_kstar0_lr_p1}, other deltas: {:?}", &a_incr_kstar0_lr_other[..a_incr_kstar0_lr_other.len().min(10)]);
    println!("[s3] Adecrease(delta=false) at s3g.kstar=0: count={a_decr_kstar0_count}, d(lRTrue)=+1 in {a_decr_kstar0_lr_m1}, other deltas: {:?}", &a_decr_kstar0_lr_other[..a_decr_kstar0_lr_other.len().min(10)]);
    if let Some((e, e2, p1, p2)) = wit {
        println!("  witness: {}  ->  {}", show(&e), show(&e2));
        println!("  Phi before = {p1}, Phi after = {p2}");
    }
}

#[allow(dead_code)]
fn one_probe(name: &str, e: Elt) {
    let e2 = s3(&e);
    let (a1, b1) = span_nogap(&e);
    let (a2, b2) = span_nogap(&e2);
    eprintln!("[{name}] e={:?} -> e2={:?}", e, e2);
    eprintln!("[{name}] span before=({a1},{b1}) after=({a2},{b2})");
    eprintln!("[{name}] cuts before={} after={}", cuts_on(&e, a1, b1), cuts_on(&e2, a2, b2));
    for s in (a1.min(a2) - 1)..=(b1.max(b2) + 2) {
        eprintln!("[{name}]   is_cut(e,{s})={} is_cut(e2,{s})={}", is_cut(&e, s), is_cut(&e2, s));
    }
}
#[allow(dead_code)]
fn probe_manual() {
    // delta=true, A-side removal (window shrinks): k=-3 (avoid k=-1 which is the
    // kstar=0-adjacent special case), d(-3)=eps=1 so s3 zeroes it (removal).
    one_probe("removal-true", Elt { eps: 1, dl: 1, k: -3, lamps: vec![(-3, 1)] });
    // delta=false, A-side growth: need g.kstar=k>0 (generic), p=k-1 vacant in g
    // (d(k-1)=0), becoming occupied in s3g. Use k=3, some other deposit to keep
    // occTrue g nonempty independent of p (e.g. an existing deposit further left
    // isn't needed -- travel(k,.) already occupies [0,k) so occTrue g is nonempty
    // via travel alone for k>0).
    one_probe("addition-false", Elt { eps: 1, dl: 0, k: 3, lamps: vec![] });
}

#[allow(dead_code)]
fn probe_empty_occ_s3g() {
    // occTrue(s3g)=empty means (s3g).kstar=0, (s3g).d≡0. Build g by inverting s3.
    // delta=true: g.k=-1, d empty (s3g).k=0. delta=false: g.k=1, d empty.
    for (delta, k) in [(1u8, -1i32), (0u8, 1i32)] {
        for eps in [1i8, -1i8] {
            // need d(crossed) = eps so it cancels to 0 after s3, making occTrue(s3g) empty
            let crossed = if delta == 1 { k } else { k - 1 };
            let dval = if delta == 1 { eps as i32 } else { -(eps as i32) };
            let e = Elt { eps, dl: delta, k, lamps: vec![(crossed, dval)] };
            let e2 = s3(&e);
            let (a1, b1) = span_nogap(&e);
            let (a2, b2) = span_nogap(&e2);
            eprintln!(
                "[empty_s3g] delta={delta} k={k} eps={eps} span_g=({a1},{b1}) span_s3g=({a2},{b2}) lr_g={} lr_s3g={}",
                lr_on(&e, a1, b1), lr_on(&e2, a2, b2)
            );
        }
    }
}

#[allow(dead_code)]
fn probe_empty_occ() {
    for delta in [0u8, 1u8] {
        for eps in [1i8, -1i8] {
            let e = Elt { eps, dl: delta, k: 0, lamps: vec![] };
            let e2 = s3(&e);
            let (a1, b1) = span_nogap(&e);
            let (a2, b2) = span_nogap(&e2);
            eprintln!(
                "[empty] delta={delta} eps={eps} span_g=({a1},{b1}) span_s3g=({a2},{b2}) lr_g={} lr_s3g={} cuts_g={} cuts_s3g={}",
                lr_on(&e, a1, b1), lr_on(&e2, a2, b2), cuts_on(&e, a1, b1), cuts_on(&e2, a2, b2)
            );
        }
    }
}
