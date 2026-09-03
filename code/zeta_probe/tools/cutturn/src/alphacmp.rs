// Does the derived-sign model reproduce the paper's alpha?
//
// sitecost's site vectors are  arr = [pu, u-pu, pd, dn-pd],  dep = [pd, dn-pd, pu, u-pu]
// -- the class is (side, sign OF THE STRAND), and both ends of a strand share the sign.
// Then  alpha = (Cp-Cm) - (Ap-Am) = 2(pd-pu) = d  when u = dn, which is the paper's alpha.
//
// EndData.sgn instead derives the sign from (side, isArr, depSign side), so on a fixed
// side every ARRIVAL carries one sign and every DEPARTURE the other.  The class counts
// are then degenerate and alpha comes out differently.  This compares them.

pub fn run(mmax: usize) {
    println!("[cutturn] alpha under the two sign conventions, f = 0 so u = dn = m/2");
    println!("  {:>3} {:>3} {:>3} {:>5} {:>10} {:>10}", "m", "pu", "pd", "d", "alpha_sc", "alpha_ed");
    let mut disagree = 0u64;
    let mut total = 0u64;
    let mut m = 2usize;
    while m <= mmax {
        let u = m / 2;
        let dn = u;
        for pu in 0..=u {
            for pd in 0..=dn {
                let d = 2 * (pd as i64 - pu as i64);
                // sitecost: class = (side, strand sign)
                let (ap, am) = (pu as i64, (u - pu) as i64);
                let (cp, cm) = (pd as i64, (dn - pd) as i64);
                let alpha_sc = (cp - cm) - (ap - am);
                // EndData: every arrival on the side takes depSign, every departure its
                // negation.  Take depSign = true; the other choice mirrors it.
                let (ap2, am2) = (u as i64, 0i64);
                let (cp2, cm2) = (0i64, dn as i64);
                let alpha_ed = (cp2 - cm2) - (ap2 - am2);
                total += 1;
                if alpha_sc != alpha_ed { disagree += 1; }
                if m <= 4 {
                    println!("  {:>3} {:>3} {:>3} {:>5} {:>10} {:>10}", m, pu, pd, d, alpha_sc, alpha_ed);
                }
            }
        }
        m += 2;
    }
    // which deposits can the derived-sign model represent at all?
    println!();
    println!("[cutturn] deposits representable under each convention");
    println!("  {:>3} {:>28} {:>26}", "m", "d values (sitecost)", "d values (EndData)");
    let mut mm = 2usize;
    while mm <= mmax {
        let u = mm / 2;
        let mut sc: Vec<i64> = vec![];
        for pu in 0..=u { for pd in 0..=u {
            let d = 2 * (pd as i64 - pu as i64);
            if !sc.contains(&d) { sc.push(d); }
        } }
        sc.sort();
        // EndData: sgn depends on (side, isArr), so all up strands of an edge share a
        // sign and all down strands the other; pu is pinned to 0 or u, likewise pd.
        let mut ed: Vec<i64> = vec![];
        for &pu in [0usize, u].iter() { for &pd in [0usize, u].iter() {
            let d = 2 * (pd as i64 - pu as i64);
            if !ed.contains(&d) { ed.push(d); }
        } }
        ed.sort();
        println!("  {:>3} {:>28} {:>26}", mm, format!("{:?}", sc), format!("{:?}", ed));
        mm += 2;
    }
    println!();
    println!("  alpha_sc = d in every row (sitecost's convention is the paper's)");
    println!("  {} of {} rows disagree between the conventions", disagree, total);
    println!("  {}", if disagree > 0 {
        "THE DERIVED SIGN DOES NOT REPRODUCE THE PAPER'S alpha"
    } else { "the two agree" });
}
