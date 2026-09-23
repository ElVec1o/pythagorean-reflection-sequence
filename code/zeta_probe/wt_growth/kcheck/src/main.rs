// Build an explicit word realizing a pure translation with edge profile a_j = 2 s_j (j=0..N-1),
// s_j = sign cos(j theta), via the lamp model; evaluate it geometrically in C; report len/|v|.
#[derive(Clone,Copy)] struct C { re: f64, im: f64 }
fn mul(a:C,b:C)->C{C{re:a.re*b.re-a.im*b.im,im:a.re*b.im+a.im*b.re}}
fn add(a:C,b:C)->C{C{re:a.re+b.re,im:a.im+b.im}}
fn conj(a:C)->C{C{re:a.re,im:-a.im}}
// affine map z -> al * sigma^dl(z) + be
#[derive(Clone,Copy)] struct A { al: C, dl: bool, be: C }
fn comp(f:A,g:A)->A{ // f o g
  let gal = if f.dl {conj(g.al)} else {g.al};
  let gbe = if f.dl {conj(g.be)} else {g.be};
  A{al:mul(f.al,gal), dl: f.dl ^ g.dl, be: add(mul(f.al,gbe), f.be)}
}
fn main(){
  let args: Vec<String> = std::env::args().collect();
  let c: f64 = args[1].parse().unwrap(); let e: f64 = args[2].parse().unwrap();
  let n: i32 = args[3].parse().unwrap();
  let cs = e/(2.0*c); let sn = (1.0-cs*cs).sqrt();
  let z = C{re:cs,im:sn}; let zi = conj(z);
  let theta = sn.atan2(cs);
  let gens = [A{al:C{re:1.0,im:0.0},dl:true,be:C{re:0.0,im:0.0}},
              A{al:C{re:-1.0,im:0.0},dl:true,be:C{re:0.0,im:0.0}},
              A{al:zi,dl:true,be:add(C{re:1.0,im:0.0},C{re:-zi.re,im:-zi.im})}];
  // lamp model state
  let (mut eps, mut dl, mut k) = (1i32, 0i32, 0i32);
  let mut lamps = std::collections::HashMap::<i32,i32>::new();
  let mut word: Vec<usize> = vec![];
  let mut apply = |g: usize, eps:&mut i32, dl:&mut i32, k:&mut i32, lamps:&mut std::collections::HashMap<i32,i32>, word:&mut Vec<usize>| {
    word.push(g);
    match g { 0 => { *dl = 1-*dl; }, 1 => { *dl = 1-*dl; *eps = -*eps; },
      _ => { if *dl==0 { *lamps.entry(*k-1).or_insert(0) += *eps; *k -= 1; *dl = 1; }
             else { *lamps.entry(*k).or_insert(0) -= *eps; *k += 1; *dl = 0; } } }
  };
  let s = |j:i32| -> i32 { if ((j as f64)*theta).cos() >= 0.0 {1} else {-1} };
  // right sweep: cross edge j (k=j -> j+1) depositing -eps; want deposit s_j => eps = -s_j, need dl=1
  for j in 0..n {
    let want_eps = -s(j);
    // toggle to dl=1 choosing generator to set eps
    if dl == 1 { if eps != want_eps { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word); apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} }
    else { if eps == want_eps { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} else { apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} }
    apply(2,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);
  }
  // left sweep: cross edge j (k=j+1 -> j) depositing +eps; want +s_j => eps = s_j, need dl=0
  for j in (0..n).rev() {
    let want_eps = s(j);
    if dl == 0 { if eps != want_eps { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word); apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} }
    else { if eps == want_eps { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} else { apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} }
    apply(2,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);
  }
  // restore dl=0, eps=1
  if dl==1 { if eps==1 { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} else { apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word);} }
  if eps != 1 { apply(0,&mut eps,&mut dl,&mut k,&mut lamps,&mut word); apply(1,&mut eps,&mut dl,&mut k,&mut lamps,&mut word); }
  assert!(k==0 && dl==0 && eps==1);
  let ok = (0..n).all(|j| lamps.get(&j).copied().unwrap_or(0) == 2*s(j));
  // geometric evaluation, both composition orders
  let id = A{al:C{re:1.0,im:0.0},dl:false,be:C{re:0.0,im:0.0}};
  let mut m1 = id; for &g in &word { m1 = comp(m1, gens[g]); }
  let mut m2 = id; for &g in &word { m2 = comp(gens[g], m2); }
  let l = word.len() as f64;
  let v1 = (m1.be.re.hypot(m1.be.im)); let v2 = (m2.be.re.hypot(m2.be.im));
  let zm1 = ((cs-1.0).powi(2)+sn*sn).sqrt(); let zp1 = ((cs+1.0).powi(2)+sn*sn).sqrt();
  println!("N={} len={} profile_ok={} lin1=({:.3e},{:.3e},{}) lin2=({:.3e},{:.3e},{})", n, word.len(), ok, m1.al.re-1.0, m1.al.im, m1.dl, m2.al.re-1.0, m2.al.im, m2.dl);
  println!("|v|={:.6} / {:.6}  len/|v| = {:.6} / {:.6}   pi/|z-1|={:.6}  9/(|z-1||z+1|^2)={:.6}", v1, v2, l/v1, l/v2, std::f64::consts::PI/zm1, 9.0/(zm1*zp1*zp1));
}
