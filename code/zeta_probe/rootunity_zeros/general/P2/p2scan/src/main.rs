// p2scan: zeros of B(q)=sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k} near q=zeta=e(a/N), q=zeta*exp(-t).
// f64 with running log-scale; reports lost digits (max|b_k|/|B|). VERIFIED-level numerics only;
// certificates are done separately in Arb (P2_cert.py).
// usage: p2scan count a N s0 s1 ns th0 th1 nth   (u=log t = s+i*theta, grid of cells; argument principle per cell)
//        p2scan eval a N tre tim
use std::env;
mod mp;
#[derive(Clone,Copy,Debug)] struct C{re:f64,im:f64}
impl C{fn n(re:f64,im:f64)->C{C{re,im}}
 fn add(self,o:C)->C{C::n(self.re+o.re,self.im+o.im)} fn sub(self,o:C)->C{C::n(self.re-o.re,self.im-o.im)}
 fn mul(self,o:C)->C{C::n(self.re*o.re-self.im*o.im,self.re*o.im+self.im*o.re)}
 fn div(self,o:C)->C{let d=o.re*o.re+o.im*o.im;C::n((self.re*o.re+self.im*o.im)/d,(self.im*o.re-self.re*o.im)/d)}
 fn abs(self)->f64{self.re.hypot(self.im)} fn sc(self,s:f64)->C{C::n(self.re*s,self.im*s)}
 fn exp(self)->C{let e=self.re.exp();C::n(e*self.im.cos(),e*self.im.sin())}
 fn arg(self)->f64{self.im.atan2(self.re)}}
fn expm1c(z:C)->C{ let em=z.re.exp_m1(); let (s,c)=z.im.sin_cos(); let h=(z.im*0.5).sin();
  C::n(em*c-2.0*h*h, (em+1.0)*s)}
// returns (B scaled: value = m * exp(lg)), lg, lost digits, k used
fn bval(a:i64,n:i64,t:C)->(C,f64,f64,usize){
  let tp=2.0*std::f64::consts::PI;
  let zp=|j:i64|->C{let ang=tp*((a*j).rem_euclid(n)) as f64/(n as f64);C::n(ang.cos(),ang.sin())};
  let qpow=|j:i64|->C{ zp(j).mul(t.sc(-(j as f64)).exp()) };
  let one_minus=|j:i64|->C{ if (a*j).rem_euclid(n)==0 { expm1c(t.sc(-(j as f64))).sc(-1.0) } else { C::n(1.0,0.0).sub(qpow(j)) } };
  let q=qpow(1); let ct=C::n(1.0,0.0).sub(q).sc(-2.0);
  // log-scaled accumulation: b = bm*exp(bl), S = sm*exp(sl)
  let mut bm=C::n(1.0,0.0); let mut bl=0.0f64; let mut sm=C::n(1.0,0.0); let mut sl=0.0f64; let mut mx=0.0f64;
  let mut k:i64=0;
  loop{
    let j=2*k+1;
    let r=ct.mul(qpow(j)).div(one_minus(j).mul(one_minus(j+1)));
    bm=bm.mul(r); let ab=bm.abs(); if ab>1e50||ab<1e-50 { bl+=ab.ln(); bm=bm.sc(1.0/ab); }
    k+=1;
    let lb=bl+bm.abs().ln(); if lb>mx {mx=lb;}
    // add b to S
    if lb>sl { let f=(sl-lb).exp(); sm=sm.sc(f).add(bm.sc((bl-lb).exp()*(1.0))); sl=lb; }
    else { sm=sm.add(bm.sc((bl-sl).exp())); }
    let as_=sm.abs(); if as_>1e50||as_<1e-50 { sl+=as_.ln(); sm=sm.sc(1.0/as_); }
    if k>10 && lb< mx-60.0 && lb < sl+sm.abs().ln()-40.0 && r.abs()<0.5 { break; }
    if k>50_000_000 { break; }
  }
  let lgS=sl+sm.abs().ln();
  (sm.sc(1.0/sm.abs()), lgS, (mx-lgS)/std::f64::consts::LN_10, k as usize)
}
fn phase(a:i64,n:i64,u:C)->(f64,f64){ let t=u.exp(); let (m,lg,lost,_)=bval(a,n,t); (m.arg(),lg.max(-1e9)+0.0*lost) }
fn wind_edge(a:i64,n:i64,u0:C,u1:C,maxlost:&mut f64)->f64{
  // adaptive: accumulate phase increments, refine until each |dphi|<0.5
  let mut tot=0.0; let mut stack=vec![(0.0f64,1.0f64)];
  let at=|s:f64,ml:&mut f64|->f64{ let u=u0.add(u1.sub(u0).sc(s)); let (m,_lg,lost,_)=bval(a,n,u.exp()); if lost>*ml{*ml=lost;} m.arg()};
  let mut cache_a=at(0.0,maxlost);
  // iterative subdivision left to right
  let mut s=0.0; let mut h=1.0/16.0;
  while s<1.0-1e-15 {
    if s+h>1.0 {h=1.0-s;}
    let pb=at(s+h,maxlost);
    let mut d=pb-cache_a; while d>std::f64::consts::PI {d-=2.0*std::f64::consts::PI;} while d< -std::f64::consts::PI {d+=2.0*std::f64::consts::PI;}
    if d.abs()>0.4 && h>1e-9 { h*=0.5; continue; }
    tot+=d; s+=h; cache_a=pb; if d.abs()<0.1 {h*=1.5;}
  }
  let _=&mut stack; tot
}
fn mwind(a:i64,n:i64,u0:C,u1:C,ml:&mut f64,nev:&mut usize)->f64{
  let at=|s:f64,ml:&mut f64,nev:&mut usize|->f64{ let u=u0.add(u1.sub(u0).sc(s)); let t=u.exp(); let r=mp::bval(a,n,t.re,t.im); *nev+=1; if r.lost_bits>*ml{*ml=r.lost_bits;} r.im.atan2(r.re)};
  let mut pa=at(0.0,ml,nev); let mut s=0.0; let mut h=1.0/32.0; let mut tot=0.0;
  while s<1.0-1e-15 { if s+h>1.0 {h=1.0-s;}
    let pb=at(s+h,ml,nev); let mut d=pb-pa; let tp=2.0*std::f64::consts::PI;
    while d>std::f64::consts::PI {d-=tp;} while d< -std::f64::consts::PI {d+=tp;}
    if d.abs()>0.5 && h>1e-10 { h*=0.5; continue; }
    tot+=d; s+=h; pa=pb; if d.abs()<0.15 {h=(h*1.5).min(0.25);} }
  tot }
fn main(){
  let a:Vec<String>=env::args().collect(); let f=|i:usize|->f64{a[i].parse().unwrap()};
  let (aa,nn)=(a[2].parse::<i64>().unwrap(),a[3].parse::<i64>().unwrap());
  match a[1].as_str(){
   "eval"=>{ let t=C::n(f(4),f(5)); let (m,lg,lost,k)=bval(aa,nn,t); println!("argB={:.6} log|B|={:.6} lost={:.2} k={}",m.arg(),lg,lost,k); }
   "count"=>{ let (s0,s1,ns,t0,t1,nt)=(f(4),f(5),f(6) as usize,f(7),f(8),f(9) as usize);
     let mut tot=0i64; let mut worst=0.0f64;
     for i in 0..ns { for j in 0..nt {
       let sa=s0+(s1-s0)*(i as f64)/(ns as f64); let sb=s0+(s1-s0)*((i+1) as f64)/(ns as f64);
       let ta=t0+(t1-t0)*(j as f64)/(nt as f64); let tb=t0+(t1-t0)*((j+1) as f64)/(nt as f64);
       let c=[C::n(sa,ta),C::n(sb,ta),C::n(sb,tb),C::n(sa,tb)]; let mut w=0.0; let mut ml=0.0;
       for e in 0..4 { w+=wind_edge(aa,nn,c[e],c[(e+1)%4],&mut ml); }
       let z=(w/(2.0*std::f64::consts::PI)).round() as i64; if ml>worst{worst=ml;}
       if z!=0 { println!("cell s[{:.4},{:.4}] th[{:.4},{:.4}] zeros={} (w/2pi={:.3}) lost={:.1}",sa,sb,ta,tb,z,w/(2.0*std::f64::consts::PI),ml); }
       tot+=z; }}
     println!("TOTAL zeros={} worst_lost_digits={:.2}",tot,worst); }
   "meval"=>{ let r=mp::bval(aa,nn,f(4),f(5)); println!("argB={:.9} log|B|={:.9} lost_bits={:.1} k={} prec={}",r.im.atan2(r.re),r.lg,r.lost_bits,r.k,r.prec); }
   "mcount"=>{ let (s0,s1,ns,t0,t1,nt)=(f(4),f(5),f(6) as usize,f(7),f(8),f(9) as usize);
     let mut tot=0i64;
     for i in 0..ns { for j in 0..nt {
       let sa=s0+(s1-s0)*(i as f64)/(ns as f64); let sb=s0+(s1-s0)*((i+1) as f64)/(ns as f64);
       let ta=t0+(t1-t0)*(j as f64)/(nt as f64); let tb=t0+(t1-t0)*((j+1) as f64)/(nt as f64);
       let c=[C::n(sa,ta),C::n(sb,ta),C::n(sb,tb),C::n(sa,tb)]; let mut w=0.0; let mut ml=0.0f64; let mut nev=0usize;
       for e in 0..4 { w+=mwind(aa,nn,c[e],c[(e+1)%4],&mut ml,&mut nev); }
       let z=(w/(2.0*std::f64::consts::PI)).round() as i64;
       println!("cell s[{:.4},{:.4}] th[{:.4},{:.4}] zeros={} (w/2pi={:.3}) maxlostbits={:.0} nev={}",sa,sb,ta,tb,z,w/(2.0*std::f64::consts::PI),ml,nev);
       tot+=z; }}
     println!("TOTAL zeros={}",tot); }
   _=>{}
  }
}
