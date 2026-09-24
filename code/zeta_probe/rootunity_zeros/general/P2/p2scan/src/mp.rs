// multiprecision B(zeta e^{-t}) with rug (MPFR). Precision chosen adaptively from the measured cancellation.
use rug::{Complex, Float, float::Constant};
pub struct Res { pub re: f64, pub im: f64, pub lg: f64, pub lost_bits: f64, pub k: usize, pub prec: u32 }
fn bval_prec(a:i64,n:i64,tre:&Float,tim:&Float,prec:u32)->(Complex,f64,usize){
  let pi=Float::with_val(prec,Constant::Pi);
  let t=Complex::with_val(prec,(tre,tim));
  let zeta_pow=|j:i64|->Complex{ let r=(a*j).rem_euclid(n); let ang=Float::with_val(prec,&pi*2u32)*Float::with_val(prec,r)/Float::with_val(prec,n);
      let (s,c)=ang.sin_cos(Float::new(prec)); Complex::with_val(prec,(c,s)) };
  let zt:Vec<Complex>=(0..n).map(|r| zeta_pow(r)).collect(); // zeta^{r a}... index by (a*j mod n) -> use direct
  let zr=|j:i64|->&Complex{ &zt[((j).rem_euclid(n)) as usize] }; // zt[r] = e(a r/N)
  let p1=Complex::with_val(prec,-&t).exp(); // p=e^{-t}
  let p2=Complex::with_val(prec,&p1*&p1);
  let q=Complex::with_val(prec,zr(1)*&p1);
  let ct=Complex::with_val(prec,(Complex::with_val(prec,1)-&q)*(-2i32));
  let mut pj=p1.clone(); // p^{2k+1}
  let mut b=Complex::with_val(prec,1); let mut s=Complex::with_val(prec,1);
  let mut mx=0f64; let mut k:i64=0;
  loop{
    let j=2*k+1;
    let pj1=Complex::with_val(prec,&pj*&p1);
    let qj=Complex::with_val(prec,zr(j)*&pj); let qj1=Complex::with_val(prec,zr(j+1)*&pj1);
    let om=|z:&Complex,jj:i64,pp:&Complex|->Complex{ if (jj).rem_euclid(n)==0 { Complex::with_val(prec,1)-pp } else { Complex::with_val(prec,1)-z } };
    let d=Complex::with_val(prec,om(&qj,j,&pj)*om(&qj1,j+1,&pj1));
    b*= Complex::with_val(prec,&ct*&qj); b/=&d;
    s+=&b; k+=1;
    let lb=b.clone().abs().real().to_f64().ln(); if lb>mx{mx=lb;}
    let rr=Complex::with_val(prec,&ct*&qj).abs().real().to_f64()/d.clone().abs().real().to_f64();
    let ls=s.clone().abs().real().to_f64().ln();
    if k>10 && lb<mx-50.0 && lb<ls-45.0 && rr<0.5 {break;}
    pj=Complex::with_val(prec,&pj1*&p1);
    if k>100_000_000 {break;}
  }
  let _=p2;
  (s,mx,k as usize)
}
pub fn bval(a:i64,n:i64,tre:f64,tim:f64)->Res{
  let mut prec=128u32;
  loop{
    let (s,mx,k)=bval_prec(a,n,&Float::with_val(prec,tre),&Float::with_val(prec,tim),prec);
    let lg=s.clone().abs().real().to_f64().ln();
    let lost=(mx-lg).max(0.0)/std::f64::consts::LN_2;
    if lost+70.0 < prec as f64 || prec>200000 {
      let re=s.real().to_f64(); let im=s.imag().to_f64(); let m=(re*re+im*im).sqrt();
      // return normalized direction, log modulus via MPFR (safe from overflow)
      return Res{re:re/m,im:im/m,lg,lost_bits:lost,k,prec};
    }
    prec=((lost+140.0) as u32).max(prec*2);
  }
}
