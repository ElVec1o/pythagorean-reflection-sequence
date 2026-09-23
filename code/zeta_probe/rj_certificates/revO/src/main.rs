// Reviewer O: direct enumeration of Elt tuples (k,eps,delta,d) from the Lean definitions
// (CorrectedSpan.lRTrue / cTrue), NOT via BFS. Output: counts[sg][lR][c].
use std::env;
fn travel(k:i64,j:i64)->i64{ if 0<=j&&j<k {1} else if k<=j&&j<0 {-1} else {0} }
struct Ctx{k:i64,eps:i64,dl:bool,a:i64,b:i64,n:i64,d:Vec<i64>,cnt:Vec<Vec<u64>>}
impl Ctx{
 fn dd(&self,j:i64)->i64{ if j<self.a||j>self.b {0} else {self.d[(j-self.a) as usize]} }
 fn site(&self,s:i64)->(i64,bool){
   let va= if s==0 {1} else {0}; let vd= if s==self.k {1} else {0};
   let vl= if self.dl {0} else {vd}; let vr= if self.dl {vd} else {0};
   let al=self.dd(s-1)-va+self.eps*vl; let be=self.dd(s)-self.eps*vr;
   let ph=travel(self.k,s-1)+va-vl;
   (al.abs().max(be.abs()), al==0&&be==0&&ph==0)
 }
 fn mu(&self,j:i64)->i64{ let d=self.dd(j); let f=travel(self.k,j); if d==0&&f==0 {2} else {d.abs().max(f.abs())} }
 // DFS over edge index j (absolute), cost so far includes edges < j and sites <= j-1... we recompute at leaf with pruning by edge mu + site s=j (left of edge j) once d_{j-1},d_j known
 fn dfs(&mut self,j:i64,cost:i64){
   if cost>self.n {return;}
   if j>self.b {
     // end checks
     let occ=|c:&Ctx,e:i64| c.dd(e)!=0||travel(c.k,e)!=0;
     if self.a<0 && !occ(self,self.a) {return;}
     if self.b>=0 && !occ(self,self.b) {return;}
     let (sc,_)=self.site(self.b+1); let tot=cost+sc; if tot>self.n {return;}
     let mut c=0usize;
     for s in (self.a+1)..=(self.b) { if self.site(s).1 {c+=1;} }
     // shield
     let shield = self.k==0 && !self.dl && (self.a..0).all(|e| self.dd(e)==0) && (0..=self.b).any(|e| self.dd(e)!=0);
     if shield && self.site(0).1 {c+=1;}
     let sg= (self.k.signum()+1) as usize;
     self.cnt[sg*64 + tot as usize][c]+=1; return;
   }
   let f=travel(self.k,j); let idx=(j-self.a) as usize;
   let mut v= if f!=0 {1} else {0};
   while v<=self.n {
     for sgn in [1i64,-1] {
       if v==0 && sgn==-1 {continue;}
       self.d[idx]=sgn*v;
       let add=self.mu(j)+self.site(j).0;
       self.dfs(j+1,cost+add);
     }
     v+=2;
   }
   self.d[idx]=0;
 }
}
fn main(){
 let n:i64=env::args().nth(1).unwrap().parse().unwrap();
 let mut cnt=vec![vec![0u64;64];3*64];
 for k in -n..=n { for eps in [1i64,-1] { for dl in [false,true] {
   let amax=0.min(k); let bmin=(-1).max(k-1);
   for a in (amax-n)..=amax { for b in bmin..=(bmin+n) {
     if (b-a+1) > n {continue;}
     let w=(b-a+1).max(0) as usize;
     let mut c=Ctx{k,eps,dl,a,b,n,d:vec![0;w],cnt:std::mem::take(&mut cnt)};
     c.dfs(a,0); cnt=c.cnt;
   }}
 }}}
 for sg in 0..3 { for l in 0..=n as usize { for c in 0..64 { let v=cnt[sg*64+l][c]; if v>0 { println!("E {} {} {} {}",sg as i64-1,l,c,v);} } } }
}
