import sys; sys.path.insert(0,'..')
from jp_lib import *
mp.mp.dps=40
import json
poles=[mp.mpf(p[1]) for p in json.load(open('../r35rust/poles_40.json'))]
def gapless(q,N,rho=1):
    # source weight: q^b * rho (W_0 = rho in source), returns Psi, t1
    def run(beta):
        P=[mp.mpf(0)]*(N+1); A=mp.mpf(0); B=beta
        for b in range(1,N+1):
            p=2*q**b*(rho*q**b+q**b*A+B); P[b]=p; A+=p; B-=q**b*p
        return P,B
    P0,B0=run(mp.mpf(0)); P1,B1=run(mp.mpf(1)); t=-B0/(B1-B0)
    return [P0[b]+t*(P1[b]-P0[b]) for b in range(N+1)], t
for m in range(1,9):
  q=poles[m-1]; N=Nfor(q); R,Bend=travel_null(q,N); x=mp.sqrt(q)
  for rho in (1,mp.mpf('0.7')):
    Psi,t1=gapless(q,N,rho)
    for yl,g in (('1',q/(1-q)),('q',q/(1-q*q))):
      if rho!=1 and yl=='q': continue
      B0=1/(1-g*t1); P=[B0*p for p in Psi]
      mu=mu_vec(q,P,N); E=extra_vec(q,P,N)
      # direct junction term weight B0 (empty run weight 1 in direct term)
      mu=[mu[s]+B0*x**(2*s+1) for s in range(N)]; E=[E[s]+B0*(x**(2*s)+x**(2*s+2)) for s in range(N)]
      C=sum(mu[s]*R[s] for s in range(N)); A=sum(E[s]*R[s] for s in range(N))
      R0=R[0]
      if rho==1:
        pred=B0*(1+x)*R0/(1-q)*(t1+(1+x)/(2*x)); predE=B0*R0*(1+t1)/(1-q)
      else:
        # direct weight 1, source weight rho: normalise Psi-> Psi/rho so source 1 and Psi_0=1/rho
        r=1/rho; F0=r+t1/rho
        FR=R0/(1-q)*(F0-r/2+(r-1)*(1-2*q)/(2*q)); FpR=R0*(r-(r-1)*q)/(2*(1-q))
        pred=B0*rho*(1+x)*(FR+FpR/x); predE=B0*rho*(FR+FpR)
      print(m,yl,'rho',rho,'q',mp.nstr(q,12),'t1',mp.nstr(t1,10),'(1-x)/2x',mp.nstr((1-x)/(2*x),10),'lamR',mp.nstr(A+2*C,15),'rel err',mp.nstr((A+2*C-pred)/pred,3),mp.nstr((A-predE)/predE,3),'E/2mu',mp.nstr(A/(2*C),10),'Bend',mp.nstr(Bend,3))
