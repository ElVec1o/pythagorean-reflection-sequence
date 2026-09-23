# K1 scoping: saddle family at zeta=e^{2 pi i a/N}; heights, amplitudes, dominant pairs, then true zeros.
from mpmath import *
import sys
mp.dps=30
def setup(a,N):
  z=exp(2j*pi*a/N); c=-2*(1-z); L=log(c); C=c**N
  bb=2+C; sq=sqrt(bb*bb-4); W1=(bb+sq)/2; W2=(bb-sq)/2; Wb=W1 if abs(W1)>abs(W2) else W2; ws=[1/Wb]; w=[u for u in ws if abs(u)<1][0]
  Phi=lambda x: x*L-x*x-polylog(2,exp(-2*N*x))/N**2+pi**2/(6*N**2)
  dPhi=lambda x: L-2*x-(2/mpf(N))*log(1-exp(-2*N*x))
  xs=None
  for m in range(2*N):
    x=-log(w)/(2*N)+1j*pi*m/N
    if abs(dPhi(x))<mpf(10)**-(mp.dps-8): xs=x
  lin=z/(1-z)
  def A(n):
    x=xs+1j*pi*n/N; s=0
    for r in range(N):
      pr=z**(r*r)*exp(-2j*pi*n*r/N)
      for j in range(1,N+1):
        d=(2*r-j)%N; pr*=(1-z**j*exp(-2*x))**(-(mpf(1)/2-mpf(d)/N))
      s+=pr
    return exp(x*lin)*s
  V=lambda n: Phi(xs+1j*pi*n/N)+2j*pi*n*(xs+1j*pi*n/N)/N
  return z,L,w,xs,A,V,Phi
def Bser(q):
  s=mpc(1);poch=mpc(1);aa=-2*(1-q);k=1;big=mpf(1)
  while True:
    poch*=(1-q**(2*k-1))*(1-q**(2*k)); term=aa**k*q**(k*k)/poch; s+=term; big=max(big,abs(term))
    if k>10 and abs(term)<mpf(10)**(-mp.dps+3)*big: return s
    k+=1
a,N=int(sys.argv[1]),int(sys.argv[2]); js=[int(u) for u in sys.argv[3:]]
z,L,w,xs,A,V,Phi=setup(a,N)
print('zeta=e^(2pi i %d/%d)'%(a,N),'w=',nstr(w,8),'x*=',nstr(xs,8),"Phi''=",nstr(-2-4*N*w/(1-w)/1,6) if False else '')
print(' log|2(1-z)|=',nstr(log(abs(2*(1-z))),8))
surv=[n for n in range(-2*N,2*N+1) if abs(A(n))>1e-12]
print(' surviving n in [-2N,2N]:',surv, ' vanishing:',[n for n in range(-2*N,2*N+1) if n not in surv])
rays=[]
for i1,n1 in enumerate(surv):
  for n2 in surv[i1+1:]:
    dV=V(n2)-V(n1); th=arg(1j*dV)
    if th>pi/2: th-=pi
    if th<-pi/2: th+=pi
    e=exp(-1j*th); h=[re(V(n)*e) for n in surv]; T=re(V(n1)*e)
    if T>=max(h)-1e-15: rays.append((float(th),n1,n2,T,dV))
for th,n1,n2,T,dV in sorted(rays):
  print('  ray th=%.4f deg pair (%d,%d) T=%s  dV=%s |A1/A2|=%s'%(th*180/pi,n1,n2,nstr(T,6),nstr(dV,6),nstr(abs(A(n1)/A(n2)),5)))
# zeros
for th,n1,n2,T,dV in sorted(rays):
  if abs(th)>80*pi/180: continue
  if not js: continue
  for j in js:
    lg=log(-A(n1)/A(n2))
    for jj in [j,-j]:
      u=(lg+2j*pi*jj)/dV
      if re(u)>0 and abs(arg(u)+th)<0.3: break
    t0=1/u
    mp.dps=int(30+2.0*N/abs(t0)); 
    try:
      ts=findroot(lambda tt:Bser(z*exp(-tt)),(t0,t0*(1+mpf(10)**-5)),solver='secant',tol=mpf(10)**-20)
      print('   pair(%d,%d) j=%d t0=%s t*=%s |1/t*-1/t0|=%s spacing|2pi/dV|=%s'%(n1,n2,jj,nstr(t0,8),nstr(ts,8),nstr(abs(1/ts-u),4),nstr(2*pi/abs(dV),4)),flush=True)
    except Exception as ex: print('   fail',j,str(ex)[:60])
    mp.dps=30
