# t1lim_i.py -- Room J step (T): the dominant saddle of S_pm at q=i, the limit of t1, and the
# gate/pairing factors in the limit. Floating point (VERIFIED against the exact series in zeros_i.py).
from mpmath import *
mp.dps=30
c0=mpc(-2,2); Lw=log(c0); th=atan(pi/(6*log(2)))
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
d2=lambda x: -2-4*exp(-8*x)/(1-exp(-8*x))
Cp=lambda x: log(1-1j*exp(-2*x))/4-log(1+1j*exp(-2*x))/4-log(1-exp(-2*x))/2
Cm=lambda x: log(1+1j*exp(-2*x))/4-log(1-1j*exp(-2*x))/4-log(1+exp(-2*x))/2
g=lambda x,C: exp(-(1-1j)*x/2+C(x))
y0=log(4+sqrt(15))/4+1j*pi/8
print("Phi'(y0)+i pi(-1/2) =",Lw-2*y0-log(1-exp(-8*y0))/2-1j*pi/2, "  Phi''(y0) =",d2(y0))
for nu in [-2.5,-1.5,-0.5,0.5,1.5]:
  x=y0+1j*pi*(nu+0.5)/2
  print('nu',nu,'saddle',nstr(x,8),'height',nstr(re((Phi(x)+1j*pi*nu*x)*exp(-1j*th)),10),' check Phi\'+i pi nu',nstr(abs(Lw-2*x-log(1-exp(-8*x))/2+1j*pi*nu),3))
Ry=1j*g(y0,Cm)/g(y0,Cp)
a=(sqrt(5)-sqrt(3))/2; w=(sqrt(15)-3)+1j*(sqrt(5)-sqrt(3))
print('R_y =',Ry,' |R_y|',abs(Ry),'  i w/|w| =',1j*w/abs(w))
ES=Phi(y0)-1j*pi*y0/2
pre=exp(1j*pi/8)/sqrt(-d2(y0))
AS=lambda sg: pre*exp(-sg*y0)*g(y0,Cp)*(1-sg*Ry)
print('E_S',ES,' A_S+',AS(1),' A_S-',AS(-1))
ratio=AS(-1)/AS(1); t1=-(1+ratio)/2
print('S-/S+ limit',ratio,'  t1 limit',t1)
q=1j; gU=q/(1-q*q); gV=q/(1-q)
print('1-gU t1',1-gU*t1,' 1-gV t1',1-gV*t1)
for x in [exp(1j*pi/4),-exp(1j*pi/4)]:
  B0=1/(1-gU*t1)
  P1=2*q*(1+x)/(1-q)*(t1+(1+x)/(2*x))/(1-gV*t1)
  Pq=2*q*B0*(1+x)/(1-x)*(t1*(1-x+q)/(1+q)+1/(2*x))
  print('x',nstr(x,6),' Pi_1',nstr(P1,10),' Pi_q',nstr(Pq,10),' t1+(1+x)/2x',nstr(t1+(1+x)/(2*x),8),' t1(1-x+q)/(1+q)+1/2x',nstr(t1*(1-x+q)/(1+q)+1/(2*x),8))
# exact-series check of S_pm = A_S(pm) e^{E_S/t}(1+O(t))
def ser(q,sh):
  s=mpc(0);poch=mpc(1);aa=-2*(1-q);k=0
  while True:
    if k>0: poch*=(1-q**(2*k-1))*(1-q**(2*k))
    term=aa**k*q**(k*k+sh*k)/poch; s+=term
    if k>20 and abs(term)<mpf(10)**(-mp.dps+5)*abs(s): return s
    k+=1
for r in [mpf('0.04'),mpf('0.02'),mpf('0.01')]:
  mp.dps=int(30+1.4/r); t=r*exp(1j*th); q=1j*exp(-t)
  out=[]
  for sg in [1,-1]:
    e=ser(q,sg)/(AS(sg)*exp(ES/t))-1; out.append('S%s/pred-1=%s (/t %s)'%('+' if sg>0 else '-',nstr(e,5),nstr(e/t,5)))
  print('r',r,' '.join(out),flush=True)
