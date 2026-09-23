# HEURISTIC/floating point: t1, gate factors and pairing factors at the zeros of B near q=i
from mpmath import *
mp.dps=30
c0=mpc(-2,2); Lw=log(c0)
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
w=1j*(4-sqrt(15)); x0=-(log(w)-2j*pi)/4; xm=x0-1j*pi/2
def amp(x):
  z=exp(-2*x); Cp=log(1-1j*z)/4-log(1+1j*z)/4-log(1-z)/2
  return exp(x*(-1+1j)/2+Cp)*(1+1j*c0*z/((1-1j*z)*(1+z)))
dV=(Phi(xm)-1j*pi*xm)-Phi(x0); rho=amp(xm)/amp(x0)
def ser(q,sh):
  s=mpc(0);poch=mpc(1);aa=-2*(1-q);k=0;big=mpf(1)
  while True:
    if k>0: poch*=(1-q**(2*k-1))*(1-q**(2*k))
    term=aa**k*q**(k*k+sh*k)/poch; s+=term; big=max(big,abs(term))
    if k>10 and abs(term)<mpf(10)**(-mp.dps-5)*big: return s
    k+=1
for j in [5,10,20,40]:
  mp.dps=30+int(8*j/5)
  u=(log(-1/rho)+2j*pi*j)/dV
  if re(u)<0: u=(log(-1/rho)-2j*pi*j)/dV
  t=findroot(lambda tt:ser(1j*exp(-tt),0),1/u)
  q=1j*exp(-t); Se=ser(q,1); Sm=ser(q,-1); t1=-(1+Sm/Se)/2
  gV=q/(1-q); gU=q/(1-q*q)
  out=[f'j={j} t={nstr(t,6)} t1={nstr(t1,8)} 1-gUt1={nstr(1-gU*t1,6)} 1-gVt1={nstr(1-gV*t1,6)}']
  for x in [sqrt(q),-sqrt(q)]:
    out.append(f' x={nstr(x,5)} P1fac={nstr(t1+(1+x)/(2*x),6)} Pqfac={nstr(t1*(1-x+q)/(1+q)+1/(2*x),6)}')
  print('\n'.join(out),flush=True)
