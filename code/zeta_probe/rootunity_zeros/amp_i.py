# amp_i.py -- Room J step (L), VERIFIED (floating point): two-saddle amplitudes of B near q=i and
# comparison with the exact series. A0 = e^{i pi/8}(-Phi''(x0))^{-1/2}[g_+(x0)+i g_-(x0)],
# Am = e^{i pi/8}(-Phi''(xm))^{-1/2}[g_+(xm)-i g_-(xm)], g_pm(x)=exp(-(1-i)x/2+C_pm(x)) (principal logs).
from mpmath import *
import sys
mp.dps=30
c0=mpc(-2,2); Lw=log(c0); th=atan(pi/(6*log(2)))
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
d2=lambda x: -2-4*exp(-8*x)/(1-exp(-8*x))
def Cp(x):
  z=exp(-2*x); return log(1-1j*z)/4-log(1+1j*z)/4-log(1-z)/2
def Cm(x):
  z=exp(-2*x); return log(1+1j*z)/4-log(1-1j*z)/4-log(1+z)/2
g=lambda x,C: exp(-(1-1j)*x/2+C(x))
x0=log(4+sqrt(15))/4+3j*pi/8; xm=x0-1j*pi/2
V0=Phi(x0); Vm=Phi(xm)-1j*pi*xm; dV=Vm-V0
pre=lambda x: exp(1j*pi/8)/sqrt(-d2(x))
A0=pre(x0)*(g(x0,Cp)+1j*g(x0,Cm)); Am=pre(xm)*(g(xm,Cp)-1j*g(xm,Cm))
print('Phi\'\'(x0)=',d2(x0),' = -2 - 4/(1-e^{8x0}) check', -2+4j*(4-sqrt(15))/(1+1j*(4-sqrt(15))) if False else '')
print('V0',V0,'Vm',Vm); print('dV',dV,' exact pi^2/8 - i 3pi/4 log2:',pi**2/8-0.75j*pi*log(2))
for nm,x,sg in [('x0',x0,1),('xm',xm,-1)]:
  z=exp(-2*x); R=1j*c0*z/((1-1j*z)*(1+z))
  print(nm,'i g-/g+ =',sg*1j*g(x,Cm)/g(x,Cp),' R(z)=',R)
print('A0',A0,'|A0|',abs(A0)); print('Am',Am,'|Am|',abs(Am)); rho=Am/A0; print('rho=Am/A0',rho,'|rho|',abs(rho))
if len(sys.argv)>1:
  def B(q):
    s=mpc(1); poch=mpc(1); aa=-2*(1-q); k=1
    while True:
      poch*=(1-q**(2*k-1))*(1-q**(2*k)); term=aa**k*q**(k*k)/poch; s+=term
      if k>20 and abs(term)<abs(s)*mpf(10)**(-25): return s
      k+=1
  for r in [mpf(s) for s in sys.argv[1:]]:
    for dd in [0,0.0005]:
      t=r*exp(1j*(th+dd))
      out=[]
      for dps in [int(20+1.2/r),int(40+1.4/r)]:
        mp.dps=dps; out.append(B(1j*exp(-t)))
      mp.dps=30
      pred=A0*exp(V0/t)+Am*exp(Vm/t)
      print('r',r,'dth',dd,'stable',nstr(abs(out[0]/out[1]-1),3),' B/pred-1 =',nstr(out[1]/pred-1,6),' /t:',nstr((out[1]/pred-1)/t,6),flush=True)
