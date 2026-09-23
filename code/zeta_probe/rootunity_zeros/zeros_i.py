# zeros_i.py -- Room J, VERIFIED (floating point, adaptive precision): zeros of B near q=i against
# t0_j=(6 log2 + i pi)/(16 j + 6 - 2i), and t1 at the zeros against t1*=((sqrt15-3)-(sqrt15+3)i)/12.
from mpmath import *
import sys
def ser(q,sh):
  s=mpc(0);poch=mpc(1);aa=-2*(1-q);k=0;big=mpf(1)
  while True:
    if k>0: poch*=(1-q**(2*k-1))*(1-q**(2*k))
    term=aa**k*q**(k*k+sh*k)/poch; s+=term; big=max(big,abs(term))
    if k>10 and abs(term)<mpf(10)**(-mp.dps+5)*abs(s): return s
    k+=1
for j in [int(a) for a in sys.argv[1:]]:
  mp.dps=40
  t0=(6*log(2)+1j*pi)/(16*j+6-2j)
  mp.dps=int(40+1.6/abs(t0))
  t0=(6*log(2)+1j*pi)/(16*j+6-2j)
  ts=findroot(lambda tt:ser(1j*exp(-tt),0),(t0,t0*(1+mpf(10)**-4)),solver="secant",tol=mpf(10)**(-30))
  q=1j*exp(-ts); Se=ser(q,1); Sm=ser(q,-1); t1=-(1+Sm/Se)/2
  t1s=((sqrt(15)-3)-(sqrt(15)+3)*1j)/12
  print('j',j,'dps',mp.dps,'t*',nstr(ts,10),' |t*-t0| j^3 =',nstr(abs(ts-t0)*j**3,5),' arg t* deg',nstr(arg(ts)*180/pi,8),
        ' t1',nstr(t1,8),' (t1-t1*)/t*',nstr((t1-t1s)/ts,6),flush=True)
