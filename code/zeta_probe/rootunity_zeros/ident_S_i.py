# ident_S_i.py -- Room J step (T), VERIFIED (floating point): the contour identity behind the exact split of
# S_pm = sum_k b_k q^{pm k} near q=i: on each branch sum_s (-1)^s G(s) = int_lower G e^{-i pi s}/(1-e^{-2 pi i s})
# + int_upper G e^{i pi s}/(1-e^{2 pi i s}), paths leaving a half-integer s_c<0 (as in ident.py for B).
from mpmath import *
exec(open(__file__.replace('ident_S_i.py','ident.py')).read().split("for r in")[0])
def Sdir(sg):
  s=mpc(0); poc=mpc(1); k=0
  while True:
    if k>0: poc*=(1-q**(2*k-1))*(1-q**(2*k))
    term=a**k*q**(k*k+sg*k)/poc; s+=term; k+=1
    if k>30 and abs(term)<mpf(10)**(-50): return s
def contS(G,sc,phi=0.35):
  lo=lambda rho: G(sc+rho*exp(-1j*phi))*exp(-1j*pi*(sc+rho*exp(-1j*phi)))/(1-exp(-2j*pi*(sc+rho*exp(-1j*phi))))*exp(-1j*phi)
  up=lambda rho: G(sc+rho*exp(1j*phi))*exp(1j*pi*(sc+rho*exp(1j*phi)))/(1-exp(2j*pi*(sc+rho*exp(1j*phi))))*exp(1j*phi)
  R=12/abs(t)**0.5+abs(sc)*2
  return quad(lo,linspace(0,R,12))+quad(up,linspace(0,R,12))
for r in [0.2,0.1]:
  setup(r)
  sc=mpf(round(float(-0.32/abs(t))))-0.5
  for sg in [1,-1]:
    Ge=lambda s: fe(s)*exp(-sg*2*s*t)
    Go=lambda s: sg*1j*fo(s)*exp(-sg*(2*s+1)*t)
    I=contS(Ge,sc)+contS(Go,sc)
    print('r',r,'S%s direct'%('+' if sg>0 else '-'),nstr(Sdir(sg),15),' contour',nstr(I,15),' rel',nstr(abs(I/Sdir(sg)-1),3),flush=True)
