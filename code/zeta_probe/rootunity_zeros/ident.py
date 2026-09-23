from mpmath import *
mp.dps=40
th=atan(pi/(6*log(2)))
def setup(r):
  global t,p,q,a,P,lnorm
  t=r*exp(1j*th); p=exp(-t); q=1j*p; a=-2*(1-q); P=p**4
  lnorm=log(qp(q,q))
def poch(z):
  s=mpc(1); w=z
  while abs(w)>mpf(10)**(-45):
    s*=(1-w); w*=P
  return s
def fe(s): return exp(2*s*log(a)-4*t*s*s-lnorm)*poch(1j*p**(4*s+1))*poch(-p**(4*s+2))*poch(-1j*p**(4*s+3))*poch(p**(4*s+4))
def fo(s): return exp((2*s+1)*log(a)-t*(2*s+1)**2-lnorm)*1j*poch(-1j*p**(4*s+3))*poch(p**(4*s+4))*poch(1j*p**(4*s+5))*poch(-p**(4*s+6))
def Bdir():
  s=mpc(0); poc=mpc(1); k=0
  while True:
    if k>0: poc*=(1-q**(2*k-1))*(1-q**(2*k))
    term=a**k*q**(k*k)/poc; s+=term; k+=1
    if k>30 and abs(term)<mpf(10)**(-50): return s
def contour(f,sc,phi=0.35):
  lo=lambda rho: f(sc+rho*exp(-1j*phi))/(1-exp(-2j*pi*(sc+rho*exp(-1j*phi))))*exp(-1j*phi)
  up=lambda rho: f(sc+rho*exp(1j*phi))*exp(2j*pi*(sc+rho*exp(1j*phi)))/(1-exp(2j*pi*(sc+rho*exp(1j*phi))))*exp(1j*phi)
  R=12/abs(t)**0.5+abs(sc)*2
  return quad(lo,linspace(0,R,12))+quad(up,linspace(0,R,12))
for r in [0.2,0.1]:
  setup(r)
  sc=-0.32/abs(t)   # x_c ~ -0.64 in x=2st => s = x/(2t) magnitude
  sc=mpf(round(float(sc)))-0.5
  I=contour(fe,sc)+contour(fo,sc)
  print('r',r,'s_c',sc,'B direct',nstr(Bdir(),15),' contour',nstr(I,15))
