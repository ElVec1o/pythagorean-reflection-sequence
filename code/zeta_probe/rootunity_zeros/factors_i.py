# factors_i.py -- Room J step (T): interval-arithmetic (mpmath.iv) enclosures of the limit values at q=i,
# t1* = ((sqrt15-3) - (sqrt15+3) i)/12, x = +-e^{i pi/4}; certifies that every factor is non-zero.
# Also re-checks the closed-form constants of step (L) at 50 digits (floating point).
from mpmath import iv, mp, mpc, sqrt, log, exp, pi, polylog, nstr
iv.prec=80
s15=iv.sqrt(15); s2=iv.sqrt(2)
class Z:
  def __init__(s,a,b=0): s.a=iv.mpf(a); s.b=iv.mpf(b)
  def __add__(s,o): o=o if isinstance(o,Z) else Z(o); return Z(s.a+o.a,s.b+o.b)
  __radd__=__add__
  def __sub__(s,o): o=o if isinstance(o,Z) else Z(o); return Z(s.a-o.a,s.b-o.b)
  def __rsub__(s,o): return Z(o)-s
  def __mul__(s,o): o=o if isinstance(o,Z) else Z(o); return Z(s.a*o.a-s.b*o.b,s.a*o.b+s.b*o.a)
  __rmul__=__mul__
  def inv(s): d=s.a**2+s.b**2; return Z(s.a/d,-s.b/d)
  def __truediv__(s,o): o=o if isinstance(o,Z) else Z(o); return s*o.inv()
  def __rtruediv__(s,o): return Z(o)*s.inv()
  def absl(s): return (s.a**2+s.b**2).a   # lower bound of |z|^2
  def __repr__(s): return '[%s] + i[%s]'%(nstr(s.a.mid,10),nstr(s.b.mid,10))
I=Z(0,1); q=I
t1=Z((s15-3)/12,-(s15+3)/12)
gU=q/(1-q*q); gV=q/(1-q)
F={'1-gU t1':1-gU*t1,'1-gV t1':1-gV*t1}
ok=True
for sg in (1,-1):
  x=Z(sg/s2,sg/s2)
  F['t1+(1+x)/(2x), x=%+de^{i pi/4}'%sg]=t1+(1+x)/(2*x)
  F['t1(1-x+q)/(1+q)+1/(2x), x=%+de^{i pi/4}'%sg]=t1*(1-x+q)/(1+q)+1/(2*x)
  F['2q(1+x)/(1-q), x=%+de^{i pi/4}'%sg]=2*q*(1+x)/(1-q)
  F['(1+x)/(1-x), x=%+de^{i pi/4}'%sg]=(1+x)/(1-x)
  B0=1/(1-gU*t1)
  F['Pi_1 limit, x=%+de^{i pi/4}'%sg]=2*q*(1+x)/(1-q)*(t1+(1+x)/(2*x))/(1-gV*t1)
  F['Pi_q limit, x=%+de^{i pi/4}'%sg]=2*q*B0*(1+x)/(1-x)*(t1*(1-x+q)/(1+q)+1/(2*x))
for k,v in F.items():
  l=v.absl(); good=l>0; ok&=good
  print('%-44s = %s   |.|^2 >= %s  %s'%(k,v,nstr(l,6),'NONZERO' if good else 'FAIL'))
print('ALL FACTORS NONZERO' if ok else 'FAILED')
# closed-form constants of step (L), 50 digits
mp.dps=50
c0=mpc(-2,2); Lw=log(c0); phi=(1+sqrt(5))/2
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
Cp=lambda x: log(1-1j*exp(-2*x))/4-log(1+1j*exp(-2*x))/4-log(1-exp(-2*x))/2
Cm=lambda x: log(1+1j*exp(-2*x))/4-log(1-1j*exp(-2*x))/4-log(1+exp(-2*x))/2
g=lambda x,C: exp(-(1-1j)*x/2+C(x))
x0=log(4+sqrt(15))/4+3j*pi/8; xm=x0-1j*pi/2; y0=x0-1j*pi/4
chk={'i g-/g+ (x0) - i phi':1j*g(x0,Cm)/g(x0,Cp)-1j*phi,'-i g-/g+ (xm) + i/phi':-1j*g(xm,Cm)/g(xm,Cp)+1j/phi,
     'i g-/g+ (y0) - e^{2 pi i/3}':1j*g(y0,Cm)/g(y0,Cp)-exp(2j*pi/3),
     'rho - e^{(1-i)pi/4}':(g(xm,Cp)*(1-1j/phi))/(g(x0,Cp)*(1+1j*phi))-exp((1-1j)*pi/4),
     'dV - (pi^2/8 - 3 i pi log2/4)':(Phi(xm)-1j*pi*xm-Phi(x0))-(pi**2/8-0.75j*pi*log(2)),
     'S-/S+ limit - (3+sqrt15)(-1+i)/6':exp(2*y0)*(1+exp(2j*pi/3))/(1-exp(2j*pi/3))-(3+sqrt(15))*(-1+1j)/6}
for k,v in chk.items(): print('%-40s |.| = %s'%(k,nstr(abs(v),3)))
