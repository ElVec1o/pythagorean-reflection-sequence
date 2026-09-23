from mpmath import *
mp.dps=20
c0=mpc(-2,2); Lw=log(c0); th=atan(pi/(6*log(2))); e=exp(-1j*th)
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
w=1j*(4-sqrt(15)); x0=-(log(w)-2j*pi)/4; xm=x0-1j*pi/2
print('x0',x0,'xm',xm)
print('T0',re(Phi(x0)*e),'Tm',re((Phi(xm)-1j*pi*xm)*e))
print("Phi' at x0",diff(Phi,x0),' at xm with -i pi:',diff(Phi,xm)-1j*pi)
# all saddles of Phi + i pi n x in a box, with heights
for n in range(-3,4):
  sols=set()
  for a in [0.1,0.3,0.5,0.8,1.2]:
    for b in [-2,-1.5,-1,-0.5,0,0.5,1,1.5]:
      try:
        z=findroot(lambda x: diff(Phi,x)+1j*pi*n,mpc(a,b))
        if re(z)>0.02 and abs(im(z))<2.5: sols.add((round(float(re(z)),6),round(float(im(z)),6)))
      except: pass
  for s in sorted(sols):
    z=mpc(*s); print(n,s,'height',nstr(re((Phi(z)+1j*pi*n*z)*e),6))
