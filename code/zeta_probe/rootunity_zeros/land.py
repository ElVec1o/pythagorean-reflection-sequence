# landscape inequalities for the zeta=-1 proof (float, dense grids)
from mpmath import mp, mpf, mpc, polylog, exp, log, pi, re, im, atan, sqrt, cos, sin, findroot
mp.dps=20
L=log(4)
Phi=lambda x: x*L-x*x-polylog(2,exp(-4*x))/4+pi**2/24
x0=-log(sqrt(5)-2)/2; Phi0=Phi(x0)
th1=atan(pi/L)
print('x0=',x0,'Phi0=',Phi0,'theta1(deg)=',th1*180/pi, 'Phi0*cos th1=',Phi0*cos(th1))
def W(n,x,th): return re((Phi(x)+2j*pi*n*x)*exp(-1j*th))
for dth in [-0.06,0,0.06]:
    th=th1+dth; T=Phi0*cos(th); worst={}
    for r1 in [0.045,0.05,0.055]:
        xA=r1*exp(1j*th)
        N=400
        worst.setdefault('arc',-99); worst.setdefault('C1',-99); worst.setdefault('C-',-99); worst.setdefault('C+',-99); worst.setdefault('ray',-99)
        for i in range(N+1):
            u=mpf(i)/N
            worst['arc']=max(worst['arc'],W(0,r1*exp(1j*th*u),th)-T)
            worst['C1']=max(worst['C1'],W(1,xA+1j*pi*u,th)-T)
            worst['C-']=max(worst['C-'],W(-1,xA-1j*pi*u,th)-T)
            worst['C+']=max(worst['C+'],W(2,xA+2j*pi*u,th)-T)
            r=r1+u*6
            worst['ray']=max(worst['ray'],W(0,r*exp(1j*th),th)+re((-4*pi**2+2j*pi*L)*exp(-1j*th))-T)
    print('dth=%+.2f T=%.4f'%(dth,T), {k:float(v) for k,v in worst.items()}, ' ReLam=',float(re((-pi**2+1j*pi*L)*exp(-1j*th))))
