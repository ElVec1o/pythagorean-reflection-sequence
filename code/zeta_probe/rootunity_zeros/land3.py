# Landscape inequalities at theta=theta1, r1=0.05 with an a-priori Lipschitz bound (float64 evaluation).
# W_n(x)=Re((Phi(x)+2 pi i n x) e^{-i theta}); need W < T=Phi0 cos(theta1) on each segment.
# Lipschitz along a segment (|dx/du|=len): |W'| <= |Phi'(x)|+2pi|n|,
#   |Phi'(x)| <= L + 2|x| + |log(1-e^{-4x})| <= L + 2 max|x| + max(-log(1-v),log2) + pi/2,  v=max|e^{-4x}|.
import numpy as np
L=np.log(4.0); th=np.arctan(np.pi/L); r1=0.05
def Li2(z):
    out=np.zeros_like(z); p=np.ones_like(z)
    for n in range(1,1601):
        p=p*z; out+=p/(n*n)
    return out
def Phi(x): return x*L-x*x-Li2(np.exp(-4*x))/4+np.pi**2/24
x0=-np.log(np.sqrt(5)-2)/2; Phi0=Phi(np.array([x0+0j]))[0].real; T=Phi0*np.cos(th)
print('theta1=%.10f deg  Phi0=%.12f  T=%.12f'%(np.degrees(th),Phi0,T))
xA=r1*np.exp(1j*th); e=np.exp(-1j*th); N=200000; u=np.linspace(0,1,N+1)
segs={'arc  (n=0) r1 e^{i phi}, phi in[0,th]':(0,r1*np.exp(1j*th*u),r1*th),
      'C1   (n=1) xA+iy, y in[0,pi]':(1,xA+1j*np.pi*u,np.pi),
      'C-   (n=-1) xA-iy, y in[0,pi]':(-1,xA-1j*np.pi*u,np.pi),
      'C+   (n=2) xA+iy, y in[0,2pi]':(2,xA+2j*np.pi*u,2*np.pi)}
for name,(n,x,length) in segs.items():
    W=((Phi(x)+2j*np.pi*n*x)*e).real
    v=np.exp(-4*x.real.min()); lip=L+2*np.abs(x).max()+max(-np.log(1-v),np.log(2))+np.pi/2+2*np.pi*abs(n)
    h=length/N; ub=W.max()+lip*length*(1.0/N)/2
    print('%-40s max W - T = %+.5f at u=%.4f ; Lipschitz %.1f, grid slack %.2e ; certified bound W-T <= %+.5f'%(name,W.max()-T,u[np.argmax(W)],lip,lip*h/2,ub-T))
# E+ remainder along the ray, E- remainder along the real axis (quasi-periodic shifts)
r=np.linspace(r1,12,N+1); x=r*np.exp(1j*th)
W=(Phi(x)*e).real+((-4*np.pi**2+2j*np.pi*L)*e).real
print('ray (E+ remainder): max W - T = %+.4f'%(W.max()-T))
xr=np.linspace(r1,12,N+1)+0j
W=(Phi(xr)*e).real+((-np.pi**2-1j*np.pi*L)*e).real
print('real axis (E- remainder): max W - T = %+.4f'%(W.max()-T))
c=r1*1.12*np.log(4*np.e/(1.8*r1*1.12))
print('head exponent c(r1)=%.4f  vs T=%.4f'%(c,T))
