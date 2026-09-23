# Lipschitz-controlled float check of landscape inequalities (zeta=-1), theta in theta1 +- 0.02, r1 in [0.045,0.055]
import numpy as np
L=np.log(4.0); th1=np.arctan(np.pi/L)
n_=np.arange(1,1201,dtype=float)
def Li2(z):
    z=np.asarray(z,dtype=complex); out=np.zeros_like(z); p=np.ones_like(z)
    for n in n_:
        p=p*z; out+=p/(n*n)
    return out  # tail < |z|^1201/(1201^2 (1-|z|)) < 1e-40 for |z|<=0.93
def Phi(x): return x*L-x*x-Li2(np.exp(-4*x))/4+np.pi**2/24
def dPhi(x): return L-2*x-np.log(1-np.exp(-4*x))
x0=-np.log(np.sqrt(5)-2)/2; Phi0=Phi(np.array([x0]))[0].real
print('Phi0',Phi0,'theta1',np.degrees(th1))
N=40000
res={}
for th in th1+np.linspace(-0.005,0.005,5):
  T=Phi0*np.cos(th); e=np.exp(-1j*th)
  for r1 in [0.045,0.05,0.055]:
    xA=r1*np.exp(1j*th); u=np.linspace(0,1,N+1)
    segs={'arc':(0,r1*np.exp(1j*th*u),r1*th),'C1':(1,xA+1j*np.pi*u,np.pi),'C-':(-1,xA-1j*np.pi*u,np.pi),'C+':(2,xA+2j*np.pi*u,2*np.pi)}
    for name,(n,x,length) in segs.items():
        W=((Phi(x)+2j*np.pi*n*x)*e).real
        lip=np.max(np.abs(dPhi(x)))+2*np.pi*abs(n)+1.0   # +1 slack for between-grid variation of |dPhi|
        h=length/N
        bound=W.max()+lip*h/2-T
        res[name]=max(res.get(name,-99),bound)
        imax=np.argmax(W); res[name+'_argmax_u']=u[imax]
    r=r1+np.linspace(0,8,N+1); x=r*np.exp(1j*th)
    W=(Phi(x)*e).real+((-4*np.pi**2+2j*np.pi*L)*e).real
    res['ray']=max(res.get('ray',-99),W.max()-T)
print(res)
