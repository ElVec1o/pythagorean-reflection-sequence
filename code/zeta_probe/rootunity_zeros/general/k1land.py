import sys; sys.argv=['x','1','3']
exec(open('k1.py').read().split('a,N=int')[0])
from math import gcd
print('a/N  ell=log(4sin)  |w|  Re x*  |S*|/max|class|   rays: (theta,T,Tcont) for the 3 most central')
for N in list(range(3,17))+[20,24,30]:
  for a in range(1,N//2+1):
    if gcd(a,N)!=1: continue
    z,L,w,xs,A,V,Phi=setup(a,N)
    ell=log(abs(2*(1-z)))
    surv=[n for n in range(-3*N,3*N+1) if abs(A(n))>1e-9*abs(A(0 if N%2 or N%4==0 else 1))]
    rays=[]
    for i in range(len(surv)-1):
      n1,n2=surv[i],surv[i+1]; dV=V(n2)-V(n1); th=arg(1j*dV)
      if th>pi/2: th-=pi
      if th<-pi/2: th+=pi
      e=exp(-1j*th); T=re(V(n1)*e)
      if T>=max(re(V(n)*e) for n in surv)-1e-12: rays.append((float(th*180/pi),float(T),float(ell**2/(4*cos(th)))))
    rays.sort(key=lambda r:abs(r[0]))
    print('%d/%d ell=%.4f |w|=%.3g Rex*=%.4g minT=%.4f'%(a,N,ell,abs(w),re(xs),min(r[1] for r in rays)), ' '.join('(%.1f,%.4f,%.4f)'%r for r in rays[:3]),flush=True)
