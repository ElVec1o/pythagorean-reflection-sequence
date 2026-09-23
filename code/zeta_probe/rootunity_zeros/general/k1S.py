import sys; sys.argv=['x','1','3']
exec(open('k1.py').read().split('a,N=int')[0])
from math import gcd
mp.dps=30
worst=[]
for N in range(3,61):
  for a in range(1,N//2+1):
    if gcd(a,N)!=1: continue
    z=exp(2j*pi*a/N)
    if log(abs(2*(1-z)))<0.05: continue
    z,L,w,xs,A,V,Phi=setup(a,N)
    n0=0 if (N%2==1 or N%4==0) else 1
    x=xs+1j*pi*n0/N; terms=[]
    for r in range(N):
      pr=z**(r*r)*exp(-2j*pi*n0*r/N)
      for j in range(1,N+1):
        d=(2*r-j)%N; pr*=(1-z**j*exp(-2*x))**(-(mpf(1)/2-mpf(d)/N))
      terms.append(pr)
    S=abs(fsum(terms)); M=sqrt(fsum(abs(u)**2 for u in terms))
    worst.append((float(S/M),a,N))
worst.sort()
print('smallest |S|/l2norm(terms):',worst[:8]); print('largest:',worst[-3:]); print('count',len(worst))
