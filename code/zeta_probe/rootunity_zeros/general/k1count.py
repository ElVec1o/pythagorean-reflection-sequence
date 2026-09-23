# argument-principle count of zeros of B(zeta e^{-t}) in annular sector r1<|t|<r2, |arg t|<thmax
from mpmath import *
import sys
a,N=int(sys.argv[1]),int(sys.argv[2]); r1,r2=mpf(sys.argv[3]),mpf(sys.argv[4]); mp.dps=int(sys.argv[5])
thm=mpf(sys.argv[7] if len(sys.argv)>7 else 85)*pi/180; z=exp(2j*pi*a/N)
def Bser(q):
  s=mpc(1);poch=mpc(1);aa=-2*(1-q);k=1;big=mpf(1)
  while True:
    poch*=(1-q**(2*k-1))*(1-q**(2*k)); term=aa**k*q**(k*k)/poch; s+=term; big=max(big,abs(term))
    if k>10 and abs(term)<mpf(10)**(-mp.dps+3)*big: return s,big
    k+=1
path=[]
M=int(sys.argv[6]) if len(sys.argv)>6 else 400
for i in range(M+1): path.append(r1*exp(1j*(-thm+2*thm*i/M)))
for i in range(1,M+1): path.append((r1+(r2-r1)*i/M)*exp(1j*thm))
for i in range(1,M+1): path.append(r2*exp(1j*(thm-2*thm*i/M)))
for i in range(1,M+1): path.append((r2-(r2-r1)*i/M)*exp(-1j*thm))
def val(t): return Bser(z*exp(-t))
tot=0; prev=val(path[0]); maxbig=prev[1]; minabs=abs(prev[0])
def walk(t0,t1,v0,v1,depth=0):
  global maxbig,minabs
  d=arg(v1[0]/v0[0])
  if abs(d)<0.5 or depth>12: return d
  tm=(t0+t1)/2; vm=val(tm); maxbig=max(maxbig,vm[1]); minabs=min(minabs,abs(vm[0]))
  return walk(t0,tm,v0,vm,depth+1)+walk(tm,t1,vm,v1,depth+1)
for i in range(1,len(path)):
  cur=val(path[i]); maxbig=max(maxbig,cur[1]); minabs=min(minabs,abs(cur[0]))
  tot+=walk(path[i-1],path[i],prev,cur); prev=cur
print('%d/%d r in [%s,%s] zeros=%s  max|b_k|=%s min|B| on contour=%s'%(a,N,r1,r2,nstr(tot/(2*pi),6),nstr(maxbig,3),nstr(minabs,3)))
