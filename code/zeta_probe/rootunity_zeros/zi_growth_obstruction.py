from mpmath import *
mp.dps=80
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s,big
th=atan(pi/(6*log(2)))
for r in [0.2,0.1,0.05,0.03]:
  for dth in [0,-0.2,0.2]:
    t=r*exp(1j*(th+dth)); b,big=B(1j*exp(-t))
    print(r,dth,'r log|B|',nstr(r*log(abs(b)),6),' r log big',nstr(r*log(big),6))
