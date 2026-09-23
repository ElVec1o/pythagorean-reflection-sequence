from mpmath import mp, mpf, mpc, exp, log, pi, nstr
mp.dps=60
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
for t in [0.2,0.1,0.05,0.025,0.0125]:
    b=B(1j*exp(-t)); print(t,' t*log B(i e^{-t}) =',nstr(t*log(b),10))
