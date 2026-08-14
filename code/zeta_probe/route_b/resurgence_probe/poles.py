import mpmath as mp

def Sigma1T(tau):
    q = mp.e**(-tau); s=mp.mpf(0); k=0
    poch2=(1-q**2); poch3=mp.mpf(1)
    tol=mp.mpf(10)**(-mp.mp.dps-10)
    while True:
        num=2*q*(-2*(1-q))**k*q**(k*k+2*k)
        term=num/(poch2*poch3); s+=term
        if k>5 and abs(term)<tol*abs(s): break
        if k>5000: break
        k+=1; poch2*=(1-q**2*q**(2*k)); poch3*=(1-q**3*q**(2*(k-1)))
    return s

def pole_tau(m, dps=None):
    if dps is None:
        # need guard digits ~ log10(maxterm) ~ m^2*0.5 ; plus working precision
        dps = 60 + int(0.9*m*m)
    mp.mp.dps = dps
    w0=(m+mp.mpf(1)/2)*mp.pi; tau0=2/w0**2
    f=lambda t: Sigma1T(t)-1
    return mp.findroot(f, (tau0, tau0*mp.mpf('1.0001')), solver='secant',
                       tol=mp.mpf(10)**(-(dps-15)))

if __name__=="__main__":
    for m in [3,4,5,8,12,20]:
        t=pole_tau(m); w=mp.sqrt(2/t); dev=(m+mp.mpf(1)/2)*mp.pi-w
        print(f"m={m:3d} dps={mp.mp.dps} w={mp.nstr(w,12):>14} dev*w={mp.nstr(dev*w,14)}")
