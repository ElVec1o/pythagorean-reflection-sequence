import mpmath as mp, pickle, sys

def Sigma1T(tau):
    q=mp.e**(-tau); s=mp.mpf(0); k=0; poch2=(1-q**2); poch3=mp.mpf(1)
    tol=mp.mpf(10)**(-mp.mp.dps-12)
    while True:
        num=2*q*(-2*(1-q))**k*q**(k*k+2*k); term=num/(poch2*poch3); s+=term
        if k>5 and abs(term)<tol*abs(s): break
        if k>6000: break
        k+=1; poch2*=(1-q**2*q**(2*k)); poch3*=(1-q**3*q**(2*(k-1)))
    return s

def pole_tau(m):
    dps=70+int(0.95*m*m)
    mp.mp.dps=dps
    w0=(m+mp.mpf(1)/2)*mp.pi; tau0=2/w0**2
    f=lambda t: Sigma1T(t)-1
    t=mp.findroot(f,(tau0,tau0*mp.mpf('1.00005')),solver='secant',tol=mp.mpf(10)**(-(dps-12)))
    return t, dps

# We need w_m to high relative precision. dev=(m+1/2)pi - w. dev ~ c1/w ~ small.
# Store (m, w_m) as strings at high precision.
data={}
ms = list(range(3, 46))
for m in ms:
    t,dps = pole_tau(m)
    mp.mp.dps=dps
    w = mp.sqrt(2/t)
    data[m] = (mp.nstr(w, dps-10), dps)
    print(f"m={m} dps={dps} w={mp.nstr(w,20)}", flush=True)
with open('/tmp/poles_data.pkl','wb') as f:
    pickle.dump(data, f)
print("DONE saved", len(data), "poles")
