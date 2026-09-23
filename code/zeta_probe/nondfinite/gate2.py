import mpmath as mp
mp.mp.dps=40
def ser(q,sh):
    s=mp.mpf(1); poch=mp.mpf(1); a=-2*(1-q)
    for k in range(1,600):
        poch*=(1-q**(2*k-1))*(1-q**(2*k)); t=a**k*q**(k*k+sh*k)/poch; s+=t
        if abs(t)<mp.mpf(10)**-45 and k>5: break
    return s
def Y3(q):
    s=0; p1=mp.mpf(1); p2=mp.mpf(1)
    for k in range(600):
        t=(-2)**k*(1-q)**k*q**(k*k+3*k)/(p1*p2); s+=t
        p1*=(1-q**(2*k+2)); p2*=(1-q**(5+2*k))
        if abs(t)<mp.mpf(10)**-45 and k>5: break
    return s
Se=lambda q: ser(q,1); B=lambda q: ser(q,0)
DU=lambda q:(1-q*q)*(1-q**3)*Se(q)-2*q**4*Y3(q)
DV=lambda q:(1-q)*(1-q**3)*Se(q)-2*q**4*Y3(q)
for name,f,gs in [('Se',Se,[0.6096,0.93,0.97]),('DU',DU,[0.541,0.9145,0.9685]),('DV',DV,[0.5205,0.914,0.9685]),('B',B,[0.4494,0.9135,0.968])]:
    for g in gs:
        r=mp.findroot(f,mp.mpf(g)); print(name, mp.nstr(r,15), 'x=+-', mp.nstr(mp.sqrt(r),10), ' Se(r)=',mp.nstr(Se(r),5))
