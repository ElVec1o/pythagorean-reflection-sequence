import json, mpmath as mp
mp.mp.dps=40
def ser(q,sh):
    s=mp.mpc(1); poch=mp.mpc(1); a=-2*(1-q)
    for k in range(1,400):
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        t=a**k*q**(k*k+sh*k)/poch; s+=t
        if abs(t)<mp.mpf(10)**(-45) and k>5: break
    return s
B=lambda q: ser(q,0); Se=lambda q: ser(q,1)
def Y3(q):
    s=mp.mpc(0); p1=mp.mpc(1); p2=mp.mpc(1)
    for k in range(0,400):
        if k>0: p1*=(1-q**(2*k)); p2*=(1-q**(2*k+3))
        # (q^2;q^2)_k , (q^5;q^2)_k = prod_{i<k}(1-q^{5+2i})
        t=(-2)**k*(1-q)**k*q**(k*k+3*k)/(p1*p2); s+=t
        if abs(t)<mp.mpf(10)**(-45) and k>5: break
    return s
def Y3b(q):  # recompute (q^5;q^2)_k carefully
    s=mp.mpc(0); p1=mp.mpc(1); p2=mp.mpc(1)
    for k in range(0,400):
        t=(-2)**k*(1-q)**k*q**(k*k+3*k)/(p1*p2); s+=t
        p1*=(1-q**(2*k+2)); p2*=(1-q**(5+2*k))
        if abs(t)<mp.mpf(10)**(-45) and k>5: break
    return s
def krec(q,k0):
    A=lambda k: 2*q/(1-q**(k+1))
    C=lambda k: 2*q**(k+3)/(1-q**(k+2))-2*q**(k+2)/(1-q**(k+1))
    s=mp.mpc(0); pr=mp.mpc(1)
    for j in range(0,400):
        t=A(k0+2*j)*pr; s+=t
        pr*=C(k0+2*j)
        if abs(t)<mp.mpf(10)**(-45) and j>5: break
    return s
def refine(q):
    return mp.findroot(B, mp.mpc(q))
z=[complex(a,b) for a,b in json.load(open('roots_0_0.95.json'))]
z=[w for w in z if abs(w)<0.94 and w.imag>=-1e-12]
out=[]
print('# q*  | |q*|  | |Se| | |Sigma0| | |1-Sigma1 via krec| | t1 | |1-gU t1| | Pi_q(x=+sqrt) | Pi_q(x=-sqrt)')
for w in z:
    q=refine(w)
    if abs(mp.im(q))<1e-30: q=mp.mpc(mp.re(q),0)
    se=Se(q); P12=2*q**3/(1-q**3)*Y3b(q); t1=P12/se
    gU=q/(1-q**2); B0=1/(1-gU*t1)
    s0=krec(q,0); s1=krec(q,1)
    res=[]
    for sg in (1,-1):
        x=sg*mp.sqrt(q)
        Pi=2*q*B0*(1+x)/(1-x)*(t1*(1-x+q)/(1+q)+1/(2*x))
        res.append(Pi)
    print('%s | %.5f | %.3g | %.3g | %.1e | %s | %.3g | %.4g | %.4g'%(mp.nstr(q,12),abs(q),abs(se),abs(s0),abs(1-s1),mp.nstr(t1,5),abs(1-gU*t1),abs(res[0]),abs(res[1])))
