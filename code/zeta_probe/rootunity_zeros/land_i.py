import numpy as np
th=np.arctan(np.pi/(6*np.log(2))); r=0.01; t=r*np.exp(1j*th); p=np.exp(-t); q=1j*p
a=-2*(1-q); N=np.arange(0,20000)
lp4=p**(4*N)
def lpoch(z): return np.sum(np.log(1-z*lp4))
lnorm=np.sum(np.log(1-q**np.arange(1,40000)))  # log (q;q)_inf
def lfe(s): return 2*s*np.log(a)-4*t*s*s+sum(lpoch(1j**j*p**(4*s+j)) for j in range(1,5))-lnorm
def lfo(s): return (2*s+1)*np.log(a)+np.log(1j)-t*(2*s+1)**2+sum(lpoch(1j**j*p**(4*s+j)) for j in range(3,7))-lnorm
# check interpolation against direct b_k
def b(k):
    v=a**k*q**(k*k)
    for m in range(1,2*k+1): v/= (1-q**m)
    return v
for k in range(6):
    f=np.exp(lfe(k//2)) if k%2==0 else np.exp(lfo((k-1)//2))
    print(k,b(k),f)
print('f_e(-1),f_o(-1):',abs(np.exp(lfe(-1.0+0j))),abs(np.exp(lfo(-1.0+0j))))
# landscape in x=k t: even branch
print('x grid: rows Im x, cols Re x ; value r*log|f_e|')
xs=np.linspace(-1.2,1.2,25); ys=np.linspace(-1.6,1.0,27)
for y in ys[::-1]:
    row=[]
    for xr in xs:
        x=xr+1j*y; s=x/(2*t)
        try: row.append(r*lfe(s).real)
        except: row.append(np.nan)
    print(f'{y:5.2f} '+' '.join(f'{v:6.2f}' for v in row))
