import cmath, math, sys, json
from ev import series
sh=int(sys.argv[1]); R=float(sys.argv[2]); nr=int(sys.argv[3]); nt=int(sys.argv[4])
f=lambda z: series(z,sh)[0]
def newton(z):
    for it in range(60):
        h=1e-7*max(1,abs(z))
        fz=f(z); d=(f(z+h)-f(z-h))/(2*h)
        if d==0: return None
        dz=fz/d; z-=dz
        if abs(z)>0.995: return None
        if abs(dz)<1e-13: return z
    return None
found=[]
for i in range(1,nr+1):
    r=R*i/nr
    for j in range(nt):
        z0=r*cmath.exp(2j*math.pi*(j+0.5)/nt)
        z=newton(z0)
        if z is None or abs(z)>R+0.01: continue
        if all(abs(z-w)>1e-8 for w in found): found.append(z)
found.sort(key=abs)
json.dump([[z.real,z.imag] for z in found],open('roots_%d_%s.json'%(sh,R),'w'))
inside=[z for z in found if abs(z)<R]
print('found inside |q|<%g:'%R,len(inside))
for z in inside:
    k=abs(z); a=cmath.phase(z)/(2*math.pi)
    print('%.6f %+.6f  |q|=%.5f arg/2pi=%+.5f  |f|=%.1e'%(z.real,z.imag,k,a,abs(f(z))))
