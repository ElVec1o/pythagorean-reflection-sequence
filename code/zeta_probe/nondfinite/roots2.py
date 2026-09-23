import cmath, math, sys, json
from ev import series
R0=float(sys.argv[1]); R=float(sys.argv[2]); nr=int(sys.argv[3]); nt=int(sys.argv[4])
f=lambda z: series(z,0,tol=1e-17)[0]
def newton(z):
    for it in range(80):
        h=1e-7
        fz=f(z); d=(f(z+h)-f(z-h))/(2*h)
        if d==0: return None
        dz=fz/d
        if abs(dz)>0.02: dz*=0.02/abs(dz)
        z-=dz
        if abs(z)>0.985: return None
        if abs(dz)<1e-12: return z
    return None
found=[]
for i in range(nr+1):
    r=R0+(R-R0)*i/nr
    for j in range(nt//2+1):
        z0=r*cmath.exp(1j*math.pi*(j+0.5)/(nt//2+1))
        z=newton(z0)
        if z is None: continue
        if z.imag<-1e-9: z=z.conjugate()
        if all(abs(z-w)>1e-7 for w in found): found.append(z)
json.dump([[z.real,z.imag] for z in found],open('roots_hi.json','w'))
tot=lambda Rr: sum((2 if w.imag>1e-9 else 1) for w in found if abs(w)<Rr)
for Rr in [0.9,0.93,0.94,0.95,0.96,0.97]: print(Rr,tot(Rr))
