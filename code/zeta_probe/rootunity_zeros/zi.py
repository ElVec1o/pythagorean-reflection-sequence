from mpmath import mp, mpf, mpc, exp, log, pi, findroot, arg, nstr, atan, polylog
import json
mp.dps=40
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
z=1j
dV=pi**2/8-1j*3*pi/4*log(2)
print('predicted theta_i =', atan(pi/(6*log(2)))*180/pi, ' predicted step of 1/t:', nstr(-2j*pi/dV,8))
R=[complex(a,b) for a,b in json.load(open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/nondfinite/roots_hi.json'))]
cand=[w for w in R if abs(w-1j)<0.25]
ts=[]
for w in cand:
    t=-log(w/z)
    if 25<float(arg(t))*180/pi<50: ts.append(t)
ts.sort(key=lambda t:-abs(t))
t=findroot(lambda tt: B(z*exp(-tt)), ts[0]); tl=[t]
t=findroot(lambda tt: B(z*exp(-tt)), ts[1]); tl.append(t)
for j in range(14):
    g=1/(2/tl[-1]-1/tl[-2]) if len(tl)>2 else 1/(1/tl[-1]-2j*pi/dV)
    tl.append(findroot(lambda tt: B(z*exp(-tt)), g))
for i,t in enumerate(tl):
    d = (1/tl[i]-1/tl[i-1]) if i>0 else 0
    print(i,'t=',nstr(t,10),' arg t=',nstr(arg(t)*180/pi,7),' d(1/t)=',nstr(d,8),' |q|=',nstr(abs(exp(-t)),6))
json.dump([[float(t.real),float(t.imag)] for t in tl],open('zi_t.json','w'))
