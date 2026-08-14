"""
Clean Gevrey c_L growth check at a travel pole (robust moment expansion, no sympy Poly).
Growth of |c_L|/|c_{L-1}| => divergent loop series (Gevrey-1) => Q2 YES.
"""
import mpmath as mp
from math import factorial

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

def hcoeffs(kmax):
    H=[[0,1]]
    for _ in range(kmax-1):
        p=H[-1]; dp=[p[i]*i for i in range(1,len(p))]
        new=[mp.mpf(0)]*(len(dp)+2)
        for i,c in enumerate(dp):
            new[i+1]+=c; new[i+2]-=c
        H.append(new)
    return H

def heval(coeffs,g):
    s=mp.mpc(0)
    for i in range(len(coeffs)-1,-1,-1): s=s*g+coeffs[i]
    return s

KMAX=14; H=hcoeffs(KMAX)

def Wderivs(xi, tau, kmax=KMAX):
    q = mp.e**(-tau); e = mp.e**(1j*xi); a_list = [q**4, 2*(1-q)*q]
    Wv = -xi**2/(4*tau)
    for a in a_list: Wv -= poch_logsum(-a*e, q**2)
    Dk = [mp.mpc(0)]*(kmax+1); tol = mp.mpf(10)**(-(mp.mp.dps+12))
    for a in a_list:
        uu = a*e; p2 = q**2
        while abs(uu) > tol:
            g = uu/(1+uu)
            for k in range(1, kmax+1): Dk[k] += (1j)**k*heval(H[k-1],g)
            uu *= p2
    out = [Wv]
    for k in range(2, kmax+1):
        base = -1/(2*tau) if k == 2 else mp.mpf(0)
        out.append(base - Dk[k])
    return out, -(2*xi)/(4*tau) - Dk[1]

def saddle(tau):
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1],
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-28)

def loop_coeffs(d, Lmax=5):
    W = {k: d[k-1] for k in range(2, len(d))}
    A = -W[2]; s2 = 1/A
    maxk = 2*Lmax+2
    Pterms = {k: W[k]/mp.mpf(factorial(k)) for k in range(3, maxk+1) if k in W}
    result = {(0,0): mp.mpf(1)}; cur = {(0,0): mp.mpf(1)}
    for n in range(1, 2*Lmax+1):
        nxt = {}
        for (zp,lp),c in cur.items():
            for k,vk in Pterms.items():
                nlp = lp+(k-2)
                if nlp>2*Lmax: continue
                nzp=zp+k
                nxt[(nzp,nlp)] = nxt.get((nzp,nlp),mp.mpf(0))+c*vk
        if not nxt: break
        nxt = {kk: vv/n for kk,vv in nxt.items()}
        for kk,vv in nxt.items(): result[kk]=result.get(kk,mp.mpf(0))+vv
        cur = nxt
    def dfac(m):
        r=mp.mpf(1); j=m-1
        while j>0: r*=j; j-=2
        return r
    bylam={}
    for (zp,lp),c in result.items():
        if zp%2: continue
        bylam[lp]=bylam.get(lp,mp.mpf(0))+c*dfac(zp)/A**(zp//2)
    return s2,[bylam.get(2*L,mp.mpf(0)) for L in range(0,Lmax+1)]

with open("/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b/poles.txt") as f:
    polesq=[mp.mpf(l.strip()) for l in f if l.strip()]

print("Loop coeffs c_L at travel poles (robust). Growth of ratio => Gevrey/divergent.")
for m,qp in enumerate(polesq):
    if m not in (4,6): continue
    tau=-mp.log(qp); mp.mp.dps=max(55,int(55+1.3/float(tau)))
    xs=saddle(tau); d,_=Wderivs(xs,tau,KMAX)
    s2,cs=loop_coeffs(d,Lmax=5)
    print(f"\n m={m} tau={float(tau):.6f} s2={mp.nstr(s2,6)}")
    acs=[float(abs(c)) for c in cs]
    print("   |c_L| L=0..5:", [f"{a:.3e}" for a in acs])
    rats=[acs[L]/acs[L-1] for L in range(2,len(cs)) if acs[L-1]>0]
    print("   ratio L=2..:", [f"{r:.2f}" for r in rats])
print()
print("If ratio grows ~L-ish (factorial) => divergent loop series, same as route D3.5 (Q2 YES).")
