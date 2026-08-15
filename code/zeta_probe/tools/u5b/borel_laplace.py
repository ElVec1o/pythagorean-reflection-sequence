import json, mpmath as mp

def _u5b_data(name, argv_index=1):
    """Locate a u5b data file.

    Search order: an explicit command-line path, then $U5B_DIR, then the directory
    holding this script.  `u5b_out.txt`, `u5b_out_m200.bak` and the `cks*.json`
    coefficient files all ship next to the scripts, so the third case is the normal
    one and no argument is needed.  Larger runs of `tools/u5b` (larger --max m) are
    not shipped; point at them with an argument or with U5B_DIR."""
    import os, sys
    if len(sys.argv) > argv_index:
        return sys.argv[argv_index]
    d = os.environ.get("U5B_DIR")
    if d:
        return os.path.join(d, name)
    here = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    if os.path.exists(here):
        return here
    raise SystemExit(
        "error: %s not found next to this script, and neither a path argument nor\n"
        "U5B_DIR was given. Regenerate it with tools/u5b; see tools/u5b/README.md." % name)

mp.mp.dps = 50

def load(fn):
    with open(fn) as f: raw=json.load(f)
    out=[]
    for sv in raw:
        if '/' in sv:
            a,b=sv.split('/'); out.append(mp.mpf(int(a))/mp.mpf(int(b)))
        else: out.append(mp.mpf(sv))
    return out

# ---- Sigma + pole (robust Newton in w) ----
def qpoch(a, base, n):
    p=mp.mpf(1); ai=mp.mpf(1)
    for i in range(n):
        p*= (1-a*ai); ai*=base
    return p
def Sigma(tau):
    q=mp.e**(-tau); q2=q*q; s=mp.mpf(0); k=0
    while True:
        num=2*q*(-2*(1-q))**k*q**(k*k+2*k)
        den=qpoch(q2,q2,k+1)*qpoch(q**3,q2,k)
        t=num/den; s+=t
        if k>3 and abs(t)<mp.mpf(10)**(-mp.mp.dps-5)*(abs(s)+1): break
        k+=1
        if k>5000: break
    return s
def F(w): return Sigma(2/w**2)-1
def pole_w(m):
    w=(m+mp.mpf(1)/2)*mp.pi; h=mp.mpf(10)**(-25)
    for _ in range(100):
        f=F(w); fp=(F(w+h)-F(w-h))/(2*h)
        if fp==0: break
        dw=f/fp; w=w-dw
        if abs(dw)<mp.mpf(10)**(-mp.mp.dps+15)*(abs(w)+1): break
    dev=(m+mp.mpf(1)/2)*mp.pi-w
    if abs(dev)>mp.mpf('0.2'): raise ValueError("branch dev=%s"%mp.nstr(dev,6))
    return w

cks=load(_u5b_data('cks.json'))
K=len(cks)
# g(tau)=dev/sqrt(tau/2)= sum a_n tau^n, a_n=c_{n+1}/2^n.  Borel: B(t)=sum b_n t^n, b_n=a_n/n!.
a=[cks[n]/mp.mpf(2)**n for n in range(K)]
b=[a[n]/mp.factorial(n) for n in range(K)]

# Pade-Borel: rational continuation of B(t).
L=K//2; M=K-1-L
pcoef,qcoef=mp.pade(b,L,M)
def Bpade(t):
    num=sum(pcoef[i]*t**i for i in range(len(pcoef)))
    den=sum(qcoef[i]*t**i for i in range(len(qcoef)))
    return num/den

# Laplace along positive real axis: g_B(tau)=(1/tau) int_0^inf e^{-t/tau} Bpade(t) dt.
# substitute t=tau*x: = int_0^inf e^{-x} Bpade(tau*x) dx.
def g_borel(tau):
    f=lambda x: mp.e**(-x)*Bpade(tau*x)
    # integrate; Bpade has complex poles at tau_s/... ; on real axis fine.
    return mp.quad(f, [0, 1, 2, 4, 8, 16, 32, mp.inf])

print("# Compare Borel-Laplace sum of asymptotic series vs TRUE dev_m at poles")
print("# dev_true from Sigma=1; dev_asy(N)=partial sum to optimal N; dev_borel=Pade-Laplace")
print(" m     w        dev_true            dev_borel            |true-borel|     best partial-sum err")
for m in [4,6,8,10,12,16]:
    try:
        w=pole_w(m)
    except Exception as e:
        print(" m=%d FAIL %s"%(m,e)); continue
    tau=2/w**2
    dev_true=(m+mp.mpf(1)/2)*mp.pi-w
    g=g_borel(tau)
    dev_borel=g*mp.sqrt(tau/2)
    # best partial sum (optimal truncation among available terms)
    S=mp.mpf(0); best=None
    for k in range(1,K+1):
        S+=cks[k-1]/w**(2*k-1)
        e=abs(dev_true-S)
        if best is None or e<best: best=e
    print(" %2d  %s  %s  %s  %s  %s"%(m, mp.nstr(w,8),
        mp.nstr(dev_true,16), mp.nstr(dev_borel,16),
        mp.nstr(abs(dev_true-dev_borel),5), mp.nstr(best,5)))
