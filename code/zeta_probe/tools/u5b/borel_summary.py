import json, mpmath as mp
mp.mp.dps = 45

def load(fn):
    with open(fn) as f: raw=json.load(f)
    out=[]
    for sv in raw:
        if '/' in sv:
            a,b=sv.split('/'); out.append(mp.mpf(int(a))/mp.mpf(int(b)))
        else: out.append(mp.mpf(sv))
    return out
import sys
cks=load(sys.argv[1] if len(sys.argv)>1 else '/Users/vico/Documents/elvec1o/u5b/cks.json')
K=len(cks)
b=[ (cks[n]/mp.mpf(2)**n)/mp.factorial(n) for n in range(K)]   # Borel-tau coeffs b_n=a_n/n!

print("="*70)
print("BOREL / RESURGENCE SUMMARY  (Route D3.5)   K=%d coefficients"%K)
print("="*70)

# --- 1. Gevrey order discriminator ---
print("\n[1] GEVREY ORDER")
print("   c_k / Gamma(2k-1)  [-> 0 means series is SUB-Gevrey-1 in 1/w]:")
for k in range(1,K+1):
    print("       k=%2d  c_k/Gamma(2k-1) = %s"%(k, mp.nstr(abs(cks[k-1])/mp.gamma(2*k-1),5)))
print("   a_n / n!  = b_n  [bounded w/ finite radius => Gevrey-1 in tau]:")
print("       |b_n|^(1/n) (-> 1/rho):", ', '.join(mp.nstr(abs(b[n])**(mp.mpf(1)/n),5) for n in range(1,K)))

# --- 2. Borel radius rho via Richardson extrapolation of u_n=|b_n|^{1/n} ---
print("\n[2] BOREL-tau RADIUS rho")
u=[abs(b[n])**(mp.mpf(1)/n) for n in range(1,K)]  # ->1/rho
# Richardson: assume u_n = 1/rho + c/n ; extrapolate pairs
print("   Richardson (u_n -> 1/rho, linear-in-1/n):")
best=None
for i in range(1,len(u)):
    n0=i; n1=i+1
    # u = L + c/n  =>  L = (n1 u1 - n0 u0)/(n1-n0)
    L=(n1*u[i]-n0*u[i-1])/(n1-n0)
    if L>0:
        print("      n=%d,%d -> 1/rho~%s  rho~%s"%(n0+1,n1+1,mp.nstr(L,7),mp.nstr(1/L,7)))
        best=1/L
# --- 3. Pade-Borel nearest singularity (location + arg) ---
print("\n[3] NEAREST BOREL SINGULARITY (Pade-Borel)")
for L_ in [K//2-1, K//2, K//2+1]:
    M_=K-1-L_
    if L_<2 or M_<1: continue
    try:
        pc,qc=mp.pade(b,L_,M_); rr=mp.polyroots(qc[::-1],maxsteps=300,extraprec=120)
        rr=[r for r in rr if abs(r)>1e-5]; rr.sort(key=lambda z:abs(z))
        z=rr[0]
        print("   [%d/%d]: tau_s=%s  rho=%s  arg=%s deg"%(L_,M_,
            mp.nstr(z,8),mp.nstr(abs(z),8),mp.nstr(mp.arg(z)*180/mp.pi,6)))
    except Exception as e:
        print("   [%d/%d] fail"%(L_,M_))

# --- 4. closed-form candidates for tau_s ---
print("\n[4] CLOSED-FORM CANDIDATES for tau_s = rho * e^{i*arg}")
for nm,rho,deg in [('sqrt(2)*pi, 60 deg', mp.sqrt(2)*mp.pi, 60),
                   ('3pi/2, 60 deg', 3*mp.pi/2, 60),
                   ('sqrt(2)*pi, 57 deg', mp.sqrt(2)*mp.pi, 57)]:
    print("   %-22s  |tau_s|=%s  Re=%s  Im=%s"%(nm, mp.nstr(rho,7),
        mp.nstr(rho*mp.cos(deg*mp.pi/180),7), mp.nstr(rho*mp.sin(deg*mp.pi/180),7)))

# --- 5. non-perturbative scale ---
print("\n[5] NON-PERTURBATIVE SCALE")
print("   conjugate Borel pair at Re(tau_s)~2.3 => optimal-trunc remainder ~ exp(-Re(tau_s)/tau)")
print("   = exp(-Re(tau_s)*w^2/2).  e.g. Re(tau_s)=2.3: at w=14 (tau~0.01) ~ exp(-225).")
print("   (much smaller than the naive exp(-c/sqrt(tau))=exp(-c*w) guess.)")
