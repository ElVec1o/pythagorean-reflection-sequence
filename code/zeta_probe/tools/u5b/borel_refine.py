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

def _u5b_data(name, argv_index=1):
    """Locate a u5b data file. The u5b run outputs are NOT part of this repository:
    they are large intermediates produced by tools/u5b. Pass the path as an argument
    or set U5B_DIR."""
    import os, sys
    if len(sys.argv) > argv_index:
        return sys.argv[argv_index]
    d = os.environ.get("U5B_DIR")
    if d:
        return os.path.join(d, name)
    raise SystemExit(
        "error: %s not found. The u5b run outputs are not shipped with this repository.\n"
        "Pass the path as the first argument, or set U5B_DIR to the directory holding it.\n"
        "Regenerate with tools/u5b (see tools/u5b/README.md if present)." % name)

cks=load(_u5b_data('cks.json'))
K=len(cks)
b=[ (cks[n]/mp.mpf(2)**n)/mp.factorial(n) for n in range(K)]
print("K=%d Borel-tau coeffs"%K)

# Several Pade orders; report nearest conjugate-pair singularity each time.
print("\n# Pade-Borel nearest singularity vs order:")
for L in range(2, K-1):
    M=K-1-L
    if M<1: break
    try:
        pc,qc=mp.pade(b,L,M)
        rr=mp.polyroots(qc[::-1],maxsteps=300,extraprec=120)
    except Exception as e:
        print("  [%d/%d] fail %s"%(L,M,e)); continue
    rr=[r for r in rr if abs(r)>1e-6]
    rr.sort(key=lambda z: abs(z))
    if not rr:
        print("  [%d/%d] no roots"%(L,M)); continue
    z=rr[0]
    print("  [%d/%d]  tau_s=%s  rho=%s  arg=%s deg"%(L,M,
        mp.nstr(z,8), mp.nstr(abs(z),9), mp.nstr(mp.arg(z)*180/mp.pi,7)))

# Richardson on |b_n|^{1/n} for rho, and on the sign-oscillation for theta.
print("\n# |b_n|^{1/n} (->1/rho):")
seq=[abs(b[n])**(mp.mpf(1)/n) for n in range(1,K)]
for n,v in enumerate(seq,1):
    print("   n=%2d  %s   rho~%s"%(n, mp.nstr(v,8), mp.nstr(1/v,8)))

# closed-form candidates
print("\n# candidate tau_s closed forms (rho, arg deg):")
for nm,rho,th in [('sqrt2*pi @60', mp.sqrt(2)*mp.pi, 60),
                  ('3pi/2 @60', 3*mp.pi/2, 60),
                  ('pi @60', mp.pi, 60),
                  ('sqrt2*pi @ atan(sqrt3)=60', mp.sqrt(2)*mp.pi, mp.atan(mp.sqrt(3))*180/mp.pi),
                  ('2pi @ ?', 2*mp.pi, 60)]:
    re=rho*mp.cos(th*mp.pi/180); im=rho*mp.sin(th*mp.pi/180)
    print("   %-26s rho=%s arg=%s  => tau_s=%s + %s i"%(nm,
        mp.nstr(rho,8), mp.nstr(th,6), mp.nstr(re,8), mp.nstr(im,8)))
