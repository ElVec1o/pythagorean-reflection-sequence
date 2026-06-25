import json, mpmath as mp
mp.mp.dps = 40

def load(fn):
    with open(fn) as f: raw=json.load(f)
    out=[]
    for sv in raw:
        if '/' in sv:
            a,b=sv.split('/'); out.append(mp.mpf(int(a))/mp.mpf(int(b)))
        else: out.append(mp.mpf(sv))
    return out

import sys
fn = sys.argv[1] if len(sys.argv)>1 else '/Users/vico/Documents/elvec1o/u5b/cks.json'
cks = load(fn)
K=len(cks)
# Borel transform of g(tau) in tau: B(t) = sum_{n>=0} b_n t^n, b_n = a_n/n! = c_{n+1}/(2^n n!).
b = [ (cks[n]/mp.mpf(2)**n)/mp.factorial(n) for n in range(K) ]
print("Borel-tau series B(t)=sum b_n t^n, K=%d coeffs"%K)

# Pade [L/M] of B(t); poles of the Pade approximant -> Borel singularities (location).
# Use mpmath.pade (needs Taylor coeffs). Take L=M=K//2.
L = K//2; M = K - 1 - L
print("Pade [%d/%d]"%(L,M))
p,q = mp.pade(b, L, M)
# poles = roots of q(t)
qpoly = q[::-1]   # mpmath pade returns lists low->high; polyroots wants high->low
roots = mp.polyroots(qpoly, maxsteps=200, extraprec=80)
print("\nBorel-transform singularities (Pade poles) t=tau_s:")
rs=[]
for r in roots:
    rs.append(r)
    print("   tau_s=%s   |tau_s|=%s   arg=%s deg"%(mp.nstr(r,9),
          mp.nstr(abs(r),9), mp.nstr(mp.arg(r)*180/mp.pi,7)))
# nearest singularity
rs.sort(key=lambda z: abs(z))
print("\nNEAREST Borel-tau singularity: tau_s=%s  rho=|tau_s|=%s  arg=%s deg"%(
      mp.nstr(rs[0],10), mp.nstr(abs(rs[0]),10), mp.nstr(mp.arg(rs[0])*180/mp.pi,8)))

# Compare to candidate exact values
print("\n compare rho: 3pi/2=%s, pi=%s, 2pi/3=%s, 3=%s, 1+pi=%s, sqrt(2)*pi=%s"%(
      mp.nstr(3*mp.pi/2,9), mp.nstr(mp.pi,9), mp.nstr(2*mp.pi/3,9), 3,
      mp.nstr(1+mp.pi,9), mp.nstr(mp.sqrt(2)*mp.pi,9)))
print(" compare arg: 90, 60, 53.13(=atan(4/3)), 45, 55, 50.77(=atan(2/sqrt(... )) ")

# Also: Borel transform in the 1/w variable (Gevrey-1 there?):
# phi(w)=dev ~ sum c_k w^{-(2k-1)}.  Borel-(1/w) Gevrey-1: Bw(z)=sum c_k z^{2k-2}/(2k-2)!
bw = [ cks[k-1]/mp.factorial(2*k-2) for k in range(1,K+1) ]   # coeff of z^{2k-2}
# this is a series in z^2; let u=z^2: Bw=sum_{k>=1} c_k/(2k-2)! u^{k-1}
bu = bw[:]   # bu[k-1]=c_k/(2k-2)!  as series in u
print("\n# Borel-(1/w) [Gevrey-1] transform Bw as series in u=z^2 = 1/w^2:")
Lu=K//2; Mu=K-1-Lu
pu,qu=mp.pade(bu, Lu, Mu)
ru=mp.polyroots(qu[::-1], maxsteps=200, extraprec=80)
ru.sort(key=lambda z: abs(z))
print("  nearest u-sing: u_s=%s |u_s|=%s ; => z^2=u_s, Borel-z sing |z_s|=sqrt|u_s|=%s"%(
      mp.nstr(ru[0],9), mp.nstr(abs(ru[0]),9), mp.nstr(mp.sqrt(abs(ru[0])),9)))
print("  (if Gevrey-1-in-1/w were right, |z_s| would be the Borel-1/w radius ~2 ; here check)")
