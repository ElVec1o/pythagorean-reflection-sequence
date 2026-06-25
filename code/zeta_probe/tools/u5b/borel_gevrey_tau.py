import json, mpmath as mp
mp.mp.dps = 50

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
print("file=%s  K=%d"%(fn,K))

# g(tau)=dev/sqrt(tau/2) ~ sum_{k>=1} a_{k-1} tau^{k-1},  a_{k-1}=c_k/2^{k-1}.
a = [cks[k-1]/mp.mpf(2)**(k-1) for k in range(1,K+1)]   # a[0..K-1] = coeff of tau^0..tau^{K-1}
print("\n# Hypothesis: g(tau) Gevrey-1 in tau:  a_n ~ A * n! / rho^n")
print("#   => |a_n|/n! -> A/rho^n, so [|a_n|/n!]^{1/n} -> 1/rho")
print(" n   a_n              |a_n|/n!        ([|a_n|/n!])^{1/n}=1/rho   rho")
for n in range(K):
    an=a[n]; r=abs(an)/mp.factorial(n)
    inv = mp.power(r, mp.mpf(1)/n) if n>=1 and r>0 else mp.mpf('nan')
    rho = (1/inv) if (n>=1 and inv==inv and inv>0) else mp.mpf('nan')
    print(" %2d  %s   %s   %s   %s"%(n, mp.nstr(an,9).rjust(15),
          mp.nstr(r,8), mp.nstr(inv,8), mp.nstr(rho,9)))

print("\n# ratio test:  a_{n}/a_{n-1} ~ n/rho  =>  (a_n/a_{n-1})/n -> 1/rho")
for n in range(1,K):
    if a[n-1]!=0:
        ratio=a[n]/a[n-1]
        print("  n=%2d  a_n/a_{n-1}=%s   /n=%s   abs/n=%s"%(n, mp.nstr(ratio,8),
              mp.nstr(ratio/n,8), mp.nstr(abs(ratio)/n,8)))

# Borel transform of g in tau:  B(t)=sum a_n t^n/n!.  Radius = rho (nearest sing).
# Estimate rho via |a_n/n!|^{-1/n}.  Also try Domb-Sykes plot: 1/rho = lim (a_n/a_{n-1})/n.
print("\n# Domb-Sykes extrap of b_n:=a_n/a_{n-1}/n (-> 1/rho); also sign pattern of a_n:")
print("  signs:", ''.join('+' if a[n]>0 else '-' for n in range(K)))
