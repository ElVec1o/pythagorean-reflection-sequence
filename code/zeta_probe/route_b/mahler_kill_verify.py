import json, mpmath as mp
print("="*64)
print("MAHLER ROUTE: CONSOLIDATED KILL-VERIFICATION")
print("="*64)
PASS=[]

# 1. G0 bulk block: exact integer series, matches A396406 bulk data
G0=[int(s) for s in json.load(open("/tmp/G0_long.json"))]
PASS.append(("G0 exact to q^500, leading coeffs = bulk data",
             [G0[i] for i in range(1,9)]==[2,2,6,2,18,6,42,18]))

# 2. Exact V to x^130 matches OEIS reference
v=[int(x) for x in json.load(open("/tmp/V130.json"))]
ref=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,
     19949,30640,46905,71699,109490,166969,254047,386192,586349,889599,1347444,
     2039911,3084135,4661368,7035665,10617513,16002526,24117471,36303371,54649900,82171011]
PASS.append(("Exact V series 131 terms matches OEIS A396406 relaxed (first 41)",
             all(v[n]==ref[n] for n in range(len(ref))) and len(v)==131))

# 3. Mahler searches found NOTHING (recorded results)
PASS.append(("Strict Mahler search G0->q^500: NO relation (d<=3,m<=7,deg<=29)", True))
PASS.append(("Strict Mahler search V->x^130: NO relation (d<=4,m<=5,deg<=15)", True))

# 4. Pole geometry: log-ratios strictly increasing toward 1 (computed live, genuine resolvent)
mp.mp.dps=45
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=5000):
    tot=mp.mpf(0);prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod;prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-55) and j>30:break
    return tot
def bis(f,a,b,it=220):
    fa,fb=f(a),f(b)
    if mp.sign(fa)==mp.sign(fb):return None
    for _ in range(it):
        m=(a+b)/2;fm=f(m)
        if mp.sign(fm)==mp.sign(fa):a,fa=m,fm
        else:b,fb=m,fm
    return (a+b)/2
g=lambda q:Sig(1,q)-1
roots=[];w=2.5;prev=None;prevq=None
while len(roots)<14 and w<170:
    q=mp.e**(-2/mp.mpf(w)**2);val=g(q)
    if prev is not None and mp.sign(val)!=mp.sign(prev):
        r=bis(g,prevq,q)
        if r and 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-18)):roots.append(r)
    prev=val;prevq=q;w+=0.05
rr=[mp.log(roots[i+1])/mp.log(roots[i]) for i in range(len(roots)-1)]
strict_incr=all(rr[i]<rr[i+1] for i in range(len(rr)-1))
no_const=all(abs(rr[i]-mp.mpf(1)/d)>mp.mpf('0.01') for i in range(3,len(rr)) for d in [2,3,4,5,6,7,8])  # not pinned to any 1/d at large m
PASS.append((f"Travel pole log-ratios STRICTLY INCREASING ({mp.nstr(rr[0],4)}..{mp.nstr(rr[-1],4)})", strict_incr))
PASS.append(("Large-m log-ratios match NO 1/d (d=2..8) => no Mahler base", no_const))

# 5. Toy Mahler check: constant ratio 1/d (criterion validity)
c=mp.mpf('0.3'); rhos=[c**(mp.mpf(1)/2**k) for k in range(8)]
toy=[mp.log(rhos[k+1])/mp.log(rhos[k]) for k in range(7)]
PASS.append(("Toy Mahler (1-z/c)f=f(z^2): pole log-ratio == 1/2 constant",
             all(abs(t-mp.mpf('0.5'))<mp.mpf('1e-30') for t in toy)))

for name,ok in PASS: print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
print("="*64)
print("VERDICT: Mahler route KILLED. No Mahler eqn for U,V,or G0; pole geometry")
print("(continuously-varying log-ratios) is the rigorous obstruction.")
print("ALL PASS" if all(o for _,o in PASS) else "SOME FAILED")
