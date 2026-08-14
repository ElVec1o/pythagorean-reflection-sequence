# Higher-precision, MANY more travel poles to nail the log-ratio trend definitively.
import mpmath as mp
mp.mp.dps=50
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=6000):
    tot=mp.mpf(0);prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod;prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-60) and j>30:break
    return tot
def bisect(f,a,b,it=250):
    fa,fb=f(a),f(b)
    if mp.sign(fa)==mp.sign(fb):return None
    for _ in range(it):
        m=(a+b)/2;fm=f(m)
        if mp.sign(fm)==mp.sign(fa):a,fa=m,fm
        else:b,fb=m,fm
    return (a+b)/2
g=lambda q:Sig(1,q)-1
roots=[];w=2.5;prev=None;prevq=None
while len(roots)<25 and w<260:
    q=mp.e**(-2/mp.mpf(w)**2);val=g(q)
    if prev is not None and mp.sign(val)!=mp.sign(prev):
        r=bisect(g,prevq,q)
        if r and 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-20)):roots.append(r)
    prev=val;prevq=q;w+=0.04
print(f"{len(roots)} travel poles. log-ratio r_m=ln(q_{{m+1}})/ln(q_m):")
print("If Mahler with base d, r_m must be CONSTANT =1/d for all large m.")
prevr=None
for i in range(len(roots)-1):
    r=mp.log(roots[i+1])/mp.log(roots[i]); m=i+1
    delta = (r-prevr) if prevr is not None else mp.mpf(0)
    print(f"  m={m:2d}: r_m={mp.nstr(r,14)}   (m^2/(m+1)^2={mp.nstr(mp.mpf(m*m)/(m+1)**2,8)})  d_step={mp.nstr(delta,8)}")
    prevr=r
# Conclusion test: r_m strictly increasing toward 1 => no constant 1/d => no Mahler base.
incr=all(mp.log(roots[i+1])/mp.log(roots[i]) < mp.log(roots[i+2])/mp.log(roots[i+1]) for i in range(len(roots)-2))
print("\nr_m STRICTLY INCREASING (never constant):", incr, " -> rules out every base d>=2")
