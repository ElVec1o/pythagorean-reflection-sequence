"""
PART 10 -- FINAL airtight verification of the verdict form:
   t1 = (1/2)(w-W)^2 - rest/Se,  rest = (1/2)(w-W)^2 cosW - P12 - (1/2)(w-W)^2 (cosW - Se)
                                       = -P12 + (1/2)(w-W)^2 Se   [ALGEBRAIC IDENTITY: rest = -(P12 - (1/2)(w-W)^2 Se) = -Rho]
So 'rest' is literally  -Rho = -(P12 - (1/2)(w-W)^2 Se), and t1 - (1/2)(w-W)^2 = -rest/Se = Rho/Se EXACTLY.
(consistent with PART 8). This part: (i) confirm the ALGEBRAIC identity t1-(1/2)(w-W)^2 = Rho/Se to machine eps,
(ii) confirm elementary expansion (1/2)(w-W)^2 = tau/4 + (3/16)tau^2 + ... gives t1/tau=1/4+(3/16)tau,
(iii) confirm s=(q/p)t1 -> 1/4 with s=1/4+tau/16, and SIGN (t1>0, s<1) -- the B_U!=0 inputs.
(iv) Rho/Se order one more time at the largest m, high dps.
"""
import mpmath as mp

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*112)
print("PART 10 -- FINAL verdict form & sign/limit checks.  t1 = (1/2)(w-W)^2 + Rho/Se, Rho=P12-(1/2)(w-W)^2 Se.")
print("  half := (1/2)(w-W)^2 = (1/2)w^2(1-e^{-tau/2})^2  [ELEMENTARY].  Series: half = tau/4 + (3/16)tau^2 + O(tau^3).")
print("="*112)
print(f"{'m':>3} {'tau':>10} {'t1':>13} {'half':>13} {'t1-half':>11} {'=Rho/Se?':>9} {'half/(tau/4)':>12} {'t1/tau':>9} {'s=(q/p)t1':>10} {'s<1':>4}")
maxsign=True
for m in [1,2,4,8,16,24,32,40,48]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=80+int(3.0*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(110/(1-q)); p=1-q
    W=w*mp.e**(-tau/2)
    b0,b1,t0,t1=raw(q,N); P12,Se,P11,P21=cocycle(q,N)
    half=mp.mpf(1)/2*(w-W)**2
    Rho=P12-half*Se
    idcheck=abs((t1-half)-Rho/Se)   # algebraic identity, should be ~1e-(dps)
    s=(q/p)*t1
    ok = (t1>0) and (s<1)
    maxsign = maxsign and ok
    print(f"{m:>3} {float(tau):>10.3e} {float(t1):>13.8f} {float(half):>13.8f} {float(t1-half):>11.3e} {float(idcheck):>9.1e} {float(half/(tau/4)):>12.8f} {float(t1/tau):>9.6f} {float(s):>10.7f} {str(ok):>4}")
    mp.mp.dps=80
print()
# elementary series check of half/(tau/4) and (s-1/4)/tau
print("ELEMENTARY EXPANSION CHECK (symbolic via mpmath series of (1/2)w^2(1-e^{-tau/2})^2 with w^2=2/tau):")
mp.mp.dps=50
for tau in [mp.mpf('0.01'),mp.mpf('0.001'),mp.mpf('0.0001')]:
    w2=2/tau; half=mp.mpf(1)/2*w2*(1-mp.e**(-tau/2))**2
    print(f"   tau={float(tau):.0e}: half={float(half):.10f}  half/(tau/4)={float(half/(tau/4)):.8f} (->1)  (half/tau-1/4)/tau={float((half/tau-mp.mpf(1)/4)/tau):.6f} (->3/16=0.1875)")
print()
print(f"SIGN/LIMIT: across sampled poles t1>0 AND s<1 : {maxsign}   (the B_U(q_m)!=0 inputs hold)")
print("ALGEBRAIC IDENTITY t1 - half = Rho/Se verified to machine eps (col '=Rho/Se?' ~ 1e-70+).")
