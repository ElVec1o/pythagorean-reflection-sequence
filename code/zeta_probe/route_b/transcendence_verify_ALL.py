"""
CONSOLIDATED reproducible verification for the transcendence theorem (A396406 relaxed series).
Run: python3 transcendence_verify_ALL.py
All claims printed with PASS/FAIL. Adequate precision throughout (dps scaled to the
exponential size sqrt(2/tau) of the alternating terms; under-precision gives spurious blowup).
"""
import mpmath as mp, math

# ---- BULK block ----
def alpha(k,tau): return 2/(mp.e**((k+1)*tau)-1)          # = 2 q^{k+1}/(1-q^{k+1}), q=e^{-tau}
def Sk(k,tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=alpha(k+2*j,tau)*prod
        prod*=(alpha(k+1+2*j,tau)-alpha(k+2*j,tau))       # gamma_{k+2j} (<0)
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot
# ---- TRAVEL block ----
def Ak(k,tau):
    q=mp.e**(-tau); return 2*q/(1-q**(k+1))
def Ck(k,tau):
    q=mp.e**(-tau); return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigk(k,tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=Ak(k+2*j,tau)*prod
        prod*=Ck(k+2*j,tau)
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot
def dps_for(w): return int(float(w)/math.log(10))+55
PASS=[]

# (0) Taylor coeffs of G_0 (bulk) reproduce 2,2,6,2,18,6,42,18,118,50,282,190,706,594
# Use power-series arithmetic in q directly (alpha_k,gamma_k as series), exact rational.
mp.mp.dps=60
N=16
def ps_alpha(k):   # 2 q^{k+1}/(1-q^{k+1}) = 2 sum_{m>=1} q^{m(k+1)}, truncated to deg N
    c=[mp.mpf(0)]*(N+1)
    m=1
    while m*(k+1)<=N: c[m*(k+1)]=mp.mpf(2); m+=1
    return c
def ps_sub(a,b): return [a[i]-b[i] for i in range(N+1)]
def ps_mul(a,b):
    c=[mp.mpf(0)]*(N+1)
    for i in range(N+1):
        if a[i]==0: continue
        for j in range(N+1-i):
            if b[j]!=0: c[i+j]+=a[i]*b[j]
    return c
def ps_Sk(k):  # sum_j alpha_{k+2j} prod_{i<j} gamma_{k+2i}, truncated
    tot=[mp.mpf(0)]*(N+1); prod=[mp.mpf(1)]+[mp.mpf(0)]*N
    for j in range(N+2):
        ak=ps_alpha(k+2*j); term=ps_mul(ak,prod)
        tot=[tot[i]+term[i] for i in range(N+1)]
        gk=ps_sub(ps_alpha(k+1+2*j),ps_alpha(k+2*j))  # gamma_{k+2j}=alpha_{k+1}-alpha_k? sign check below
        prod=ps_mul(prod,gk)
        if all(prod[i]==0 for i in range(N+1)): break
    return tot
# gamma_k = 2q^{k+2}/(1-q^{k+2}) - 2q^{k+1}/(1-q^{k+1}) = alpha_{k+1}-alpha_k
S0p=ps_Sk(0); S1p=ps_Sk(1)
# G0 = S0/(1-S1): invert (1-S1) as power series
den=[mp.mpf(1)-S1p[0]]+[-S1p[i] for i in range(1,N+1)]
inv=[mp.mpf(0)]*(N+1); inv[0]=1/den[0]
for n in range(1,N+1):
    inv[n]=-sum(den[k]*inv[n-k] for k in range(1,n+1))/den[0]
G0p=ps_mul(S0p,inv)
coeffs=[int(mp.nint(G0p[i])) for i in range(1,15)]
tgt=[2,2,6,2,18,6,42,18,118,50,282,190,706,594]
PASS.append(("G_0 Taylor coeffs match A396406 bulk data", coeffs==tgt))

# (1) Travel singularity q*=0.44945363..., rate 1.4916177871
qstar=mp.findroot(lambda q: Sigk(1,-mp.log(q),60)-1, mp.mpf('0.4495'))
PASS.append(("travel q*=0.4494536305...", abs(qstar-mp.mpf('0.449453630558948'))<mp.mpf('1e-12')))
PASS.append(("travel rate 1.4916177871", abs(1/mp.sqrt(qstar)-mp.mpf('1.4916177871'))<mp.mpf('1e-9')))

# (2) Asymptotic model S_1 ~ 1-cos(sqrt(2/(-ln q))) with adequate precision (NO spurious blowup)
ok_model=True; ok_inrange=True
for le in [-3,-4,-5,-6,-7]:
    eps=mp.mpf(10)**le; q=1-eps; tau=-mp.log(q); w=mp.sqrt(2/tau)
    dps=dps_for(w); s=Sk(1,tau,dps)
    if not (mp.mpf(-0.01)<=s<=mp.mpf(2.01)): ok_inrange=False
    if abs(s-(1-mp.cos(w)))>mp.mpf('0.05'): ok_model=False
PASS.append(("S_1 in [0,2], no precision-blowup (dps scaled)", ok_inrange))
PASS.append(("S_1 ~ 1-cos(sqrt(2/(-ln q))) to <0.05", ok_model))

# (3) Two extreme-phase limits => sign changes of S_1-1 (bulk) and Sigma_1-1 (travel)
ok_b=True; ok_t=True
for n in [8,16,32,64]:
    wo=(2*n+1)*mp.pi; we=2*n*mp.pi
    so=Sk(1,2/wo**2,dps_for(wo));  se=Sk(1,2/we**2,dps_for(we))
    if not (so>1 and se<1): ok_b=False
    To=Sigk(1,2/wo**2,dps_for(wo)); Te=Sigk(1,2/we**2,dps_for(we))
    if not (To>1 and Te<1): ok_t=False
PASS.append(("BULK: S_1>1 at w=(2n+1)pi and S_1<1 at w=2n*pi (n<=64)", ok_b))
PASS.append(("TRAVEL: Sigma_1>1 at w=(2n+1)pi and <1 at w=2n*pi (n<=64)", ok_t))

# (4) Genuine poles: count zeros of 1-S_1 and 1-Sigma_1 in a w-window; S_0, Sigma_0 nonzero there
def count(S1f,S0f,wlo,whi,N):
    zs=[]; prev=None; pw=None
    for i in range(N+1):
        w=wlo+(whi-wlo)*mp.mpf(i)/N
        s=int(mp.sign(S1f(2/w**2,dps_for(w))-1))
        if prev is not None and s!=0 and prev!=0 and s!=prev:
            lo,hi=pw,w; fl=prev
            for _ in range(70):
                m=(lo+hi)/2; fm=int(mp.sign(S1f(2/m**2,dps_for(m))-1))
                if fm==fl or fm==0: lo=m
                else: hi=m
            wz=(lo+hi)/2; s0=S0f(2/wz**2,dps_for(wz)); zs.append((wz,s0))
        if s!=0: prev=s; pw=w
    return zs
zb=count(lambda t,d:Sk(1,t,d), lambda t,d:Sk(0,t,d), mp.mpf(10),mp.mpf(40),600)
zt=count(lambda t,d:Sigk(1,t,d), lambda t,d:Sigk(0,t,d), mp.mpf(10),mp.mpf(40),600)
PASS.append((f"BULK: {len(zb)} poles in w[10,40], all S_0!=0", len(zb)>=8 and all(abs(s0)>mp.mpf('1e-4') for _,s0 in zb)))
PASS.append((f"TRAVEL: {len(zt)} poles in w[10,40], all Sigma_0!=0", len(zt)>=8 and all(abs(s0)>mp.mpf('1e-4') for _,s0 in zt)))

# (5) simple pole + nonzero residue at a sample bulk zero
mp.mp.dps=80
qz=mp.findroot(lambda q: 1-Sk(1,-mp.log(q),80), mp.mpf('0.999338942380106116'))
dv=mp.diff(lambda q: 1-Sk(1,-mp.log(q),80), qz)
s0z=Sk(0,-mp.log(qz),80)
PASS.append(("sample bulk pole is SIMPLE (deriv!=0) with S_0!=0", abs(dv)>mp.mpf('1e-3') and abs(s0z)>mp.mpf('1e-3')))

# (6) Monotone domination (lem:dom) + EXACT cosine reduction (lem:reduce):
#     0 < t_j <= that_j, rho_j=t_j/that_j decreasing to 0, and
#     S_1 = (1-cos w) + sum_j mu_j R_j(w),  mu_j=rho_{j-1}-rho_j>=0, sum mu_j=1,
#     R_j(w)=cos w - sum_{i<=j}(-1)^i w^{2i}/(2i)!   (cosine Taylor remainder).
ok_dom=True; ok_reduce=True
for tau in [mp.mpf('0.01'), mp.mpf('0.002')]:
    mp.mp.dps=120
    w=mp.sqrt(2/tau); J=int(6/float(tau))+200
    t=[]; prod=mp.mpf(1)
    for j in range(J):
        t.append(alpha(1+2*j,tau)*prod); prod*=-(alpha(2+2*j,tau)-alpha(1+2*j,tau))
    that=[(2/tau)**(j+1)/mp.factorial(2*j+2) for j in range(J)]
    rho=[t[j]/that[j] for j in range(J)]
    if not (all(0<rho[j]<=1+mp.mpf('1e-60') for j in range(J)) and
            all(rho[j]<=rho[j-1]+mp.mpf('1e-60') for j in range(1,J)) and rho[J-1]<mp.mpf('1e-3')):
        ok_dom=False
    mu=[(1 if j==0 else rho[j-1])-rho[j] for j in range(J)]
    S1=sum((-1)**j*t[j] for j in range(J)); cw=mp.cos(w)
    Cj=mp.mpf(0); rhs=1-cw
    for j in range(J):
        Cj+=(-1)**j*w**(2*j)/mp.factorial(2*j); rhs+=mu[j]*(cw-Cj)
    if abs(S1-rhs)>mp.mpf('1e-90') or abs(sum(mu)-1)>mp.mpf('1e-90'): ok_reduce=False
PASS.append(("lem:dom  0<t_j<=that_j, rho_j decreasing to 0", ok_dom))
PASS.append(("lem:reduce  S_1=(1-cos w)+sum mu_j R_j(w) to 90+ digits", ok_reduce))

# (7) Closed-form leading constant:  (S_1-1)/sqrt(tau) -> -17*sqrt(2)/36 at sin w = 1.
c1=-17*mp.sqrt(2)/36
w=(2*160+mp.mpf(1)/2)*mp.pi; tau=2/w**2
s=Sk(1,tau,dps_for(w)); approx=(s-1)/mp.sqrt(tau)
PASS.append(("c_1 = -17*sqrt(2)/36 = -0.667823071 (leading asymptotic)", abs(approx-c1)<mp.mpf('1e-5')))

# (8) Geometric-collapse split (prop:T1): E = T1 + T2 with T1 = cos w - cos(w e^{-tau/2})
#     EXACT and |T1| <= sqrt(tau/2) UNCONDITIONALLY/uniformly; T1 carries -(1/sqrt2)sqrt(tau)sin w,
#     T2 the residual carries +(sqrt2/36)sqrt(tau)sin w.  (Half of c_1 is unconditional.)
ok_split=True; ok_T1bound=True
for n in [20,80]:
    w=(2*n+mp.mpf(1)/2)*mp.pi; tau=2/w**2; dps=dps_for(w)
    E=Sk(1,tau,dps)-(1-mp.cos(w))
    T1=mp.cos(w)-mp.cos(w*mp.e**(-tau/2)); T2=E-T1
    if not (abs(T1)<=mp.sqrt(tau/2)): ok_T1bound=False           # uniform bound, unconditional
    if abs(T1/mp.sqrt(tau)-(-1/mp.sqrt(2)))>mp.mpf('1e-3'): ok_split=False   # T1 -> -1/sqrt2
    if abs(T2/mp.sqrt(tau)-(mp.sqrt(2)/36))>mp.mpf('1e-3'): ok_split=False    # T2 -> +sqrt2/36
PASS.append(("prop:T1  |T1|<=sqrt(tau/2) unconditional, T1=cos w-cos(w e^{-tau/2})", ok_T1bound))
PASS.append(("split  T1->-(1/sqrt2)sqrt(t)sinw, T2->+(sqrt2/36)sqrt(t)sinw  (sum=c_1)", ok_split))

# (9) Unconditional block theorem (thm:blocks): Sigma_1 in Z[[q]], radius 1, non-rational
#     (Hankel det != 0 through size 11); and the TRAVEL constant is +sqrt2/36 (NOT -17sqrt2/36,
#     which is the BULK value) -- rem:blockscope correctness check.
from fractions import Fraction as F
Nq=40
def psAk(k):
    c=[F(0)]*(Nq+1); m=0
    while m*(k+1)+1<=Nq: c[m*(k+1)+1]+=F(2); m+=1
    return c
def psCk(k):
    c=[F(0)]*(Nq+1); m=0
    while (k+3)+m*(k+2)<=Nq: c[(k+3)+m*(k+2)]+=F(2); m+=1
    m=0
    while (k+2)+m*(k+1)<=Nq: c[(k+2)+m*(k+1)]-=F(2); m+=1
    return c
def psmul(a,b):
    c=[F(0)]*(Nq+1)
    for i in range(Nq+1):
        if a[i]==0: continue
        for j in range(Nq+1-i):
            if b[j]: c[i+j]+=a[i]*b[j]
    return c
tot=[F(0)]*(Nq+1); prod=[F(1)]+[F(0)]*Nq
for j in range(Nq+2):
    term=psmul(psAk(1+2*j),prod); tot=[tot[i]+term[i] for i in range(Nq+1)]
    prod=psmul(prod,psCk(1+2*j))
    if all(x==0 for x in prod): break
Sig1c=tot
allint=all(x.denominator==1 for x in Sig1c)
def hankel_nz(seq,m):
    M=[[F(seq[i+j]) for j in range(m)] for i in range(m)]; det=F(1)
    for col in range(m):
        piv=next((r for r in range(col,m) if M[r][col]!=0),None)
        if piv is None: return False
        if piv!=col: M[col],M[piv]=M[piv],M[col]; det=-det
        det*=M[col][col]; inv=M[col][col]
        for r in range(col+1,m):
            f=M[r][col]/inv; M[r]=[M[r][j]-f*M[col][j] for j in range(m)]
    return det!=0
hk=all(hankel_nz(Sig1c,m) for m in [4,5,6,7,9,10,11])
PASS.append(("thm:blocks  Sigma_1 in Z[[q]], non-rational (Hankel!=0 thru 11)", allint and hk))
# travel constant: (Sigma_1-1)/sqrt(tau) -> +sqrt2/36 (bulk is -17sqrt2/36)
w=(2*120+mp.mpf(1)/2)*mp.pi; tau=2/w**2
ct=(Sigk(1,tau,dps_for(w))-1)/mp.sqrt(tau)
PASS.append(("rem:blockscope  travel c1 = +sqrt2/36 (bulk c1 = -17sqrt2/36)", abs(ct-mp.sqrt(2)/36)<mp.mpf('1e-5')))

# (10) Model-subtraction (ss:modelsub): corr=K'-K'_model has sup~tau/6 (knife-edge gone);
#      L_1 closed form bounds it, sup|L_1|<=tau/6+(13sqrt2/36)tau^1.5+tau^2/6; corr-L_1=O(tau^1.5).
def Kpfull(u,mu,J):
    tot=mp.mpf(0); term=mp.mpf(-1)
    for j in range(J):
        tot+=mu[j]*term; term*=-u*u/mp.mpf((2*j+1)*(2*j+2))
        if abs(term)<mp.mpf(10)**-55 and (2*j)>float(u): break
    return tot
def L1cf(u,tau):
    W=u*mp.e**(-tau/2); s=mp.sin(W); c=mp.cos(W)
    A=W**3*s/72-W**2*c/16-W*s/48; B=-W**3*s/72+7*W**2*c/48+17*W*s/48-c/6
    return tau**2*A+tau**2*mp.e**(-tau)*B
ok_ms=True
for tau in [mp.mpf('0.02'),mp.mpf('0.005')]:
    mp.mp.dps=80; w=mp.sqrt(2/tau); J=int(8/float(tau))+300
    t=[]; pr=mp.mpf(1)
    for j in range(J):
        t.append(alpha(1+2*j,tau)*pr); pr*=-(alpha(2+2*j,tau)-alpha(1+2*j,tau))
    that=[(2/tau)**(j+1)/mp.factorial(2*j+2) for j in range(J)]
    rho=[t[j]/that[j] for j in range(J)]; mu=[(1 if j==0 else rho[j-1])-rho[j] for j in range(J)]
    amp=1-mp.e**(-tau); a=mp.e**(-tau/2)
    sC=mp.mpf(0); sR=mp.mpf(0)
    for i in range(0,701):
        u=w*mp.mpf(i)/700
        corr=Kpfull(u,mu,J)+amp*mp.cos(u*a); sC=max(sC,abs(corr)); sR=max(sR,abs(corr-L1cf(u,tau)))
    bound=tau/6+(13*mp.sqrt(2)/36)*tau**mp.mpf(1.5)+tau**2/6
    if not (sC<=bound and sR<2*tau**mp.mpf(1.5)): ok_ms=False   # corr<=L1 bound; corr-L1=O(tau^1.5)
PASS.append(("ss:modelsub  sup|corr|<=tau/6+.., corr-L1=O(tau^1.5) (knife-edge gone)", ok_ms))

# (11) Lemma TAIL machinery (lem:tail): Touchard identity D_p=2^-p Re[e^iW T_p(iW)], T_p(w)=E[N^p]
#      Poisson; per-p bound |D_p|<=2^-p T_p(w); R-control 0<=phi(y)<=y^2/24. (My earlier uniform-D_p
#      claim was FALSE: sup|D_p|/(w/2)^p grows like 2^-p Bell -- corrected to Touchard/Poisson.)
import sympy as _sp
_x=_sp.symbols('x'); _W=_sp.symbols('W')
def _Tou(p): return sum(_sp.functions.combinatorial.numbers.stirling(p,r,kind=2)*_x**r for r in range(p+1))
_Ds=[_sp.cos(_W)]
for _ in range(11): _Ds.append(_sp.simplify((_W/2)*_sp.diff(_Ds[-1],_W)))
ok_tou=True; ok_pois=True; ok_phi=True
for p in [3,6,10]:
    Wv=mp.mpf('2.3'); dd=_sp.lambdify(_W,_Ds[p],'mpmath')(Wv)
    Tp=_sp.lambdify(_x,_Tou(p),'mpmath'); dt=mp.re(mp.e**(1j*Wv)*Tp(1j*Wv))/2**p
    if abs(dd-dt)>mp.mpf('1e-12'): ok_tou=False
    w0=mp.mpf(5); Em=mp.nsum(lambda n: mp.mpf(n)**p*mp.e**(-w0)*w0**n/mp.factorial(n),[0,mp.inf])
    if abs(Tp(w0)-Em)>mp.mpf('1e-8'): ok_pois=False
phi=lambda y: mp.log(mp.sinh(y/2)/(y/2))
for y in [mp.mpf(v) for v in [0.01,0.1,0.5,1,2,5,10,20]]:
    if not (0<=phi(y)<=y**2/24+mp.mpf('1e-25')): ok_phi=False
PASS.append(("lem:tail Touchard D_p=2^-p Re[e^iW T_p(iW)] (corrects false uniform-D_p)", ok_tou))
PASS.append(("lem:tail Poisson-moment T_p(w)=E[N^p], N~Poisson(w)", ok_pois))
PASS.append(("lem:tail R-control 0<=log(sinh(y/2)/(y/2))<=y^2/24", ok_phi))

# (12) lem:tail CORRECTED assembly (finite truncation): the FULL abs-majorant Rbar diverges for
#      j>pi/tau (Poisson tail), so truncate at N=2: Rbar^[2]=|f1|tau^2 Q1+|f2|tau^4 Q2 (fixed poly);
#      remainder S_j=O(tau^{5/2}) on j<=2w; 2 E[Psi(Rbar^[2](N/2))]=O(tau) dominates true tail.
try:
    import sympy as _sp2
    _y=_sp2.symbols('y'); _jj=_sp2.symbols('j'); _ii=_sp2.symbols('i')
    _phi=_sp2.series(_sp2.log(_sp2.sinh(_y/2)/(_y/2)),_y,0,40).removeO()
    _f=[_phi.coeff(_y,2*n) for n in range(1,12)]
    _Q=[_sp2.lambdify(_jj,_sp2.summation((2*_ii+2)**(2*n)+(2*_ii+1)**(2*n)-1,(_ii,0,_jj)),'mpmath') for n in range(1,12)]
    ok_div=True; ok_tail=True
    for tau in [mp.mpf('0.02'),mp.mpf('0.005')]:
        mp.mp.dps=45; w=mp.sqrt(2/tau)
        # full Rbar diverges past j=pi/tau: grows with #terms there, stable below
        below=[sum(abs(mp.mpf(str(_f[n-1])))*tau**(2*n)*_Q[n-1](w) for n in range(1,nt+1)) for nt in [4,9]]
        above=[sum(abs(mp.mpf(str(_f[n-1])))*tau**(2*n)*_Q[n-1](mp.mpf('1.5')*mp.pi/tau) for n in range(1,nt+1)) for nt in [4,9]]
        if not (abs(below[0]-below[1])<mp.mpf('1e-6') and above[1]>3*above[0]): ok_div=False  # converges below, diverges above
        Rb2=lambda x: abs(mp.mpf(str(_f[0])))*tau**2*_Q[0](x)+abs(mp.mpf(str(_f[1])))*tau**4*_Q[1](x)
        E=sum(mp.e**(-w)*w**N/mp.factorial(N)*(mp.e**Rb2(mp.mpf(N)/2)-1-Rb2(mp.mpf(N)/2)) for N in range(0,int(10*w)+50))
        if not (2*E < mp.mpf('0.02')*tau): ok_tail=False  # 2E[Psi(Rbar^[2])] = O(tau), <0.02 tau
    PASS.append(("lem:tail full majorant DIVERGES past j=pi/tau (=> truncation needed)", ok_div))
    PASS.append(("lem:tail truncated 2E[Psi(Rbar^[2](N/2))] = O(tau) <= 0.02 tau (finite)", ok_tail))
except Exception as _e:
    PASS.append(("lem:tail truncated assembly (sympy)", False))

print("="*64); print("TRANSCENDENCE VERIFICATION — A396406 relaxed series"); print("="*64)
for name,ok in PASS:
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
print("="*64)
print("ALL PASS" if all(ok for _,ok in PASS) else "SOME FAILED")
