import mpmath as mp
mp.mp.dps=60
def direct(q,N,s):
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c=2*qb**s
        u[b-1]=u[b]*(1+2*q2b)+qb*c+vb*(c+2*qb*u[b]); v[b-1]=vb
    return u[0],v,qp
def Se(q,J=None):
    if J is None: J=int(6*mp.sqrt(2/(-mp.log(q))))+200
    onem=1-q; S=mp.mpf(0); poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J): S+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
    return S
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
print("R2 CONSOLIDATED PROOF-CHAIN NUMERICS (travel poles)")
print("="*100)
print("(1) EXACT t_k = 2 sum_b (prod_{i<b}A_i) q^{kb}(q^b+v[b-1]), A_b=(1+2q2b)+2qb v[b-1] [SHARED v]")
print("    => t0=t(s=1)=S1b/Se [proven block], t1=t(s=2): same family, source power s is the y-variable.")
# verify unroll identity once more at a pole
q=poles[7]; N=int(60/(1-q))
t1d,v,qp=direct(q,N,2)
A=[(1+2*qp[b]**2)+2*qp[b]*v[b-1] for b in range(N+1)]
s_=mp.mpf(0); pr=mp.mpf(1)
for b in range(1,N+1):
    s_+=pr*2*qp[b]**2*(qp[b]+v[b-1]); pr*=A[b]
print(f"    unroll check at m=8: direct t1={float(t1d):.10f} unroll={float(s_):.10f} match={abs(t1d-s_)<1e-20}")
print()
print(f"{'m':>3} {'tau':>11} | {'t1':>13} {'tau/4':>13} {'t1/(tau/4)':>11} || {'P12':>13} {'sinw*tau^1.5/4sqrt2':>13} {'ratio':>9} || {'Se':>13} {'sqrt(tau/2)sinw':>13} {'ratio':>8}")
allok=True
for m in [2,4,8,12,16,20,24,28,32,36]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    t1,_,_=direct(q,N,2); se=Se(q); P12=t1*se; sw=mp.sin(w)
    p12pred=sw*tau**mp.mpf('1.5')/(4*mp.sqrt(2)); sepred=mp.sqrt(tau/2)*sw
    r_t1=t1/(tau/4); r_p=P12/p12pred; r_s=se/sepred
    if not (abs(r_t1-1)<0.05 and abs(r_p-1)<0.05 and abs(r_s-1)<0.05): allok=False
    print(f"{m:>3} {float(tau):>11.4e} | {float(t1):>13.6e} {float(tau/4):>13.6e} {float(r_t1):>11.7f} || {float(P12):>13.5e} {float(p12pred):>13.5e} {float(r_p):>9.6f} || {float(se):>13.5e} {float(sepred):>13.5e} {float(r_s):>8.6f}")
print()
print(f"ALL THREE RATIOS -> 1 within tol: {allok}")
print("CHAIN: t1=P12/Se ~ [sinw tau^1.5/(4sqrt2)]/[sqrt(tau/2)sinw] = tau/4. sin w CANCELS (pole-tied).")
print("SIGN: t1/tau->1/4>0 at all sampled poles; s=g_V t1->1/4<1 (the B_U!=0 input).")
