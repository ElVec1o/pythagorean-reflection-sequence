import mpmath as mp
mp.mp.dps=40
def raw_L(q,N):
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b]); v[b-1]=vb
    l0=mp.mpf(0); L=[mp.mpf(0)]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; L.append(l0)
    return l0,L,qp
q=mp.mpf('0.9'); N=int(50/(1-q))
b0,L,qp=raw_L(q,N)
print(f"q=0.9 b0(=L_inf)={float(b0):.6f}")
print("raw L_b (the TRUE source-0 partial sum) for small b:")
for b in range(0,8):
    print(f"  L_{b}={float(L[b]):+.6f}")
print(f"  L_N={float(L[N]):+.6f} (=b0)")
print()
# Does the TRUE L_b satisfy the homogeneous recursion? Check:
print("Does raw L satisfy L_{b+1}-A_b L_b+q L_{b-1}=0 (homogeneous)?")
for b in range(1,5):
    A=(1+q)-2*(1-q)*q**(2*b+1)
    res=L[b+1]-A*L[b]+q*L[b-1]
    print(f"  b={b}: residual={float(res):.2e}")
print()
# So TRUE L_b is POSITIVE and ->b0>0. The series I built gave NEGATIVE L_b. So my series
# solution is a DIFFERENT homogeneous solution (the one with c_0=b0 but wrong overall).
# The point: q^{kb} for k>=1 ->0, so L_inf = c_0. TRUE L_inf=b0=6.808 => c_0=6.808. GOOD.
# But the series sum_k c_k q^{kb} must ALSO equal TRUE L_b for all b, and TRUE L_1=+2.0..?
print(f"TRUE L_1={float(L[1]):.6f}. Series with c0=b0,c1=? must give this.")
# Build series, solve c1 so that L_1 series = TRUE L_1 (one linear condition), check L_0.
K=800
def Lseries(c0,c1,b):
    c=[mp.mpf(0)]*(K+2); c[0]=mp.mpf(c0); c[1]=mp.mpf(c1)
    for k in range(2,K+1): c[k]=2*(1-q)*q*c[k-2]/((1-q**k)*(1-q**(1-k)))
    return sum(c[k]*q**(k*b) for k in range(K+1)), c
# Solve c1 from L_1: L_1series(c0=b0,c1)=L[1]. It's linear in c1.
v0,_=Lseries(b0,0,1); v1,_=Lseries(0,1,1)
# L_1 = b0*v0_per(c0)+c1*... careful: Lseries(b0,0,1) has c0=b0,c1=0; Lseries(0,1,1) c0=0,c1=1.
c1_solved=(L[1]-v0)/v1
print(f" c1 solved from matching TRUE L_1: c1={float(c1_solved):.6f}")
# Now check L_0 with this c1:
L0check,cc=Lseries(b0,c1_solved,0)
print(f" with c0=b0={float(b0):.4f}, c1={float(c1_solved):.4f}: L_0series={float(L0check):.6f} (should be 0)")
# And verify reproduces L_b:
print(" verify series reproduces TRUE L_b:")
for b in [0,1,2,3,5,10,20]:
    Ls,_=Lseries(b0,c1_solved,b)
    print(f"   b={b}: series={float(Ls):+.6f} raw={float(L[b]):+.6f} diff={float(Ls-L[b]):.1e}")
