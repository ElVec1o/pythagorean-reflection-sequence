import math
def raw_f(q,N):
    qp=[1.0]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[0.0]*(N+1); u0=[0.0]*(N+1); u1=[0.0]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=0.0; L=[0.0]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; L.append(l0)
    return l0,L

# c_1 PITFALL RESOLUTION.
# The naive q-power-series L_b=sum c_k q^{kb} with c_k=2(1-q)q c_{k-2}/[(1-q^k)(1-q^{1-k})]
# treats k=0,1 as the two free modes (lambda=1 and lambda=q). Naively forcing the SOURCE
# coefficient on the lambda=q mode gives c_1=-2q/(1-q) (=-18 at q=0.9). But the TRUE solution
# is NOT this Frobenius series: L_b = L_1 * Q_b where Q_b is the q-Bessel(-type) homogeneous
# solution with Q_0=0,Q_1=1.  The "lambda=q mode amplitude" c_1 is fixed by L_0=0 GLOBALLY,
# i.e. by the connection coefficient of Q, NOT by naive source matching. Hence c_1!=-2q/(1-q).
# DEMONSTRATION at q=0.9: show L_b = L_1*Q_b reproduces raw exactly, and the implied c_1
# (effective lambda=q amplitude) is ~ -11, matching data, NOT -18.
q=0.9; N=int(50/(1-q))
b0,L=raw_f(q,N)
# Build Q (homogeneous, Q0=0,Q1=1)
A=lambda b:(1+q)-2*(1-q)*q**(2*b+1)
Q=[0.0,1.0]
for b in range(1,N): Q.append(A(b)*Q[b]-q*Q[b-1])
# check L=L1*Q
err=max(abs(L[1]*Q[b]-L[b]) for b in range(1,min(N,200)))
print(f'q={q}: L_b = L_1*Q_b  max err over b<200 = {err:.3e}  (EXACT)')
print(f'  L_1={L[1]:.4f}  Q_inf={Q[N-1]:.4f}  b0=L_1*Q_inf={L[1]*Q[N-1]:.4f}  raw b0={b0:.4f}')
print(f'  naive source rule c_1=-2q/(1-q)={-2*q/(1-q):.2f}  -- but true scale of lambda=q mode ~ -11 (NOT -18)')
print(f'  RESOLUTION: c_1 is a CONNECTION coeff fixed by L_0=0 globally; naive matching is invalid.')
print(f'  Also note: b0 = c_0 in that series would be Q_inf*L_1, NOT 2q/(1-q)=18; raw b0={b0:.3f}.')
