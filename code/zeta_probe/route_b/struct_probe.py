import mpmath as mp
mp.mp.dps=50

def raw(q,N):
    q = mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0); L0arr=[]; L1arr=[]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
        L0arr.append(l0); L1arr.append(l1)
    return l0,l1,u0[0],u1[0],L0arr,L1arr

# The forward loop in raw builds L_b = (L_{b-1} + c_b + 2 q^b u_b)/dd_b. This IS the partial cumsum.
# So the source-0 resolvent partial sum L_b (l0 accumulator) and b0 = L_inf = l0 final.
# Let's confirm the 2nd-order homogeneous recursion that L_b (source0) satisfies:
# L_{b+1} - [(1+q) - 2(1-q)q^{2b+1}] L_b + q L_{b-1} = 0
q=mp.mpf('0.9'); N=int(50/(1-q))
b0,b1,t0,t1,L0,L1=raw(q,N)
# L0 is L_1..L_N. Prepend L_0=0.
L=[mp.mpf(0)]+L0  # L[b]=L_b for b=0..N
print('check homogeneous recursion source0:')
for b in range(1,6):
    lhs=L[b+1]-((1+q)-2*(1-q)*q**(2*b+1))*L[b]+q*L[b-1]
    print(f'b={b} residual={float(lhs):.3e}  L_b={float(L[b]):.6f}')
print('b0=L_inf=',float(b0),' L_N=',float(L[N]))
