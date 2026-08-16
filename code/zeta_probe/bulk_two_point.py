import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur

def basis(qm,N):
    """Backward recursion H_b = (p_b H_{b+1} - H_{b+2})/q for the two modes at infinity."""
    p=lambda b: 1+qm-2*qm**(1+2*b)*(1-qm)
    u=[mp.mpf(0)]*(N+3); v=[mp.mpf(0)]*(N+3)
    u[N+2]=mp.mpf(1);      u[N+1]=mp.mpf(1)          # constant mode
    v[N+2]=qm**(N+2);      v[N+1]=qm**(N+1)          # decaying mode
    for b in range(N,0,-1):
        u[b]=(p(b)*u[b+1]-u[b+2])/qm
        v[b]=(p(b)*v[b+1]-v[b+2])/qm
    return u,v

print("Closed form:  c2 = -2/(1-q) pinned by B_inf = 0;")
print("  c1 = 2 (v_1 - g V) / ((1-q)(u_1 - g U)),   U = sum q^a (u_{a+1}-u_a),  V likewise;")
print("  beta = c1 U + c2 V ;   B_V = c1 - beta g .")
print()
print("  m   B_V (closed form)   B_V (direct)      rel.diff")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); g=qm/(1-qm)
    u,v=basis(qm,N)
    U=sum(qm**a*(u[a+1]-u[a]) for a in range(1,N+1))
    V=sum(qm**a*(v[a+1]-v[a]) for a in range(1,N+1))
    c2=-2/(1-qm)
    c1=(-c2*(v[1]-g*V))/(u[1]-g*U)
    beta=c1*U+c2*V
    BV=c1-beta*g
    P=bulk_solve(qm,mp.mpf(1),N); BVd=sum(P[1:])
    print(f"  {m}   {mp.nstr(BV,10):>16}   {mp.nstr(BVd,10):>13}   {mp.nstr(abs(BV-BVd)/abs(BVd),4)}")
