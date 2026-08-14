import mpmath as mp
mp.mp.dps=70
def raw(q,N):
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        v[b-1]=(v[b]*(1+2*q2b)+2*q3b)/dd
    return v
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-140) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
# t1 = v[0]. The v-Riccati: v_{b-1}=(v_b(1+2q^{2b})+2q^{3b})/(1-2q^{2b}-2q^b v_b), v_inf=0.
# This is a CONTINUED FRACTION. Is v[0] a known block? Note the relaxed-V resolvent b0 used
# the SAME v. So v IS the relaxed bulk Riccati. The block Sb is its 'resolvent'. Let me test
# whether v[0] = -Sb(1)+ ... no. Let me see v[0] as continued fraction value vs a block.
# Actually: the recursion for u1 had t1=u1[0]; we found t1=v[0]. Let me VERIFY robustly:
print("VERIFY t1 = v[0] (Riccati boundary), high precision:")
def raw_full(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c1=2*q2b
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    return u1[0],v[0]
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02']]:
    q=mp.e**(-tau);N=int(70/(1-q)); t1,v0=raw_full(q,N)
    print(f"  tau={float(tau):.3f}  t1={mp.nstr(t1,14)}  v[0]={mp.nstr(v0,14)}  diff={mp.nstr(abs(t1-v0),3)}")
print()
# So t1=v[0]=relaxed-bulk Riccati boundary. The relaxed bulk block B_V resolvent uses the SAME v.
# Now: s=g_V*t1=g_V*v[0]. The lem:Bbounded machinery is EXACTLY about this v-Riccati / B_s form factor.
# Pin the asymptotic of v[0]: at poles s->1/4 so v[0]~ (1/4)/g_V = (1-q)/(4q) ~ tau/4. Confirm
# v[0] ~ tau/4 at poles AND find its off-pole functional form:
print("v[0]=t1 functional asymptotic. s=g_V v0 ->1/4 at poles. Off-pole form?")
print(f"{'tau':>8} {'v0':>14} {'tau/4':>12} {'v0/tau':>10} {'g_V v0':>12}")
for tau in [mp.mpf(x) for x in ['0.05','0.02','0.01','0.005','0.002']]:
    q=mp.e**(-tau);N=int(70/(1-q)); v=raw(q,N); v0=v[0]; gV=q/(1-q)
    print(f"{float(tau):>8.4f} {mp.nstr(v0,10):>14} {mp.nstr(tau/4,8):>12} {float(v0/tau):>10.5f} {float(gV*v0):>12.6f}")
print()
# v[0] off-pole is NOT tau/4 (s oscillates). At poles it->tau/4. The pole condition is Sigma_1(travel)=1
# which is a SEPARATE block. So R2 says: AT the travel poles, g_V v0->1/4.
# Crucial: is v[0] expressible via Sb? Test the Mobius: v0 satisfies a fixed-pt-like relation.
# Try v0 = q*(1-?)... Let me test v0 against (S0b - S1b*something)/(1-S1b):
print("Hunt v0 block form via 2-term fit {S0b,S1b,1} at poles (where it's smooth ->tau/4):")
import itertools
qs=[poles[i] for i in [1,3,5]]
rows=[];rhs=[]
for q in qs:
    N=int(70/(1-q)); v=raw(q,N)
    rows.append([Sb(0,q),Sb(1,q),mp.mpf(1)]); rhs.append(v[0])
sol=mp.lu_solve(mp.matrix(rows),mp.matrix(rhs))
print("  fit v0=a*S0b+b*S1b+c:",[mp.nstr(x,6) for x in sol])
for i in [7,11]:
    q=poles[i];N=int(70/(1-q));v=raw(q,N)
    pred=sol[0]*Sb(0,q)+sol[1]*Sb(1,q)+sol[2]
    print(f"  test pole m={i+1}: v0={mp.nstr(v[0],10)} pred={mp.nstr(pred,10)} diff={mp.nstr(abs(v[0]-pred),3)}")
