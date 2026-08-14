import mpmath as mp
mp.mp.dps=70
def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        v[b-1]=(v[b]*(1+2*q2b)+2*q3b)/dd
    return v[0]
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-140) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
# t1=v[0] is the relaxed-V bulk Riccati boundary. It is the SAME object as B_s (the lem:Bbounded
# form factor for the BULK block). The relaxed bulk block B_V resolvent denominator is 1-S1b; its
# pole is the bulk pole S1b=1. The travel poles (Sigma_1^travel=1) are DIFFERENT, and there 1-S1b!=0.
# CONCLUSION CHECK: t1=v[0], so the V machinery (lem:Bbounded) controls t1 directly. The remaining
# fact R2 (g_V v[0]->1/4 at travel poles) is the asymptotic of THIS form factor.
#
# Test the LEADING asymptotic of v[0] off-pole: the relaxed bulk Riccati ~ has the lem:cos engine.
# Conjecture: v[0] ~ (sin w / w - related). Let me fit v[0] to the (1-cos w),(sin w / w) basis * tau.
print("Off-pole leading asymptotic of t1=v[0]:  test v0 vs combos of cos w, sin w, 1, scaled by tau")
print(f"{'tau':>9} {'w':>9} {'v0':>15} {'(1-cosw)?':>12} {'1-S1b=Se':>12} {'v0/Se':>12} {'v0*g_V':>12}")
for tau in [mp.mpf(x) for x in ['0.02','0.01','0.005','0.002','0.001','0.0005']]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau); N=int(70/(1-q)); v0=raw(q,N); gV=q/(1-q)
    Se=1-Sb(1,q)
    print(f"{float(tau):>9.4f} {float(w):>9.3f} {mp.nstr(v0,11):>15} {mp.nstr(1-mp.cos(w),8):>12} {mp.nstr(Se,8):>12} {mp.nstr(v0/Se,8):>12} {mp.nstr(v0*gV,8):>12}")
print()
# v0*g_V is exactly s (oscillates off-pole). Now AT the travel poles, s->1/4. Let me show the
# R2 limit's structure: s = g_V v0. Need its value at q where Sigma_1^travel=1.
# Test: at poles, does s = (1-S1b)/... no. Let me just confirm s->1/4 and (s-1/4) ~ tau/16 with
# the s expressed PURELY via the Riccati v0 (which IS lem:Bbounded's object). High-m robust:
print("R2 final (robust): s=g_V*v[0] -> 1/4 at travel poles; (s-1/4)/tau -> 1/16:")
print(f"{'m':>3} {'tau':>10} {'s=g_V v0':>14} {'|s-1/4|':>10} {'(s-1/4)/tau':>13}")
for m in [1,2,4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); gV=q/(1-q); N=int(90/(1-q)); v0=raw(q,N); s=gV*v0
    print(f"{m:>3} {float(tau):>10.6f} {float(s):>14.10f} {float(abs(s-mp.mpf(1)/4)):>10.2e} {float((s-mp.mpf(1)/4)/tau):>13.8f}")
