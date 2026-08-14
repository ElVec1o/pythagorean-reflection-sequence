import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Need the t1-related bulk block. t1=P12/Se, s=(q/p)t1.
# The bulk resolvent has a SECONDARY (source-1) channel. raw returns t1=u1[0].
# Hypothesis: there's a bulk block S_0^{(1)} or the "b1" companion.
# From bulk_riccati: B(q,y)=(b0+g*c)/(1-g*t1), c=t0*b1-b0*t1, g=q/(1-qy).
# Let's get the full set and look for S-block partners for t0,t1,b1.

# Additional lem:cos bulk blocks at higher index? The bulk resolvent G_k=S0b shifted.
# Try: define bulk block with source weight q^{2(k+1)} (the c1=2q2b source) -> a DIFFERENT Lambert sum.
def alpha1_b(k,q): return 2*q**(2*(k+1))/(1-q**(k+1))   # source c1=2q^{2b}
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sblk1(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha1_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>60: break
    return tot

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q)
    S0b=Sblk(0,q); S1b=Sblk(1,q)
    S0b1=Sblk1(0,q); S1b1=Sblk1(1,q)
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,
                S0b=S0b,S1b=S1b,S0b1=S0b1,S1b1=S1b1,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]
print("raw internals + source-1 bulk blocks:")
print(f"{'q':>7} {'t1':>12} {'t0':>12} {'b1':>12} | {'S1b1':>12} {'S0b1':>12}")
for q in qs:
    d=block(q)
    print(f"{float(q):>7.3f} {float(d['t1']):>12.6f} {float(d['t0']):>12.6f} {float(d['b1']):>12.6f} | {float(d['S1b1']):>12.6f} {float(d['S0b1']):>12.6f}")

print("\n[T1] test t1 ?= -S1b1/Se  or  t1*Se=P12 ?= -S1b1 (since source c1=2q2b)")
for q in qs:
    d=block(q)
    P12=d['t1']*d['Se']
    print(f"  q={float(q):.3f}: P12=t1*Se={float(P12):+.10f}  S1b1={float(d['S1b1']):+.10f}  "
          f"-S1b1={float(-d['S1b1']):+.10f}  diff(P12,-S1b1)={float(abs(P12+d['S1b1'])):.1e}")

print("\n[T1b] test t1 ?= S1b1/(1-S1b)=S1b1/Se directly:")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: t1={float(d['t1']):+.10f}  S1b1/Se={float(d['S1b1']/d['Se']):+.10f}  "
          f"diff={float(abs(d['t1']-d['S1b1']/d['Se'])):.1e}")
