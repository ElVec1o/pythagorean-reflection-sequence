import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# t0=b1 observed. Let's understand raw u1 recursion. Source c1=2q^{2b} (deposit-2 channel).
# The bulk resolvent for source 2q^{2b}: build Lambert with alpha(k)=2q^{2(k+1)}/(1-q^{k+1})?? but
# the FORCING also feeds through v (cocycle vb). Need to mirror EXACTLY the u-recursion which is:
#   u[b-1]=u[b]*(1+2q2b)+qb*c + vb*(c+2qb*u[b]),  c=source_b
# This is NOT a pure Lambert telescope; it's resolvent of full (I-M). So t1 = [(I-M)^{-1} E1]_0 with
# E1_b=2q^{2b}, vs b0-channel E0_b=2q^b. Both share kernel M. b0=G0b proven => the kernel resolvent
# diagonal IS the bulk resolvent. So t1 = same resolvent applied to a DIFFERENT source vector.
# In Lambert-block language: bulk resolvent (I-M)^{-1} with M[b,a]=2q^b(q^max(a,b)+q^{a+b}*?).
# b0 = sum_b [(I-M)^{-1}E0]_b ... actually b0=l0 accumulates. Let me just directly test whether
# s=(q/p)t1 equals a cross-block ratio.

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q)
    S0b=Sblk(0,q); S1b=Sblk(1,q)
    Sig0=Sigma(0,q); Sig1=Sigma(1,q)
    s=(q/(1-q))*t1
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,s=s,
                S0b=S0b,S1b=S1b,Sig0=Sig0,Sig1=Sig1,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]

# Build P12 as a NEW q-Pochhammer series like Se/So but with the t1 source.
# Closed form memory: t1=P12/Se, P12=sum_j (-2(1-q))^j q^{?}/(q;q)_{?}. Let's reverse-engineer
# P12 = t1*Se and fit a q-series. First just print P12 to find pattern.
print("P12 = t1*Se, and candidate combos:")
print(f"{'q':>7} {'P12':>14} {'b1':>12} {'S0b':>12} {'So':>12}")
for q in qs:
    d=block(q); P12=d['t1']*d['Se']
    print(f"{float(q):>7.3f} {float(P12):>14.8f} {float(d['b1']):>12.6f} {float(d['S0b']):>12.6f} {float(d['So']):>12.6f}")

# The b1 channel: b1=l1 accumulates source 2q^{2b}. Is b1 itself = a bulk resolvent of source-2?
# Define bulk resolvent applied to source E1_b=2q^{2b}: mirror raw but that's exactly what u1/l1 do.
# So l1=b1 IS that resolvent. We want a LAMBERT/Pochhammer closed form for it analogous to S0b.
# Test: b1 ?= S0b shifted, or b1 = (something)*Sig.
# Recall raw l1 source 2q^{2b} vs l0 source 2q^b. The Lambert block S0b had source alpha=2q^{k+1}.
# A source 2q^{2(k+1)} block 'T0b':
def Tsrc(k,q): return 2*q**(2*(k+1))/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Tblk(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Tsrc(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>60: break
    return tot
print("\n[B1] b1 vs source-2 bulk block ratio T0b/(1-S1b):")
for q in qs:
    d=block(q); T0=Tblk(0,q)
    print(f"  q={float(q):.3f}: b1={float(d['b1']):+.8f}  T0b/Se={float(T0/d['Se']):+.8f}  T0b={float(T0):+.8f}")
