import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# t1=u1[0], source c1=2q^{2b}.  We proved b0=u0-channel = S0b/Se with S0b the source-q^b Lambert block.
# The u-recursion (forward L accumulation) is LINEAR in the source. So both l0 (source 2q^b => b0) and
# l1 (source 2q^{2b} => b1) are (I-M)^{-1} applied to different sources, M shared.  Likewise u0[0]=t0,
# u1[0]=t1 are the b=0 component of the BACKWARD pass resolvent.
# The proven dictionary b0=S0b/Se suggests t1 = (source-2 numerator block)/Se as well.
# Define the source-2 numerator block by MIRRORING S0b but with source weight 2q^{2(k+1)}:
#   S0b: alpha(k)=2q^{k+1}/(1-q^{k+1}); the *2 source => alpha2(k)=2q^{2(k+1)}/(1-q^{k+1})? tested-> no.
# The correct partner must use the SAME C/gamma cocycle but the source for t1 is c1=2q^{2b}, AND t1 is
# the u1[0] BACKWARD component (the t0/t1=u[0]) NOT the forward l1=b1. Different block!
# t0=b1 was observed. Let me re-examine: t0=u0[0], b1=l1. They coincided numerically. Check t1 vs t0.
def block(q):
    N=int(60/(1-q)); tau=-mp.log(q)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q); S0b=Sblk(0,q); S1b=Sblk(1,q)
    return dict(q=q,tau=tau,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,S0b=S0b,S1b=S1b,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]
print("t0 vs b1 (do they coincide exactly?), t1 vs other:")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: t0={float(d['t0']):+.10f} b1={float(d['b1']):+.10f} diff={float(abs(d['t0']-d['b1'])):.1e} | t1={float(d['t1']):+.10f}")

# So t0=b1 exactly (resolvent symmetry). Now t1 is the (1,1)-ish entry. P12=t1*Se.
# Define the SOURCE-2 forward block b1=l1 = (numerator-2)/Se by analogy: numerator-2 = b1*Se.
print("\nDefine N2 := b1*Se (analog of S0b=b0*Se). And t1*Se=P12. Compare N2 and a Lambert block:")
# Lambert block with source 2q^{2(k+1)} and SAME gamma cocycle:
def src2(k,q): return 2*q**(2*(k+1))/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Blk2(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=src2(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>60: break
    return tot
for q in qs:
    d=block(q)
    N2=d['b1']*d['Se']; B2=Blk2(0,q)
    print(f"  q={float(q):.3f}: N2=b1*Se={float(N2):+.10f}  Blk2(0)={float(B2):+.10f}  diff={float(abs(N2-B2)):.1e}")
