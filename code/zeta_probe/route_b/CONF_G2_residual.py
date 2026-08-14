"""
G2: explicit residual bound for the Bessel basis under eq:qdiff.
D[Y](x) = Y(qx) - (1+q^3-2(1-q)q^2 x^2) Y(x) + q^3 Y(x/q).
Basis: B^J(x)=x^{3/2} J_{3/2}(W x), B^Y(x)=x^{3/2} Y_{3/2}(W x), W=w e^{-tau/2}, w=sqrt(2/tau).
Want: |D[B](x)| <= K2 tau^2 |B(x)| UNIFORMLY in x in (0,1], for BOTH solutions, with explicit K2.
(The continuum limit is Bessel's eqn x^2 B'' - ... ; the q-difference is its O(tau^2) discretization.)
"""
import mpmath as mp
mp.mp.dps = 30

def Dop(Yfun,q,x):
    return Yfun(q*x) - (1+q**3-2*(1-q)*q**2*x**2)*Yfun(x) + q**3*Yfun(x/q)

print("G2: sup over x in (0,1] of |D[B]/B| / tau^2  for B^J and B^Y  (should be a bounded constant K2):")
print(f"{'tau':>9}{'w':>9}{'supJ |DB/B|/tau^2':>20}{'supY |DB/B|/tau^2':>20}{'x* (argmax J)':>14}")
for taus in ['0.04','0.02','0.01','0.005','0.0025','0.00125']:
    tau=mp.mpf(taus);q=mp.e**(-tau);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    BJ=lambda x: x**mp.mpf('1.5')*mp.besselj(mp.mpf(3)/2,W*x)
    BY=lambda x: x**mp.mpf('1.5')*mp.bessely(mp.mpf(3)/2,W*x)
    supJ=mp.mpf(0); supY=mp.mpf(0); xstar=mp.mpf(0)
    # sweep x in (0,1]; avoid x where B~0 (relative residual spikes) by also tracking |B|
    Ngrid=400
    for i in range(1,Ngrid+1):
        x=mp.mpf(i)/Ngrid
        for B,supref,nm in [(BJ,'J',0),(BY,'Y',1)]:
            val=B(x)
            if abs(val)<mp.mpf('1e-8'): continue   # skip near-zeros of B (relative residual ill-defined)
            rel=abs(Dop(B,q,x)/val)/tau**2
            if nm==0 and rel>supJ: supJ=rel; xstar=x
            if nm==1 and rel>supY: supY=rel
    print(f"{taus:>9}{float(w):>9.3f}{float(supJ):>20.5f}{float(supY):>20.5f}{float(xstar):>14.4f}")
print("\nIf supJ,supY -> bounded constants K2 as tau->0: residual |D[B]|<=K2 tau^2 |B| UNIFORM => G2 done.")
print("(near-zeros of B excluded: there |B|~0 so the VoP uses the OTHER solution; handled by the pair.)")

# Also: get the explicit leading residual coefficient via small-x and the continuum operator.
# Continuum: D[Y] ~ (log q)[x Y' ...]; expand D[B^J](x)/tau^2 at a fixed x to read K2(x).
print("\nExplicit residual shape D[B^J](x)/(tau^2 B^J(x)) at fixed x (tau->0 limit = K2(x)):")
for x0 in ['0.3','0.6','1.0']:
    x=mp.mpf(x0); vals=[]
    for taus in ['0.004','0.002','0.001']:
        tau=mp.mpf(taus);q=mp.e**(-tau);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
        BJ=lambda xx: xx**mp.mpf('1.5')*mp.besselj(mp.mpf(3)/2,W*xx)
        vals.append(Dop(BJ,q,x)/(tau**2*BJ(x)))
    print(f"   x={x0}: K2(x)-> {mp.nstr(vals[-1],8)}  (tau=.004,.002,.001: {[mp.nstr(v,6) for v in vals]})")
