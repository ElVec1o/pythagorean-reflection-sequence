import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# The cocycle gives the FULL sequences, not just the endpoint. Track the partial cocycle to express
# P12 via a Wronskian/reduction-of-order sum over the two columns.
# M_n = [[1+2q2n, -2qn],[2q3n, 1-2q2n]], det M_n = (1+2q2n)(1-2q2n)+4 q^{4n} = 1-4q^{4n}+4q^{4n}=1. SL2!
# P = M_N ... M_1.  Columns c1=(P11,P21)=P(1,0)^T, c2=(P12,P22)=P(0,1)^T.
# Reduction of order: with one solution (the P22=Se / P12 column), the partner (P11,P21) column is
# obtained via Wronskian (det=1). The TOP entries P11,P12 both solve the same 2nd-order recursion in n.
# Let me extract the scalar recursion for the TOP row. From M_n: x_n = (1+2q2n)x_{n-1} - 2qn y_{n-1},
# y_n = 2 q3n x_{n-1} + (1-2q2n) y_{n-1}.  Eliminate y: y_{n-1}=[(1+2q2n)x_{n-1}-x_n]/(2qn).
# This gives a 2nd order recursion for x (=top entry). Both P11-seq and P12-seq satisfy it.
# => P12 = P11 * sum_n W_n / (P11_n P11_{n-1})  (reduction of order), W=Wronskian.
# Simpler: just verify the master reduced facts and the cross-checks via SL2 already proven.

# What we CAN state rigorously: t1 = P12/Se, and P12 = (1 - P11 Se)/(-S0b)?? no: det: P11 Se + P12 S0b=1
# Wait det P=1 with P=[[P11,P12],[P21,P22]]: P11 P22 - P12 P21 = 1 => P11 Se - P12(-S0b)=1
# => P11 Se + P12 S0b = 1. (confirmed). This RELATES P11,P12 but doesn't pin either alone.

# DECISIVE: express t1 directly. t1=P12/Se. From the resolvent, there's ALSO t0=u0[0]=b1=S1b/Se.
# And the OTHER resolvent entry. Let me get the full inverse of (I-M_resolvent) relation.
# Actually simplest rigorous path for R2: show t1 = (q/p)^{-1} * s and we proved s numerically.
# For the DICTIONARY we just need: is P12 a lem:cos block? Test P12 vs Sigma (TRAVEL) blocks:
def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]
print("P12 vs TRAVEL blocks Sigma_0,Sigma_1 and combos:")
for q in qs:
    N=int(60/(1-q)); p=1-q
    P12,P22,P11,P21=cocycle_full(q,N)
    Sig0=Sigma(0,q); Sig1=Sigma(1,q); So=So_clf(q); Se=Se_clf(q)
    # candidate: P12 = (So - p*P11*?)/... ; try P12 vs So, So-Se, etc.
    print(f" q={float(q):.2f}: P12={float(P12):+.8f}  So={float(So):+.8f}  So-... | Sig0={float(Sig0):+.7f} Sig1={float(Sig1):+.7f}")

# Direct: P12 satisfies P11 Se + P12 S0b=1. Pair with the b1 identity (t0=b1=S1b/Se) and the resolvent
# relation s=(q/p)P12/Se. Numerically pin P12*w/tau->1/4. Let me just lock the two reduced facts hard:
print("\nLOCK: along ALL poles m=1..40, (a) Se*w->1, (b) P12*w/tau->1/4, (c) b0*tau->2:")
print(f"{'m':>3} {'Se*w':>11} {'P12*w/tau':>11} {'b0*tau':>11} {'s':>11}")
for m in range(1,41):
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle_full(q,N)
    if m in (1,2,3,5,8,12,16,24,32,40):
        print(f"{m:>3} {float(P22*w):>11.8f} {float(P12*w/tau):>11.8f} {float(b0*tau):>11.8f} {float((q/p)*t1):>11.8f}")
