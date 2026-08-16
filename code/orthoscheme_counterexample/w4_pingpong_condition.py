from fractions import Fraction as F
import itertools, random
def refl(v):
    n=4; d=sum(x*x for x in v)
    return tuple(tuple((F(1) if i==j else F(0))-2*v[i]*v[j]/d for j in range(n)) for i in range(n))
def diag(*d): return tuple(tuple(F(d[i]) if i==j else F(0) for j in range(4)) for i in range(4))
def mul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(4)) for j in range(4)) for i in range(4))
I4=diag(1,1,1,1)
R0=diag(-1,1,1,1); R4=diag(1,1,-1,1)
R1=refl((F(3),F(4),F(0),F(0))); R3=refl((F(0),F(0),F(5),F(12))); R2=refl((F(0),F(8),F(0),F(15)))
def vpmin(M,p):
    def vp(x):
        if x==0: return 10**9
        n,d=x.numerator,x.denominator; v=0
        while n%p==0: n//=p; v+=1
        while d%p==0: d//=p; v-=1
        return v
    return min(vp(M[i][j]) for i in range(4) for j in range(4))
C=[I4,R0,R4,mul(R0,R4)]
A=set()
for t in itertools.product([I4,R0],[I4,R2],[I4,R4]): A.add(mul(mul(t[0],t[1]),t[2]))
AmC=[g for g in A if g not in C]
# infinite part of B: powers of R0R1 (place 5) and R3R4 (place 13), times C
a01=mul(R0,R1); a34=mul(R3,R4)
def powm(M,k):
    X=I4
    for _ in range(abs(k)): X=mul(X,M)
    if k<0:
        # inverse = transpose for orthogonal
        X=tuple(tuple(X[j][i] for j in range(4)) for i in range(4))
    return X
def Belt(rng):
    k=rng.choice([-3,-2,-1,1,2,3]); l=rng.choice([-3,-2,-1,0,1,2,3])
    g=mul(powm(a01,k),powm(a34,l))
    return mul(g,rng.choice(C))

import random
rng=random.Random(20260816)
print("Weaker ping-pong condition: is v17 < 0 for EVERY alternating word with k>=1 A-letters?")
print("  k   trials   min v17 seen   any v17 >= 0 ?")
worst_overall=None
for k in range(1,10):
    mn=None; bad=0
    for trial in range(200):
        w=I4
        for i in range(k):
            w=mul(w,rng.choice(AmC))
            if i<k-1: w=mul(w,Belt(rng))
        v=vpmin(w,17)
        if mn is None or v>mn: mn=v          # the LEAST negative is the dangerous one
        if v>=0: bad+=1
    print(f"  {k}   200      max v17 = {mn:4d}      {'YES  <-- FAILS' if bad else 'no'}")
print()
print("(reporting the MAXIMUM v17, i.e. the closest to zero, since that is the")
print(" case that would break the argument.)")
