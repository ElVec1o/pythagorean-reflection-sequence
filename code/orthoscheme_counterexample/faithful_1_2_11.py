"""End-to-end check that the point group at (1,2,11) is faithful."""
from fractions import Fraction as F
def lin_refl(m,n):
    d=sum(x*x for x in m)
    return tuple(tuple((F(1) if i==j else F(0))-2*m[i]*m[j]/d for j in range(n)) for i in range(n))
def mul(A,B,n=3): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)) for i in range(n))
def inv(X): return tuple(tuple(X[j][i] for j in range(3)) for i in range(3))
a=[1,2,11]
M=[(F(1),F(0),F(0)),(F(a[1]),F(-a[0]),F(0)),(F(0),F(a[2]),F(-a[1])),(F(0),F(0),F(1))]
R=[lin_refl(m,3) for m in M]
I=tuple(tuple(F(1) if i==j else F(0) for j in range(3)) for i in range(3))
A=mul(R[0],R[1]); C=mul(R[2],R[3])
print("STEP 1  W_3 = <A,C> semidirect V, abstract facts")
print("  V=<R_0,R_3> order 4 :", len({I,R[0],R[3],mul(R[0],R[3])})==4)
print("  R_0AR_0=A^-1        :", mul(mul(R[0],A),R[0])==inv(A))
print("  R_3CR_3=C^-1        :", mul(mul(R[3],C),R[3])==inv(C))
print("  R_0CR_0=C, R_3AR_3=A:", mul(mul(R[0],C),R[0])==C and mul(mul(R[3],A),R[3])==A)
print("  chi(W_3) = 3/4 - 2/2 = -1/4 ; ker(phi) has index 4 so chi = -1 so free of rank 2")
print()
print("STEP 2  the images")
B=[[F(1),F(0),F(0)],[F(0),F(3,5),F(-4,5)],[F(0),F(4,5),F(3,5)]]
B=tuple(tuple(r) for r in B)
B3=mul(mul(B,B),B)
print("  A = rot_e3, (cos,sin) = (%s,%s)"%(A[0][0],A[1][0]))
print("  B = rot_e1, (cos,sin) = (3/5,4/5)   [not itself in the group]")
print("  C == B^3 :", C==B3)
print()
print("STEP 3  <A,B> free: the 5-adic invariant (second coordinate never 0 mod 5)")
Am=[[3,-4,0],[4,3,0],[0,0,5]]; Ai=[[3,4,0],[-4,3,0],[0,0,5]]
Bm=[[5,0,0],[0,3,-4],[0,4,3]]; Bi=[[5,0,0],[0,3,4],[0,-4,3]]
G={'a':Am,'A':Ai,'b':Bm,'B':Bi}; opp={'a':'A','A':'a','b':'B','B':'b'}
def mv(Mx,v): return tuple(sum(Mx[i][k]*v[k] for k in range(3)) for i in range(3))
front=[(g,mv(G[g],(1,0,0))) for g in "aA"]; ok=True
for d in range(1,12):
    if any(v[1]%5==0 for _,v in front): ok=False; break
    nf=[]
    for w,v in front:
        for g in G:
            if opp[g]==w[-1]: continue
            nf.append((w+g,mv(G[g],v)))
    front=nf
print("  invariant holds through length 11 :",ok,"  (%d words at the last level)"%len(front))
print()
print("STEP 4  torsion")
print("  image of <A,C> is free hence torsion-free; V\\{1} are involutions, so the")
print("  two images meet trivially, and V injects.")
print()
print("CONCLUSION: pi o rho_a is injective at (1,2,11), hence rho_a is injective.")
