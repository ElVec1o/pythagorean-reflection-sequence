from fractions import Fraction as F
import sys
def refl(v):
    n=4; d=sum(x*x for x in v)
    return tuple(tuple((F(1) if i==j else F(0))-2*v[i]*v[j]/d for j in range(n)) for i in range(n))
def diag(*d): return tuple(tuple(F(d[i]) if i==j else F(0) for j in range(4)) for i in range(4))
def mul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(4)) for j in range(4)) for i in range(4))
I4=diag(1,1,1,1)
# Pythagorean directions, all different
def dirs(a,b): return (F(a),F(b))
R0=diag(-1,1,1,1)
R4=diag(1,1,-1,1)
def build(p1,p3,p2):
    a,b=p1; R1=refl((a,b,F(0),F(0)))          # reflection inside P1 = span(e1,e2)
    c,d=p3; R3=refl((F(0),F(0),c,d))          # reflection inside P2 = span(e3,e4)
    e,f=p2; R2=refl((F(0),e,F(0),f))          # reflection on the MIXED plane span(e2,e4)
    return [R0,R1,R2,R3,R4]
def envelope4(D):
    # W_4(t) = (1+t)^3 / K_5,  K_5 = 1 - 2t - t^2 + t^3
    num=[1,3,3,1]; den=[1,-2,-1,1]
    s=[]
    for k in range(D+1):
        c=num[k] if k<len(num) else 0
        for j in range(1,k+1):
            if j<len(den): c-=den[j]*s[k-j]
        s.append(c)
    return s
G=build(dirs(3,4),dirs(5,12),dirs(8,15))
# check the Gamma_4 relations: commute iff |i-j|>=2
print("relation check (want commute exactly when |i-j|>=2):")
ok=True
for i in range(5):
    for j in range(i+1,5):
        com = mul(G[i],G[j])==mul(G[j],G[i])
        want = (j-i)>=2
        if com!=want: ok=False; print(f"   MISMATCH i={i} j={j}: commute={com} want={want}")
print("   all relations correct" if ok else "   RELATIONS WRONG")
for i in range(5):
    if mul(G[i],G[i])!=I4: print(f"   R_{i} not an involution")
env=envelope4(14)
print(f"\nenvelope spheres: {env[:10]}")
seen={I4}; front=[I4]
for d in range(1,int(sys.argv[1]) if len(sys.argv)>1 else 9):
    nf=[]
    for X in front:
        for g in G:
            Y=mul(X,g)
            if Y not in seen: seen.add(Y); nf.append(Y)
    front=nf
    tag="MATCH" if len(nf)==env[d] else f"DEVIATES (env {env[d]})"
    print(f"  d={d:2d}: sphere {len(nf):7d}   {tag}", flush=True)
    if len(nf)!=env[d]: break
