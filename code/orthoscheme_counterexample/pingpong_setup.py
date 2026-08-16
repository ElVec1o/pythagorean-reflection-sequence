from fractions import Fraction as F
def vp(x,p):
    if x==0: return None
    n,d=x.numerator,x.denominator; v=0
    while n%p==0: n//=p; v+=1
    while d%p==0: d//=p; v-=1
    return v
def lin_refl(m,n):
    d=sum(x*x for x in m)
    return tuple(tuple((F(1) if i==j else F(0))-2*m[i]*m[j]/d for j in range(n)) for i in range(n))
a=[1,2,3]; n=3
M=[(F(1),F(0),F(0)),(F(a[1]),F(-a[0]),F(0)),(F(0),F(a[2]),F(-a[1])),(F(0),F(0),F(1))]
G=[lin_refl(m,n) for m in M]
print("legs (1,2,3);  |m_1|^2 =",a[0]**2+a[1]**2," |m_2|^2 =",a[1]**2+a[2]**2)
for p in (5,13):
    print(f"--- valuation at p={p} ---")
    for k,g in enumerate(G):
        vs=[vp(x,p) for row in g for x in row if x!=0]
        print(f"  R_{k}: min valuation {min(vs)}   {'INTEGRAL' if min(vs)>=0 else 'NOT integral'}")
# isotropy of x^2+y^2+z^2 over Q_p (p odd): check mod p
for p in (5,13):
    sq={(i*i)%p for i in range(p)}
    hit=[(x,y,z) for x in range(p) for y in range(p) for z in range(p)
         if (x,y,z)!=(0,0,0) and (x*x+y*y+z*z)%p==0]
    print(f"x^2+y^2+z^2 isotropic mod {p}: {len(hit)>0}  e.g. {hit[0] if hit else None}"
          f"  -> SO_3 split over Q_{p}, building is a TREE")
# check that each generator is orthogonal (preserves the form)
def mul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)) for i in range(3))
def tr(A): return tuple(tuple(A[j][i] for j in range(3)) for i in range(3))
I=tuple(tuple(F(1) if i==j else F(0) for j in range(3)) for i in range(3))
print("all generators orthogonal:", all(mul(tr(g),g)==I for g in G))
