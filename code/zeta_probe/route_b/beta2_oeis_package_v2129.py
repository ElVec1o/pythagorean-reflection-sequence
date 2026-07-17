import json, os
M=300
def mul(a,b):
    c=[0]*(M+1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j]+=ai*b[j]
    return c
def qpow(n):
    c=[0]*(M+1)
    if n<=M: c[n]=1
    return c
def inv_poch(m):
    c=[0]*(M+1); c[0]=1
    for part in range(1,m+1):
        for n in range(part,M+1): c[n]+=c[n-part]
    return c
# ---- A-candidate 1: a(n) = [q^n] (-G(q,1)), the m=0 lattice value ----
G1=[0]*(M+1); G1[0]=1
k=1
while k*(k-1)<=M:
    t=mul(qpow(k*(k-1)),inv_poch(2*k))
    G1=[g+((-1)**k)*x for g,x in zip(G1,t)]
    k+=1
negG1=[-x for x in G1]
assert negG1[0]==0 and negG1[1]==1
# verify lattice identity at m=0 to order 300 exactly:
# (q;Q)oo * G(q,1) = -(Q;Q)oo * sum_r (-1)^r q^{(1+r)^2} / ((Q;Q)_r (Q;Q)_{1+r})
def pochoo(step,start):
    c=qpow(0)
    e=start
    while e<=M:
        c=[c[j]-(c[j-e] if j>=e else 0) for j in range(M+1)]
        e+=step
    return c
def inv_pochQ(n):
    c=[0]*(M+1); c[0]=1
    for part in range(2,2*n+1,2):
        for j in range(part,M+1): c[j]+=c[j-part]
    return c
qQ=pochoo(2,1); QQ=pochoo(2,2)
lhs=mul(qQ,G1)
Ssum=[0]*(M+1)
r=0
while (1+r)**2<=M:
    t=mul(qpow((1+r)**2),mul(inv_pochQ(r),inv_pochQ(1+r)))
    Ssum=[s+((-1)**r)*x for s,x in zip(Ssum,t)]
    r+=1
rhs=[-x for x in mul(QQ,Ssum)]
print("lattice identity m=0 exact to order 300:",lhs==rhs)
# ---- A-candidate 2: u2 coefficients ----
u2=json.load(open("ulattice_300.json"))["2"]
OUT="/Users/vico/Documents/elvec1o/certify_run/paper/oeis"
os.makedirs(OUT,exist_ok=True)
def listing(seq,n0,count=36):
    return ", ".join(str(x) for x in seq[n0:n0+count])
with open(f"{OUT}/bfile_negG_q1.txt","w") as f:
    for n in range(M+1): f.write(f"{n} {negG1[n]}\n")
with open(f"{OUT}/bfile_u2.txt","w") as f:
    for n in range(M+1): f.write(f"{n} {u2[n]}\n")
print()
print("=== -G(q,1): first 36 terms (offset 0) ===")
print(listing(negG1,0))
print()
print("=== u2: first 36 terms (offset 0) ===")
print(listing(u2,0))
