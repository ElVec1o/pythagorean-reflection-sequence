#!/usr/bin/env python3
"""Positive-control sanity checks for the three detectors in wf_guess.py.
We feed KNOWN sequences that DO satisfy each relation type and confirm the
exact-arithmetic nullspace/consistency machinery flags them."""

import importlib.util, sys
spec = importlib.util.spec_from_file_location("wg", "/tmp/wf_guess.py")
# We just reuse the helper functions by exec-ing the top part. Simpler: re-import.
sys.argv = ["wf_guess.py"]
import types
src = open("/tmp/wf_guess.py").read()
# strip the __main__ block to avoid running full battery
src = src.split('if __name__ == "__main__":')[0]
mod = types.ModuleType("wg")
exec(src, mod.__dict__)

from fractions import Fraction as Fr
nullspace = mod.nullspace
to_int_vector = mod.to_int_vector
series_mul = mod.series_mul

# ---- Control A: Fibonacci satisfies u_n = u_{n-1}+u_{n-2}. Const-rec detector. ----
F = [1,1]
for _ in range(40):
    F.append(F[-1]+F[-2])
Ffr = [Fr(v) for v in F]
N = len(F)
# build order-2 system u_n - c1 u_{n-1} - c2 u_{n-2} = 0
L=2
ns=list(range(L,N))
A=[[Ffr[n-i] for i in range(1,L+1)] for n in ns]
b=[Ffr[n] for n in ns]
aug=[A[k][:]+[b[k]] for k in range(len(ns))]
# reuse elimination idea: solve first two, check rest
import copy
M=[row[:] for row in aug]
# Gaussian elim on first L cols
rr=0; piv_cols=[]
for c in range(L):
    p=None
    for i in range(rr,len(M)):
        if M[i][c]!=0: p=i;break
    if p is None: continue
    M[rr],M[p]=M[p],M[rr]
    pv=M[rr][c]; M[rr]=[x/pv for x in M[rr]]
    for i in range(len(M)):
        if i!=rr and M[i][c]!=0:
            f=M[i][c]; M[i]=[a-f*bb for a,bb in zip(M[i],M[rr])]
    piv_cols.append(c); rr+=1
consistent=all(not(all(x==0 for x in row[:L]) and row[L]!=0) for row in M)
sol=[Fr(0)]*L
for i,c in enumerate(piv_cols): sol[c]=M[i][L]
print("Control A (Fibonacci const-rec): consistent=%s  sol=%s  expect [1,1]"%(consistent,sol))

# ---- Control B: algebraic. F = 1/(1-x-x^2) is the Fib GF: (1-x-x^2)F - 1 = 0.
# Test the algebraic detector finds a relation for dy>=1. Our test starts dy=2,
# but a dy=1 relation is also captured as a special dy=2 nullspace? No - relation
# is linear in F. Build monomials x^i F^j and confirm nullspace dim>=1.
Nser=20
Fib_gf=[Fr(v) for v in F[:Nser]]  # coeffs 1,1,2,3,5,... = u_n with u0=1
# Actually 1/(1-x-x^2) = 1 + x + 2x^2 + 3x^3 + 5x^4... = F[1],F[2],...? Fib[1..]=1,1,2,3,5
gf=[Fr(1),Fr(1),Fr(2),Fr(3),Fr(5),Fr(8),Fr(13),Fr(21),Fr(34),Fr(55),Fr(89),
    Fr(144),Fr(233),Fr(377),Fr(610),Fr(987),Fr(1597),Fr(2584),Fr(4181),Fr(6765)]
# monomials: F^0=1, F^1=gf, plus x^i. dy=1,dx=2 -> unknowns (3)*(2)=6
def smul(a,b,t): return series_mul(a,b,t)
Fpow={0:[Fr(1)]+[Fr(0)]*(Nser-1),1:gf[:Nser]}
cols=[];info=[]
dx,dy=2,1
for j in range(dy+1):
    fj=Fpow[j]
    for i in range(dx+1):
        vec=[Fr(0)]*Nser
        for k in range(Nser):
            if k-i>=0: vec[k]=fj[k-i]
        cols.append(vec);info.append((i,j))
ncols=len(cols)
Mat=[[cols[c][row] for c in range(ncols)] for row in range(Nser)]
rank,basis=nullspace(Mat,ncols)
print("Control B (Fib GF algebraic, dx=2,dy=1): nulldim=%d (expect>=1)"%len(basis))
if basis:
    iv=to_int_vector(basis[0])
    terms=[("(%d)x^%d F^%d"%(c,i,j)) for (i,j),c in zip(info,iv) if c!=0]
    print("   relation:", " + ".join(terms), "= 0   (expect (1-x-x^2)F - 1)")

# ---- Control C: holonomic. n*u_n - ... Catalan numbers satisfy
# (n+2) C_{n+1} = (4n+2) C_n  -> order1, deg1. Use detector logic.
C=[1]
for n in range(0,30):
    C.append(C[-1]*2*(2*n+1)//(n+2))
Cfr=[Fr(v) for v in C]
Nc=len(C)
# recurrence in u_n,u_{n-1}: (n+1)*u_n - (4n-2)*u_{n-1}=0 for n>=1
# p0(n)=n+1 deg1, p1(n)=-(4n-2) deg1. order r=1,d=1 unknowns=4
r,d=1,1
ns=list(range(r,Nc))
Mh=[]
for n in ns:
    row=[]
    for i in range(r+1):
        un=Cfr[n-i]
        for e in range(d+1):
            row.append(Fr(n)**e*un)
    Mh.append(row)
rank,basis=nullspace(Mh,(r+1)*(d+1))
print("Control C (Catalan holonomic, r=1,d=1): nulldim=%d (expect>=1)"%len(basis))
if basis:
    print("   int relation coeffs:", to_int_vector(basis[0]))
