"""
OPTION 1 attempt: does D = P12*S0b = 1 - P11*Se (the U-quantity, ~tau/4) have a clean q-series with
B-function / Lindelof structure? If so, lem:T2abs-type absolute bound may transfer and close U.
Compute the cocycle product as a TRUNCATED POWER SERIES in q, extract P11,P12,P22=Se, S0b=Sbulk(0),
form D = 1 - P11*Se and t1 = P12/Se, print coefficients, and test structure:
  - integer coeffs? j^2-gaps (like lem:cos blocks)? matches a Lambert/theta candidate?
Pure Python rational/integer series, exact (Fraction), truncated at order K.
"""
from fractions import Fraction as F
K = 70

def mul(a, b):
    c = [F(0)]*(K+1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        if i > K: break
        for j, bj in enumerate(b):
            if i+j > K: break
            if bj: c[i+j] += ai*bj
    return c

def add(a,b): return [a[i]+b[i] for i in range(K+1)]
def scal(a,s): return [s*x for x in a]
def qpow(n):  # q^n as a series
    e=[F(0)]*(K+1)
    if n<=K: e[n]=F(1)
    return e
def one():
    e=[F(0)]*(K+1); e[0]=F(1); return e

# cocycle M_n = [[1+2q^2n, -2q^n],[2q^3n, 1-2q^2n]], product over n=1..N (N>K so q^N=0 mod K)
P11=one(); P12=[F(0)]*(K+1); P21=[F(0)]*(K+1); P22=one()   # start = Identity
for n in range(1, K+1):
    if n> K: break
    m11=add(one(), scal(qpow(2*n),F(2)))
    m12=scal(qpow(n),F(-2))
    m21=scal(qpow(3*n),F(2))
    m22=add(one(), scal(qpow(2*n),F(-2)))
    # P_new = P * M_n   (right-multiply, matching cocycle order M_1 M_2 ... )
    n11=add(mul(P11,m11), mul(P12,m21)); n12=add(mul(P11,m12), mul(P12,m22))
    n21=add(mul(P21,m11), mul(P22,m21)); n22=add(mul(P21,m12), mul(P22,m22))
    P11,P12,P21,P22=n11,n12,n21,n22

Se=P22
# S0b = Sbulk(0,q) = sum_j alpha(2j) prod gamma, alpha(k)=2q^{k+1}/(1-q^{k+1}), gamma(k)=2q^{k+2}/(1-q^{k+2})-2q^{k+1}/(1-q^{k+1})
def geom(a):  # 1/(1-q^a) as series
    e=[F(0)]*(K+1); j=0
    while j*a<=K: e[j*a]=F(1); j+=1
    return e
def alpha(k): return scal(mul(qpow(k+1),geom(k+1)),F(2))
def gamma(k): return add(scal(mul(qpow(k+2),geom(k+2)),F(2)), scal(mul(qpow(k+1),geom(k+1)),F(-2)))
S0b=[F(0)]*(K+1); prod=one(); j=0
while 2*j<=K+2:
    S0b=add(S0b, mul(alpha(2*j),prod)); prod=mul(prod,gamma(2*j)); j+=1

D=add(one(), scal(mul(P11,Se),F(-1)))       # D = 1 - P11*Se
D2=mul(P12,S0b)                              # should equal D (unimodular)
# t1 = P12/Se  (series division)
def divser(a,b):
    assert b[0]!=0
    c=[F(0)]*(K+1);
    for i in range(K+1):
        s=a[i]-sum(c[k]*b[i-k] for k in range(i))
        c[i]=s/b[0]
    return c
t1=divser(P12,Se)

def show(name,s,m=28):
    num=[ (i,s[i]) for i in range(m+1) if s[i]!=0]
    print(f"{name}: "+", ".join(f"{c}q^{i}" if c!=1 else f"q^{i}" for i,c in num))
print("=== q-series (first coeffs) ===")
show("P12",P12); show("Se ",Se); show("S0b",S0b)
show("D=1-P11*Se",D); show("P12*S0b   ",D2)
print("  D == P12*S0b (unimodular check):", all(D[i]==D2[i] for i in range(K+1)))
show("t1=P12/Se ",t1)
print()
print("=== structure tests on D ===")
allint=all(x.denominator==1 for x in D)
print("D integer coeffs?", allint)
# coefficient growth (for Polya-Carlson / natural boundary): |c_n| pattern
cs=[int(D[i]) if D[i].denominator==1 else float(D[i]) for i in range(K+1)]
print("D coeffs 0..40:", cs[:41])
print()
print("=== structure tests on t1 ===")
print("t1 integer?", all(x.denominator==1 for x in t1))
print("t1 coeffs*? first 20:", [str(t1[i]) for i in range(20)])
