"""Fast exact truncated power-series in tau over Fraction. index = power of tau."""
from fractions import Fraction as Fr
import math

def const(c, P):
    a=[Fr(0)]*(P+1); a[0]=Fr(c); return a

def add(A,B):
    P=len(A)-1; return [A[i]+B[i] for i in range(P+1)]
def sub(A,B):
    P=len(A)-1; return [A[i]-B[i] for i in range(P+1)]
def smul(A,B):
    P=len(A)-1; C=[Fr(0)]*(P+1)
    for i in range(P+1):
        ai=A[i]
        if ai==0: continue
        for j in range(P+1-i):
            bj=B[j]
            if bj: C[i+j]+=ai*bj
    return C
def cmul(c,A):
    c=Fr(c); return [c*x for x in A]
def inv(A):
    P=len(A)-1; assert A[0]!=0
    B=[Fr(0)]*(P+1); B[0]=1/A[0]
    for n in range(1,P+1):
        s=Fr(0)
        for j in range(1,n+1): s+=A[j]*B[n-j]
        B[n]=-s/A[0]
    return B
def qpow(a, P):
    """q^a = e^{-a tau}, a rational. coeff[n]=(-a)^n/n!."""
    a=Fr(a); out=[Fr(0)]*(P+1); t=Fr(1)
    for n in range(P+1):
        out[n]=t
        t=t*(-a)/(n+1)
    return out
# verify e^{-a tau}: coeff n = (-a)^n/n!
def qpow_check(a,P):
    return [Fr((-a)**n, math.factorial(n)) for n in range(P+1)]
