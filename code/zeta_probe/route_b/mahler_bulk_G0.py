"""
Build the EXACT bulk block G_0 = S_0/(1-S_1) as an integer power series in q, high order.
Using the verified definitions from transcendence_verify_ALL.py:
  alpha_k = 2 q^{k+1}/(1-q^{k+1}) = 2 sum_{m>=1} q^{m(k+1)}
  gamma_k = alpha_{k+1} - alpha_k
  S_k = sum_j alpha_{k+2j} prod_{i<j} gamma_{k+2i}
  G_0 = S_0/(1-S_1)
Target check: G_0 coeffs (q^1..) = 2,2,6,2,18,6,42,18,118,50,282,190,706,594,...
"""
from fractions import Fraction as Fr
import json

N = 200   # q-order

def zero(): return [0]*(N+1)

def ps_alpha(k):
    c=zero(); m=1
    while m*(k+1)<=N:
        c[m*(k+1)]+=2; m+=1
    return c

def ps_sub(a,b): return [a[i]-b[i] for i in range(N+1)]

def ps_mul(a,b):
    c=zero()
    for i in range(N+1):
        ai=a[i]
        if ai==0: continue
        for j in range(N+1-i):
            if b[j]: c[i+j]+=ai*b[j]
    return c

def ps_Sk(k):
    tot=zero(); prod=[1]+[0]*N
    j=0
    while True:
        ak=ps_alpha(k+2*j); term=ps_mul(ak,prod)
        tot=[tot[i]+term[i] for i in range(N+1)]
        gk=ps_sub(ps_alpha(k+1+2*j), ps_alpha(k+2*j))
        prod=ps_mul(prod,gk)
        if all(x==0 for x in prod): break
        j+=1
        if j>N+2: break
    return tot

S0=ps_Sk(0); S1=ps_Sk(1)
# G0 = S0 * inv(1-S1)
den=[1-S1[0]]+[-S1[i] for i in range(1,N+1)]
inv=zero(); inv[0]=Fr(1,den[0])
for n in range(1,N+1):
    s=sum(den[k]*inv[n-k] for k in range(1,n+1))
    inv[n]=-s/den[0]
# multiply S0 (ints) by inv (fractions)
G0=[Fr(0)]*(N+1)
for i in range(N+1):
    if S0[i]==0: continue
    for j in range(N+1-i):
        if inv[j]: G0[i+j]+=S0[i]*inv[j]
G0int=[int(x) for x in G0 if x.denominator==1 ] if all(x.denominator==1 for x in G0) else None
print("all integer:", all(x.denominator==1 for x in G0))
G0i=[int(x) for x in G0]
print("G0 q^1..14:", G0i[1:15])
print("target     :", [2,2,6,2,18,6,42,18,118,50,282,190,706,594])
json.dump(G0i, open('/tmp/G0.json','w'))
