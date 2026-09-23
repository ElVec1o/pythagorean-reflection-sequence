# Step 2: rigorous exclusion "no integer polynomial P != 0 with deg P <= d, height <= H has P(x*)=0",
# x* = q* or beta2, from the certified bracket [lo,hi] of step 1.
# Certificate: for the LLL-reduced basis, lambda_1(L) >= min_k ||b_k^*|| (exact rational Gram-Schmidt
# via leading principal minors of the Gram matrix). Any P with P(x*)=0, H(P)<=H gives a lattice vector
# of norm <= H*K_d; if min_k ||b_k^*|| > H*K_d no such P exists.
import sys, time, math
from fractions import Fraction as Fr
import flint
t0=time.time()
target=sys.argv[1]; d=int(sys.argv[2])
a_num,b_num,Dd,blo,bhi,E=[int(x) for x in open("bracket.txt").read().split()]
if target=="q":
    num,den=a_num,10**Dd; w=Fr(b_num-a_num,10**Dd); R=Fr(1)          # [lo,hi] subset (0,1)
elif target=="ctl":   # negative control: x*=sqrt(2)-1, root of x^2+2x-1 (deg 2, height 2); also x*^2 etc.
    from math import isqrt
    den=10**Dd; num=isqrt(2*den*den)-den; w=Fr(4,den); R=Fr(1)
else:
    num,den=blo,10**E; w=Fr(bhi-blo,10**E); R=Fr(3,2)                 # [lo,hi] subset (1,3/2)
M=int(1/w)                                   # M*w <= 1
s_d=sum(i*R**(i-1) for i in range(1,d+1))    # max |P'|/H on [lo,hi]
Kd2=(d+1)+(s_d+d+1)**2                       # (norm bound / H)^2 ; exact rational
rows=[]
for i in range(d+1):
    v=(M*num**i)//(den**i)                   # floor(M c^i), 0 <= M c^i - v < 1
    r=[0]*(d+2); r[i]=1; r[d+1]=v; rows.append(r)
B=flint.fmpz_mat(rows)
L,T=B.lll(transform=True,delta=0.99)
assert T*B==L and abs(int(T.det()))==1, 'LLL output not a basis of the same lattice'
t1=time.time()
G=L*L.transpose()
n=d+1
dets=[flint.fmpz(1)]
for k in range(1,n+1):
    sub=flint.fmpz_mat([[G[i,j] for j in range(k)] for i in range(k)])
    dets.append(sub.det())
gs2=[Fr(int(dets[k]),int(dets[k-1])) for k in range(1,n+1)]
m2=min(gs2)                                   # min ||b_k^*||^2, exact
# certified H: largest H with H^2*Kd2 < m2  ->  log10
Hc2=m2/Kd2
log10H=0.5*(math.log10(Hc2.numerator)-math.log10(Hc2.denominator))
shortest=min(sum(int(L[k,j])**2 for j in range(d+2)) for k in range(n))
print(f"[unimodular T verified] {target} d={d}: certified log10 H_max = {log10H:.2f} "
      f"(min GS norm 10^{0.5*(math.log10(m2.numerator)-math.log10(m2.denominator)):.2f}, "
      f"shortest found 10^{0.5*math.log10(shortest):.2f}, Gaussian-heur 10^{(math.log10(M))/(d+1):.2f}) "
      f"LLL {t1-t0:.1f}s total {time.time()-t0:.1f}s", flush=True)
