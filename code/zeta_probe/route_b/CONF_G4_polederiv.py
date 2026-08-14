"""
Self-contained pole-phase derivation (attack (a)): is sqrt2/36 = Theta_sub + Airy-offset (both turning-point)?
1-Sig_1^T = P11+P21 ~ cos(w + phi_corr), phi_corr=(sqrt2/36)sqrt(tau) (the sharp pole phase).
Claim: phi_corr = Theta_sub + AiryOffset, where
   Theta(n*) = w - (3/4)pi + Theta_sub  (smooth phase integral subleading, EM/dilog),
   AiryOffset = the uniform-Airy connection phase subleading.
Step 1: compute Theta(n*) (exact sum) to high precision, extract Theta_sub coefficient, identify it.
Step 2: implied AiryOffset = phi_corr - Theta_sub; check it's a sensible Airy constant x sqrt(tau).
"""
import mpmath as mp
mp.mp.dps=45
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(300/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=20):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def Theta_nstar(q,tau):
    def bn(n): return (1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
    S=mp.mpf(0); n=1
    while True:
        b=bn(n)
        if b>=2: break
        S+=mp.acos(b/2); n+=1
    return S, n

print("Step 1: Theta(n*) - w + (3/4)pi  =>  Theta_sub ; extract /sqrt(tau) coefficient.")
print(f"{'m':>3}{'tau':>10}{'Theta(n*)-w+3pi/4':>20}{'/sqrt(tau)':>14}")
taus=[];subs=[]
for m in [8,12,16,22,30,40,55,75]:
    if m>len(poles): continue
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    Th,nst=Theta_nstar(q,tau)
    sub=Th-w+mp.mpf(3)/4*mp.pi
    taus.append(tau);subs.append(sub/mp.sqrt(tau))
    print(f"{m:>3}{float(tau):>10.6f}{float(sub):>20.8f}{float(sub/mp.sqrt(tau)):>14.7f}")
# extrapolate Theta_sub/sqrt(tau) to tau->0
n=len(taus); A=mp.matrix(n,n); b=mp.matrix(n,1)
for i in range(n):
    p=mp.mpf(1)
    for j in range(n): A[i,j]=mp.sqrt(taus[i])**j
    b[i]=subs[i]
c=mp.lu_solve(A,b); c1=c[0]
print(f"\nTheta_sub/sqrt(tau) -> {mp.nstr(c1,10)}")
print(f"  candidates: -sqrt2 * something? identify={mp.identify(c1,['sqrt(2)','pi'])}")
for cand,nm in [(-mp.sqrt(2)*5/12,'-5sqrt2/12'),(-mp.mpf(13)/16,'-13/16'),(-mp.sqrt(2)*mp.mpf('0.408'),'-0.408sqrt2'),
                (-(1-mp.sqrt(2)/36)*mp.sqrt(2)/2,'?')]:
    print(f"    {nm} = {mp.nstr(cand,8)}  diff={mp.nstr(c1-cand,3)}")
sqrt2_36=mp.sqrt(2)/36
print(f"\nphi_corr coeff (sharp pole phase) = sqrt2/36 = {mp.nstr(sqrt2_36,8)}")
print(f"implied AiryOffset/sqrt(tau) = sqrt2/36 - Theta_sub_coeff = {mp.nstr(sqrt2_36 - c1,8)}")
print(f"  (this should be the uniform-Airy connection phase subleading; identify={mp.identify(sqrt2_36-c1,['sqrt(2)','pi'])})")
