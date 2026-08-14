import mpmath as mp
mp.mp.dps=40
# CLAIM: the sharp pole phase sqrt2/36 = (1/24) sum_n k_n^3 (EM correction to the 2nd difference),
# k_n=arccos(b_n/2), b_n=(1+q^3-2(1-q)q^{2n+2})/q^{3/2}.  Verify (1/24) sum k_n^3 / sqrt(tau) -> sqrt2/36.
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
s2_36=mp.sqrt(2)/36
print(f"target sqrt2/36 = {mp.nstr(s2_36,10)}")
print(f"{'m':>3}{'tau':>10}{'(1/24)sum k^3':>16}{'/sqrt(tau)':>14}{'ratio to s2/36':>16}")
for m in [8,12,16,22,30,42,60]:
    if m>len(poles): continue
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    S3=mp.mpf(0); n=1
    while True:
        b=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
        if b>=2: break
        S3+=mp.acos(b/2)**3; n+=1
    val=S3/24
    print(f"{m:>3}{float(tau):>10.6f}{mp.nstr(val,8):>16}{mp.nstr(val/mp.sqrt(tau),9):>14}{mp.nstr(val/mp.sqrt(tau)/s2_36,9):>16}")
print("\nIf (1/24 sum k^3)/sqrt(tau) -> sqrt2/36 (ratio->1): sqrt2/36 is DERIVED elementarily (EM correction)")
print("=> sharp pole phase = elementary EM/discretization correction => sharp lem:cos PROVED, U closes self-contained.")
