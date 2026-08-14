import mpmath as mp, pickle, numpy as np
mp.mp.dps=45
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
print("Nrel (>=12 dig):",Nrel)
a={n:mp.mpf(an[n]) for n in an}
# Borel coefficients b_n = a_n/n!
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]

# --------- Method 1: Mercer-Roberts / d^2 test for complex conj pair ---------
# If b_n ~ Re(C A^{-n}) with A = R e^{i th}, then b_n satisfy approx b_{n+1}=2cos(th)/R b_n - 1/R^2 b_{n-1}
# Fit (1/R^2, 2cos th /R) from triples => extract R, th.
print("\n--- 3-term linear recurrence fit (conj-pair singularity) ---")
print(" n :   |A|        arg(deg)")
for n in range(4,Nrel):
    # solve b_{n+1}= alpha b_n + beta b_{n-1}  -> char x^2-alpha x-beta=0 roots=1/A,1/Abar
    # use 2 eqns at n,n-1
    M=mp.matrix([[b[n],b[n-1]],[b[n-1],b[n-2]]])
    rhs=mp.matrix([b[n+1],b[n]])
    try:
        sol=mp.lu_solve(M,rhs)
        alpha,beta=sol[0],sol[1]
        # x^2 - alpha x - beta =0
        disc=alpha**2+4*beta
        r1=(alpha+mp.sqrt(disc))/2; r2=(alpha-mp.sqrt(disc))/2
        # smaller-modulus root r = 1/A => A=1/r, take the complex one
        roots=[r1,r2]
        roots=[r for r in roots]
        # pick root giving arg in (30,150)
        best=None
        for r in roots:
            A=1/r
            ar=float(mp.arg(A)*180/mp.pi)
            if 20<abs(ar)<160:
                best=A
        if best is not None:
            print(f" {n:2d}: {float(abs(best)):8.4f}   {float(mp.arg(best)*180/mp.pi):+8.3f}")
        else:
            print(f" {n:2d}: real roots A={float(1/roots[0]):.3f},{float(1/roots[1]):.3f}")
    except Exception as e:
        print(n,"fail",e)
