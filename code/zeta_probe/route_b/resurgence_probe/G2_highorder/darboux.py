import mpmath as mp, pickle, numpy as np
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=40
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b={n:a[n]/mp.factorial(n) for n in range(1,Nrel+1)}
print(f"Darboux/ratio analysis, reliable b_1..b_{Nrel}")
# Darboux: if nearest sing pair t_s=R e^{i th} (and conj) of type (1-t/t_s)^{-alpha},
# then b_n ~ (2/|t_s|^n) * |C| n^{alpha-1}/|Gamma(alpha)| cos(n th + ph).
# => |b_n|^2 + |b_{n+1}|^2 cross terms... Use the THREE-term real recursion from conj pair:
# b_n = 2 cos(th)/R b_{n-1} - (1/R^2) b_{n-2}  (leading, ignoring n^{alpha-1} drift).
# Better: include the algebraic factor. Fit log|b_n| = -n log R + (alpha-1) log n + osc.
# Extract R from b_n b_{n-2} - b_{n-1}^2 style? Use the determinant method (Hankel) for 2 sings:
# the 3-term recursion coefficients p=2cos(th)/R, q=-1/R^2 from consecutive triples, with the
# n^{alpha-1} making it n-dependent. Track R(n), th(n) per triple and see drift.
print("\nPer-triple (R,th) [pure conj-pair recursion]:")
for n in range(4,Nrel+1):
    # solve b_n = p b_{n-1}+q b_{n-2}, b_{n-1}=p b_{n-2}+q b_{n-3}
    M=mp.matrix([[b[n-1],b[n-2]],[b[n-2],b[n-3]]])
    rhs=mp.matrix([b[n],b[n-1]])
    try:
        sol=mp.lu_solve(M,rhs); p,q=sol[0],sol[1]
        # x^2 - p x - q =0 ; t_s=1/x
        disc=p*p+4*q
        sq=mp.sqrt(disc)
        x=(p+sq)/2
        if x!=0:
            ts=1/x; R=abs(ts); th=mp.arg(ts)*180/mp.pi
            print(f"  n={n}: R={mp.nstr(R,7)}  th={mp.nstr(th,6)}  (q=-1/R^2 => R={mp.nstr(1/mp.sqrt(-q) if q<0 else mp.mpf('nan'),6)})")
    except Exception as e:
        print(f"  n={n}: {e}")
