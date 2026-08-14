import mpmath as mp, pickle
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=40
Nrel=max(n for n in an if agree[n]>=10)
a={n:mp.mpf(an[n]) for n in an}
b={n:a[n]/mp.factorial(n) for n in range(1,Nrel+1)}
A=4*mp.sqrt(2)*mp.e**(1j*mp.atan(2))  # candidate
# if b_n ~ Re[ C A^{-n} n^{alpha-1} ], then |b_n| |A|^n ~ |C| n^{alpha-1} |cos(n arg A + ph)|.
# the ENVELOPE |b_n| |A|^n / n^{alpha-1} const. Extract alpha from growth of |b_n| |A|^n.
print("n   |b_n|*|A|^n   ratio_to_prev   (=> if ~ (n/(n-1))^{alpha-1})")
RA=abs(A)
prev=None
for n in range(2,Nrel+1):
    val=abs(b[n])*RA**n
    r=val/prev if prev else float('nan')
    # alpha-1 = log(r)/log(n/(n-1))
    aest = mp.log(r)/mp.log(mp.mpf(n)/(n-1)) if prev else float('nan')
    print(f"{n:2d}  {mp.nstr(val,6):>12}  {mp.nstr(r,5):>8}  alpha-1~{mp.nstr(aest,4)}")
    prev=val
print("\nNOTE: |b_n||A|^n oscillates (cos factor) so envelope needs peaks. Pole=>alpha integer;")
print("branch cut => alpha non-integer (e.g. 1/2, 3/2). The doubly-exp/sqrt structure suggests")
print("a logarithmic or sqrt branch (alpha=1/2 type), consistent with w=sqrt(2/tau) map.")
