import mpmath as mp
mp.mp.dps = 30
# Morita's infinity-solutions carry 1phi1(0, p^{1±2nu}; p, x).  Check its confluent (p->1) correction
# is O(eps)=O(tau) RELATIVE (regular, no sqrt), at the confluent scaling x ~ 1/((1-p)^2 X).
# 1phi1(0;c;p;z) = sum_n (-1)^n p^{n(n-1)/2} z^n / ((c;p)_n (p;p)_n)
def ppoch(a,p,n):
    r=mp.mpf(1)
    for k in range(n): r*=(1-a*p**k)
    return r
def phi11(c,p,z,N=400):
    return mp.fsum( (-1)**n * p**(mp.mpf(n*(n-1))/2) * z**n / (ppoch(c,p,n)*ppoch(p,p,n)) for n in range(N))
nu=mp.mpf(3)/2; X=mp.mpf('0.5')
print("1phi1(0;p^{1+2nu};p; 1/((1-p)^2 X)) confluent order in eps (X=0.5, nu=3/2):")
vals=[]
for eps in [mp.mpf('0.1'),mp.mpf('0.05'),mp.mpf('0.025'),mp.mpf('0.0125')]:
    p=mp.e**(-eps); c=p**(1+2*nu); z=1/((1-p)**2 * X)
    F=phi11(c,p,z)
    vals.append((eps,F))
    print(f"  eps={float(eps):.4f}: 1phi1 = {mp.nstr(F,12)}")
# fit F(eps) = L (1 + a eps + ...): check first differences scale ~eps (linear => O(tau) correction)
print("  successive (F(eps)-F(eps/2)) ratios (->2 if O(eps) linear convergence):")
for i in range(len(vals)-2):
    d1=vals[i][1]-vals[i+1][1]; d2=vals[i+1][1]-vals[i+2][1]
    print(f"    ratio = {mp.nstr(d1/d2,6)}   (2.0 = clean O(eps) i.e. O(tau), no sqrt)")
