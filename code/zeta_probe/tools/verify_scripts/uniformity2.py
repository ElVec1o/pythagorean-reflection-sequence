import mpmath as mp
mp.mp.dps = 45
def qpoch(a,q,n):
    r=mp.mpf(1)
    for k in range(n): r*=(1-a*q**k)
    return r
def qpoch_inf(a,q):
    r=mp.mpf(1); k=0
    while True:
        t=1-a*q**k; r*=t; k+=1
        if abs(t-1)<mp.mpf(10)**(-44) or k>400000: break
    return r
def J3(nu,x,q,N=300):
    pref=qpoch_inf(q**(nu+1),q)/qpoch_inf(q,q)
    s=mp.fsum((-1)**n*q**(mp.mpf(n*(n-1))/2)*(q*x*x)**n/(qpoch(q**(nu+1),q,n)*qpoch(q,q,n)) for n in range(N))
    return pref*x**nu*s
nu=mp.mpf(3)/2
# find EXTREMA of classical J_{3/2}: zeros of derivative, between consecutive Bessel zeros
extrema=[]
for guess in [2.46,6.0,9.2,12.4,15.6,18.7,21.9,25.0]:
    try:
        z=mp.findroot(lambda z: mp.besselj(nu,z,derivative=1), mp.mpf(guess))
        if z>1: extrema.append(z)
    except: pass
print("At classical-Bessel EXTREMA (phase contamination tan(A-phi)=0 -> isolates AMPLITUDE correction):")
print(f"{'A_extremum':>11} {'(J3/Jcl - 1)/tau':>20}   (tau=0.004)")
tau=mp.mpf('0.004'); q=mp.e**(-tau)
coefs=[]
for A in extrema:
    if A > 1/mp.sqrt(tau)*1.2: continue   # stay within the confluent regime A <~ 1/sqrt(tau)
    x=A*(1-q)/2
    coef=(J3(nu,x,q)/mp.besselj(nu,A)-1)/tau
    coefs.append(coef)
    print(f"{mp.nstr(A,7):>11} {mp.nstr(coef,12):>20}")
print()
if len(coefs)>=3:
    import statistics
    vals=[float(c) for c in coefs]
    print(f"  amplitude-correction coefficients: min={min(vals):.4f} max={max(vals):.4f} spread={max(vals)-min(vals):.4f}")
    print(f"  => {'BOUNDED/FLAT (x-independent O(tau)) => uniform bound HOLDS' if max(vals)-min(vals)<1.5 and max(abs(v) for v in vals)<5 else 'GROWING => problem'}")
