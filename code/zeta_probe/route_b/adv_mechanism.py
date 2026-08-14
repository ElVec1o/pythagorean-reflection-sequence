import mpmath as mp
mp.mp.dps = 40
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def sigmas(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,400):
        Se+=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        So+=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
    return So,Se
poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

# Bessel connection: the c_k recursion has continuum limit J0(w). 
# Claim in problem: b0 ~ sin-structure; pole at sin(w)=0. w=sqrt(2/tau).
# Test: is Se(q) ~ J0(w)-like and at poles cos(w)~0 so sin(w)~+-1?
# The closed forms ARE q-Bessel partial theta sums. Let's check Se ~ cos(w)*sqrt-thing
# and So ~ involves sin(w). Test asymptotic Se ~ A cos(w), So ~ A (cos(w)+ (tau/2)*...)
print("=== Bessel-saddle check: w, cos w, sin w vs Se,So along poles ===")
for m,q in enumerate(poles[:10]):
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    So,Se=sigmas(q)
    # van der Corput / Bessel: J0(w)~sqrt(2/(pi w)) cos(w-pi/4)
    J0=mp.besselj(0,w)
    print(f" m={m} w={float(w):.4f} cos(w)={mp.nstr(mp.cos(w),6):>10} Se={mp.nstr(Se,7):>11} So={mp.nstr(So,7):>11} J0(w)={mp.nstr(J0,6)} Se/J0={mp.nstr(Se/J0,6)}")
