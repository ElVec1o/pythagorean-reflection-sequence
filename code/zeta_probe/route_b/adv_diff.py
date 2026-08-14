import mpmath as mp
mp.mp.dps = 45
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def sig(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,400):
        Se+=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        So+=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
    return So,Se
poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]
# So-Se via the factor: So = sum even_j f_j, So-Se = sum even_j (f_j-1)
# (f_j-1) = [q^j(1-q)-(1-q^{2j+1})]/(1-q^{2j+1})
print("=== (So-Se)/(Se*tau) along poles -> should -> 1/2 if So/Se=1+tau/2 ===")
for m,q in enumerate(poles[:18]):
    tau=-mp.log(q)
    So,Se=sig(q)
    val=(So-Se)/(Se*tau)
    print(f" m={m:>2} (So-Se)/(Se*tau)={mp.nstr(val,10)}")
