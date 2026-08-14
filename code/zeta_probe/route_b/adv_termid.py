import mpmath as mp
mp.mp.dps = 40
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
# A_j = even-term = (-2(1-q))^j q^{j(j+1)}/(q;q)_{2j}
# So-Se = sum_j A_j (f_j - 1), f_j=q^j(1-q)/(1-q^{2j+1})
# f_j-1 = [q^j(1-q)-(1-q^{2j+1})]/(1-q^{2j+1})
# colleague claims = g_j = -(1-q^j)(1+q^{j+1})/(1-q^{2j+1})
# check numerator: q^j-q^{j+1}-1+q^{2j+1} =? -(1-q^j)(1+q^{j+1})
# -(1-q^j)(1+q^{j+1}) = -(1 + q^{j+1} - q^j - q^{2j+1}) = -1 -q^{j+1}+q^j+q^{2j+1}
# numerator q^j -q^{j+1} -1 + q^{2j+1}  == -1 +q^j -q^{j+1}+q^{2j+1}  YES identical
print("Algebraic check f_j-1 == g_j:")
for q in [mp.mpf('0.9'),mp.mpf('0.95')]:
    for j in [0,1,2,3]:
        f=q**j*(1-q)/(1-q**(2*j+1))
        g=-(1-q**j)*(1+q**(j+1))/(1-q**(2*j+1))
        print(f"  q={float(q)} j={j} (f_j-1)={mp.nstr(f-1,10)} g_j={mp.nstr(g,10)} eq={abs(f-1-g)<1e-35}")
