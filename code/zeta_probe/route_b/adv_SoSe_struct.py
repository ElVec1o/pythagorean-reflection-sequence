import mpmath as mp
mp.mp.dps = 45
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def sigmas(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0);termsE=[];termsO=[]
    for j in range(0,400):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to;termsE.append(te);termsO.append(to)
    return So,Se,termsE,termsO
poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

# Compare term-by-term: ratio of jth odd term to jth even term:
# odd_j/even_j = q^{j(j+2)-j(j+1)}(1-q)*(q;q)_{2j}/(q;q)_{2j+1} = q^j (1-q)/(1-q^{2j+1})
# So So = sum_j even_j * [q^j(1-q)/(1-q^{2j+1})].
# Thus So/Se is a weighted avg of factor f_j = q^j(1-q)/(1-q^{2j+1}) with weights even_j.
# As q->1: f_j = (1-q)/(1-q^{2j+1}) * q^j -> (1/(2j+1)) as q->1 for fixed j? check.
print("=== odd_j/even_j factor f_j = q^j(1-q)/(1-q^{2j+1}) ===")
for m,q in enumerate(poles[:4]):
    onem=1-q
    fs=[float(q**j*onem/(1-q**(2*j+1))) for j in range(6)]
    print(f" m={m} q={float(q):.5f} f_0..5 = "+", ".join(f"{x:.5f}" for x in fs))
# At q->1, f_j -> 1/(2j+1). So So/Se = sum even_j/(2j+1) / sum even_j, weighted by even_j.
# The saddle j* ~ w/2 ~ sqrt(1/(2tau)) -> infinity. So dominant j large => f_j ~ 1/(2j+1) -> 0??
# But data says So/Se->1. Resolve: weights even_j alternate; near-cancellation; dominant
# contribution where? Let's see which j dominates |even_j| at a pole.
print("=== which j dominates even-term magnitude at a pole (m=6) ===")
q=poles[6];onem=1-q;tau=-mp.log(q);w=mp.sqrt(2/tau)
So,Se,tE,tO=sigmas(q)
mags=[abs(t) for t in tE]
jmax=max(range(len(mags)),key=lambda j:mags[j])
print(f" w/2={float(w/2):.3f}, argmax_j |even_j| = {jmax}, |even_{jmax}|={float(mags[jmax]):.5f}")
print(f" f_{{w/2}} ~ 1/(w+1) = {float(1/(w+1)):.5f}  but So/Se={mp.nstr(So/Se,8)}")
