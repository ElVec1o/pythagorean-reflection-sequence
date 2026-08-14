import mpmath as mp
mp.mp.dps=70
import sys
# Question: bulk S1blk subleading c_B = sqrt2/36 - 1/sqrt2 ?  travel Sig1 sublead c_T = sqrt2/36 ?
# The saddle/lem:cos result says the ERROR Sig1-(1-cos w) ~ (sqrt2/36) sqrt(tau) sin w (travel).
# Test BOTH off-pole with a PHASE-AVERAGING-FREE method: sample at w = (k+1/2)pi (sin=+-1, cos=0)
# so that the (1-cos w) leading is EXACTLY 1 and the subleading dominates cleanly.
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=60000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-200) and j>60: break
    return tot
def A_(k,q): return 2*q/(1-q**(k+1))
def C_(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=60000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_(k+2*j,q)*prod; prod*=C_(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-200) and j>60: break
    return tot

# choose w exactly = (k+1/2)*pi => cos w=0, sin w=(-1)^k. tau=2/w^2, q=e^{-tau}.
print("Sample at w=(k+1/2)pi (cos w=0 exactly, sin w=+-1): isolate subleading sqrt(tau) coeff.")
print(f"{'k':>4} {'w':>9} {'(1-Sig1)/(rt*sinw)=cT':>24} {'(Sb1-1)/(rt*sinw)? ':>22}")
print("   [Sig1=1-cosw+cT rt sinw => at cosw=0: Sig1-1 = cT rt sinw => cT=(Sig1-1)/(rt sinw)]")
print("   [Sb1=1-cosw+cB rt sinw => at cosw=0: Sb1-1 = cB rt sinw => cB=(Sb1-1)/(rt sinw)]")
print(f"{'k':>4} {'w':>9} {'cT':>16} {'sqrt2/36':>12} {'cB':>16} {'sqrt2/36-1/sqrt2':>17}")
for k in [40,80,160,320,640]:
    w=(mp.mpf(k)+mp.mpf(1)/2)*mp.pi
    tau=2/w**2; q=mp.e**(-tau); rt=mp.sqrt(tau); sw=mp.sin(w)
    mp.mp.dps=70+int(0.9*float(w)/10)
    s1=Sig(1,q); sb1=Sb(1,q)
    cT=(s1-1)/(rt*sw); cB=(sb1-1)/(rt*sw)
    print(f"{k:>4} {float(w):>9.2f} {mp.nstr(cT,10):>16} {mp.nstr(mp.sqrt(2)/36,8):>12} {mp.nstr(cB,10):>16} {mp.nstr(mp.sqrt(2)/36-1/mp.sqrt(2),10):>17}")
    sys.stdout.flush(); mp.mp.dps=70

print()
print("targets: sqrt2/36 =", mp.nstr(mp.sqrt(2)/36,12), " sqrt2/36-1/sqrt2 =", mp.nstr(mp.sqrt(2)/36-1/mp.sqrt(2),12))
print("cB-cT should be -1/sqrt2 =", mp.nstr(-1/mp.sqrt(2),12))
