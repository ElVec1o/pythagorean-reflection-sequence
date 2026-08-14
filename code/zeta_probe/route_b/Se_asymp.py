import mpmath as mp
mp.mp.dps=60
import sys

def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-160) and j>60: break
    return tot
def A_(k,q): return 2*q/(1-q**(k+1))
def C_(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_(k+2*j,q)*prod; prod*=C_(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-160) and j>60: break
    return tot

# Goal: find the subleading coeff of S1blk: S1blk = (1-cos w) + c*sqrt(tau)*sin w + O(tau).
# i.e. (S1blk-(1-cos w))/(sqrt(tau) sin w) -> c.  Off-pole, high precision.
print("Bulk S1blk subleading:  E1b=(S1blk-(1-cos w)); E1b/(sqrt(tau) sin w) -> c1_bulk ?")
print(f"{'tau':>10} {'w':>9} {'E1b/(sqrt(tau)sinw)':>22} {'sqrt2/36':>12} {'17sqrt2/36':>12} {'5sqrt2/36':>12}")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.004'),mp.mpf('0.002'),mp.mpf('0.001'),mp.mpf('0.0005')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    sb1=Sb(1,q)
    E=sb1-(1-mp.cos(w))
    r=E/(mp.sqrt(tau)*mp.sin(w))
    print(f"{mp.nstr(tau,4):>10} {mp.nstr(w,7):>9} {mp.nstr(r,12):>22} {mp.nstr(mp.sqrt(2)/36,8):>12} {mp.nstr(17*mp.sqrt(2)/36,8):>12} {mp.nstr(5*mp.sqrt(2)/36,8):>12}")

print()
# Now AT poles: Sigma_1=1, and w_m=(m+3/2)pi approx so cos w_m=O(sqrt tau), sin w_m=+-1.
# Pin cos(w_m): the travel pole condition Sigma_1=1 fixes cos w_m. Sigma_1=(1-cos w)+c_T sqrt(tau) sin w+...=1
# => cos w_m = c_T sqrt(tau) sin w_m + O(tau).   (so cos w_m ~ c_T sqrt(tau) sin w_m)
print("At travel poles: pin cos(w_m). Sigma_1=1 => 1-cos w_m + (Sig1-(1-cosw)) =1 => cos w_m = E_T(travel).")
print("Check cos(w_m)/(sqrt(tau) sin w_m) -> c_T (travel subleading coeff):")
poles=[mp.mpf(l.strip()) for l in open('poles.txt')]
print(f"{'m':>3} {'w':>9} {'cos w_m':>14} {'cosw/(sqrt(tau)sinw)':>22}")
for i in [2,4,8,16,24,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    cw=mp.cos(w); sw=mp.sin(w)
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(cw,9):>14} {mp.nstr(cw/(mp.sqrt(tau)*sw),10):>22}")

print()
# THE KEY RATIO at poles. Se=1-S1blk, So=(p/2q)S0blk.
# Se = 1-S1blk = cos w - c1b sqrt(tau) sin w + O(tau).  At pole cos w_m = c_T sqrt(tau) sin w_m+O(tau).
# => Se(q_m) = (c_T - c1b) sqrt(tau) sin w_m + O(tau).
# So = (p/2q)S0blk ~ (tau/2)*w sin w = sqrt(tau/2) sin w + O(tau^{?}).  sqrt(tau/2)=sqrt(tau)/sqrt2.
# So/Se -> [1/sqrt2] / (c_T - c1b).  For ->1 need c_T - c1b = 1/sqrt2.
print("Decompose Se(q_m)/(sqrt(tau) sin w) -> (c_T - c1b) ; So(q_m)/(sqrt(tau) sin w) -> 1/sqrt2 ?")
print(f"{'m':>3} {'Se/(sqrt(tau)sinw)':>20} {'So/(sqrt(tau)sinw)':>20} {'1/sqrt2':>10} {'So/Se':>11}")
for i in [2,4,8,16,24,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    sb1=Sb(1,q); sb0=Sb(0,q)
    Se=1-sb1; So=(p/(2*q))*sb0; sw=mp.sin(w)
    rSe=Se/(mp.sqrt(tau)*sw); rSo=So/(mp.sqrt(tau)*sw)
    print(f"{i:>3} {mp.nstr(rSe,9):>20} {mp.nstr(rSo,9):>20} {mp.nstr(1/mp.sqrt(2),7):>10} {mp.nstr(So/Se,9):>11}")
    sys.stdout.flush(); mp.mp.dps=60
