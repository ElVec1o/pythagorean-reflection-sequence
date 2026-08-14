import mpmath as mp
mp.mp.dps=60
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("PART 11.  Decompose cos W at the travel pole. W = w e^{-tau/2} = w(1-tau/2+tau^2/8-...).")
print("  w - W = w(1-e^{-tau/2}) = w*tau/2 - w*tau^2/8 + ...  w*tau/2 = sqrt(2/tau)*tau/2 = sqrt(tau/2).")
print("  => W = w - sqrt(tau/2) + O(tau^{3/2}).  cos W = cos(w - sqrt(tau/2)+...) ")
print("       = cos w cos(sqrt(tau/2)) + sin w sin(sqrt(tau/2)) + (higher).")
print("       ~ cos w * 1 + sin w * sqrt(tau/2) + O(tau)   [since sqrt(tau/2) small].")
print("  So cos W ~ cos w + sin w sqrt(tau/2).  AT the pole cos w ~ (sqrt2/36)sqrt(tau)*sin w (lem:cos saddle).")
print("  => cos W ~ sin w [ (sqrt2/36)sqrt(tau) + sqrt(tau/2) ].  Dominant = sqrt(tau/2) sin w (ELEMENTARY shift!).")
print("="*120)
print(f"{'m':>3} {'w':>9} {'w-W':>13} {'sqrt(tau/2)':>13} {'cos W':>13} {'cosw+sinw*sqrt(t/2)':>20} {'match':>9}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(0.8*float(w))
    W=w*mp.e**(-tau/2)
    cw=mp.cos(w); sw=mp.sin(w)
    approx=cw+sw*mp.sqrt(tau/2)
    print(f"{i:>3} {float(w):>9.3f} {float(w-W):>13.8f} {float(mp.sqrt(tau/2)):>13.8f} {float(mp.cos(W)):>13.8f} {float(approx):>20.8f} {float(abs(mp.cos(W)-approx)):>9.1e}")
    mp.mp.dps=60

print()
print("  Confirm cos W/sqrt(tau) -> sin w/sqrt2 + (sqrt2/36)*sin w*... NO: dominant is sin w/sqrt2 (the shift),")
print("  PLUS the cos w piece which is itself (sqrt2/36)sqrt(tau)sin w. Net cos W/sqrt(tau):")
print(f"{'m':>3} {'cos W/sqrt(tau)':>16} {'sin w/sqrt2 + sin w*sqrt2/36':>28} {'(shift+saddle)':>15}")
for i in [4,8,16,32,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(0.8*float(w))
    W=w*mp.e**(-tau/2); cw=mp.cos(w); sw=mp.sin(w)
    pred=sw/mp.sqrt(2)+sw*mp.sqrt(2)/36   # sin w (1/sqrt2 + sqrt2/36)
    print(f"{i:>3} {float(mp.cos(W)/mp.sqrt(tau)):>16.8f} {float(pred):>28.8f}")
    mp.mp.dps=60

print()
print("="*120)
print("PART 12.  PUT IT TOGETHER (the clean derivation of R1):")
print("  Se = cos W - T2.")
print("    cos W ~ sin w [ sqrt(tau/2) + (sqrt2/36)sqrt(tau) ]   (elementary shift + lem:cos saddle on cos w)")
print("    T2    ~ sin w (sqrt2/36) sqrt(tau)                    (lem:cos saddle, lem:Bbounded)")
print("  Se = cos W - T2 ~ sin w sqrt(tau/2) + sin w(sqrt2/36)sqrt(tau) - sin w(sqrt2/36)sqrt(tau)")
print("     = sin w sqrt(tau/2).   [the two saddle pieces CANCEL; elementary shift survives]")
print("  This is the SAME cancellation structure as lem:Bbounded. CHECK the cancellation directly:")
print(f"{'m':>3} {'Se/sqrt(tau)':>14} {'shift sin w/sqrt2':>18} {'cosW saddle':>13} {'-T2 saddle':>13} {'net saddle':>12}")
for i in [2,4,8,16,32,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.6*float(w))
    W=w*mp.e**(-tau/2); cw=mp.cos(w); sw=mp.sin(w)
    Sbulk_J=20000
    def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
    def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(Sbulk_J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>60: break
    S1b=tot
    Se=1-S1b; T1=cw-mp.cos(W); T2=S1b-(1-cw)-T1
    cosW_saddle=mp.cos(W)/mp.sqrt(tau)-sw/mp.sqrt(2)   # cos W minus the shift part
    print(f"{i:>3} {float(Se/mp.sqrt(tau)):>14.8f} {float(sw/mp.sqrt(2)):>18.8f} {float(cosW_saddle):>13.8f} {float(-T2/mp.sqrt(tau)):>13.8f} {float(cosW_saddle-T2/mp.sqrt(tau)):>12.2e}")
    mp.mp.dps=60
