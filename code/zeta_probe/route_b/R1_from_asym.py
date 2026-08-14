import mpmath as mp
mp.mp.dps=60
# Use the SHARP proven asymptotics (uniform in phase, from lemcos_uniform_phase.py):
#   S1_bulk(q) = (1-cos w) + c1b*sqrt(tau)*sin w + o(sqrt tau), c1b = -17 sqrt2/36
#   S0_bulk(q) = w sin w + (lower order)   [companion; let's get its sharp subleading]
# Dictionary: Se = 1 - S1_bulk = cos w - c1b sqrt(tau) sin w + o(sqrt tau)
#             So = (p/2q) S0_bulk = (p/2q) w sin w + ...
# So/Se -> 1 requires (p/2q) w sin w / [cos w - c1b sqrt(tau) sin w] -> 1.  Test the model.
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>80: break
    return tot

# Off-pole, smooth q: check the dictionary identities hold AND check So/Se via bulk asym model.
print("OFF-POLE smooth check of dictionary + asymptotic decomposition of So/Se:")
print(f"{'tau':>10} {'w':>10} {'So/Se(dict)':>14} {'(p/2q)wsinw/cosw':>18} {'(p/2q)w':>12}")
for tauf in ['0.05','0.02','0.01','0.005','0.002','0.001']:
    tau=mp.mpf(tauf); q=mp.e**(-tau); p=1-q; w=mp.sqrt(2/tau)
    b1=Sb(1,q); b0=Sb(0,q)
    Se=1-b1; So=(p/(2*q))*b0
    model=(p/(2*q))*w*mp.sin(w)/mp.cos(w)
    print(f"{tauf:>10} {float(w):>10.4f} {mp.nstr(So/Se,9):>14} {mp.nstr(model,9):>18} {mp.nstr((p/(2*q))*w,7):>12}")

# KEY ALGEBRAIC POINT: (p/2q)*w. With tau=-ln q, p=1-q. As tau->0: p=1-e^{-tau}=tau-tau^2/2+...,
#   q=e^{-tau}, 2q->2. w=sqrt(2/tau). So (p/2q)w = (tau-tau^2/2+..)/(2 e^{-tau}) * sqrt(2/tau)
#   = (1/2)(tau)(1+tau/2..)*e^{tau} * sqrt(2/tau) = (1/2) sqrt(2 tau)(1+..) = sqrt(tau/2)(1+..).
# So (p/2q) w ~ sqrt(tau/2) -> 0. Then model = sqrt(tau/2) w tan w... wait w sin w not w sin w/cos:
# So ~ (p/2q) w sin w ~ sqrt(tau/2) sin w. Se ~ cos w. So So/Se ~ sqrt(tau/2) sin w / cos w -> 0 generically!
# But at travel poles So/Se->1. CONTRADICTION with generic. RESOLUTION: at travel poles the bulk
# blocks are NOT in the q->1 asymptotic regime in the naive way; rather Se,So are O(tau)-small there
# and their RATIO is fixed by the travel-pole condition. Let me verify Se,So SIZE at poles:
print()
print("(p/2q)*w ~ sqrt(tau/2): verify, and note So,Se -> 0 at poles (both ~ sqrt(tau)?):")
print(f"{'tau':>10} {'(p/2q)w':>12} {'sqrt(tau/2)':>12}")
for tauf in ['0.05','0.01','0.002']:
    tau=mp.mpf(tauf); q=mp.e**(-tau); p=1-q; w=mp.sqrt(2/tau)
    print(f"{tauf:>10} {mp.nstr((p/(2*q))*w,8):>12} {mp.nstr(mp.sqrt(tau/2),8):>12}")
