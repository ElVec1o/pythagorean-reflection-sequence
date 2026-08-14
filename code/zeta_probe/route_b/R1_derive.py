import mpmath as mp
mp.mp.dps=80
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
# R1: So/Se = [(1-q)/(2q)] S0b/(1-S1b).  -> 1.
# Leading lem:cos: S1b~1-cos w => 1-S1b ~ cos w. S0b~w sin w. (1-q)/(2q)~ (1/w^2)(1+...).
# So So/Se ~ (1/w^2) w sin w / cos w = tan(w)/(w). At poles cos w ->0 so naive -> inf.
# RESOLUTION: at travel poles q_m, the BULK block S1b(q_m) is NOT at its own pole; cos(w_m) is
# small but 1-S1b=Se(q_m) is FINITE nonzero. So So/Se=[(1-q)/(2q)]S0b/Se is finite. The point of
# R1 is that this finite value ->1. Let me decompose: So/Se = [(1-q)/(2q) S0b] / Se = So_exact/Se.
# We already PROVED So=(1-q)/(2q)S0b and Se=1-S1b EXACTLY. So R1 <=> So/Se->1 <=> So-Se->0
# (since Se->0? no, Se=1-S1b at poles is small but not ->0... check).
print("At travel poles: how do Se=1-S1b and So behave? Is So-Se->0 the right statement?")
print(f"{'m':>3} {'tau':>9} {'Se=1-S1b':>13} {'So':>13} {'So-Se':>13} {'(So-Se)/tau':>13} {'So/Se':>11}")
for m in [1,2,4,8,16,32,48,64]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    s0b=Sb(0,q); s1b=Sb(1,q); Se=1-s1b; So=(1-q)/(2*q)*s0b
    print(f"{m:>3} {float(tau):>9.5f} {float(Se):>13.8f} {float(So):>13.8f} {float(So-Se):>13.3e} {float((So-Se)/tau):>13.7f} {float(So/Se):>11.7f}")
print()
print("KEY: So-Se -> 0 like O(tau). Both Se,So ->0 (since S1b->1, S0b/w bounded). So/Se->1 means")
print("So and Se have the SAME leading behavior. Decompose Se,So at poles via lem:cos blocks:")
print("Se=1-S1b. At a travel pole, what is S1b? It's the BULK block at q=q_m^{travel}. Not 1.")
print()
# The real content: Se=1-S1b and So=(1-q)/(2q)S0b BOTH ->0 at poles, ratio->1.
# Using S1b=1-cos w + E1 (E1=lem:cos remainder O(tau)) and S0b = w sin w + E0:
#   Se = cos w - E1
#   So = (1-q)/(2q)(w sin w + E0)
# At travel poles, the pole condition Sigma_1^travel(q_m)=1 fixes w_m. Is cos(w_m) ~ O(sqrt tau)
# (as prompt says) or O(tau)? Check cos(w_m) magnitude at poles:
print("At travel poles: is cos(w_m) ~ sqrt(tau) or ~tau?  And Se vs cos w_m:")
print(f"{'m':>3} {'tau':>9} {'cos w_m':>13} {'cos/sqrt(tau)':>14} {'Se':>12} {'Se/cos w':>11}")
for m in [1,2,4,8,16,32,48,64]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    s1b=Sb(1,q); Se=1-s1b; cw=mp.cos(w)
    print(f"{m:>3} {float(tau):>9.5f} {float(cw):>13.6e} {float(cw/mp.sqrt(tau)):>14.6f} {float(Se):>12.6e} {float(Se/cw):>11.6f}")
