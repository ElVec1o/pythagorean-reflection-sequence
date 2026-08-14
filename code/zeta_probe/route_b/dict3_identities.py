import mpmath as mp
mp.mp.dps = 120   # high dps to beat Se/So cancellation at poles
exec(open('dict_U_vs_lemcos.py').read().split('poles=')[0])
poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

print("="*120)
print("TEST EXACT IDENTITIES (claimed):  (E1) Se = 1 - S1b   (E2) So*Sig0 = 1   -- at poles AND generic q")
print("="*120)
print("\n[generic q, NOT poles]")
print(f"{'q':>6} | {'Se':>16} {'1-S1b':>16} {'|Se-(1-S1b)|':>13} | {'So*Sig0':>18} {'|So*Sig0-1|':>13}")
for qv in ['0.5','0.7','0.8','0.85','0.9','0.93','0.95']:
    q=mp.mpf(qv); N=int(120/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    S1b=Sbulk(1,q); Sig0=Sigma(0,q); Sig1=Sigma(1,q)
    print(f"{qv:>6} | {mp.nstr(Se,12):>16} {mp.nstr(1-S1b,12):>16} {mp.nstr(abs(Se-(1-S1b)),3):>13} | {mp.nstr(So*Sig0,14):>18} {mp.nstr(abs(So*Sig0-1),3):>13}")

print("\n[travel poles, dps=120]")
print(f"{'m':>2} {'tau':>10} | {'|Se-(1-S1b)|':>13} | {'|So*Sig0-1|':>13} | {'So/Se':>12} {'(So/Se-1)/tau':>14}")
for m in [1,2,4,8,16,24,32,40,48,56,64,72,80]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); N=int(120/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    S1b=Sbulk(1,q); Sig0=Sigma(0,q)
    print(f"{m:>2} {float(tau):>10.6f} | {mp.nstr(abs(Se-(1-S1b)),3):>13} | {mp.nstr(abs(So*Sig0-1),3):>13} | {mp.nstr(So/Se,10):>12} {float((So/Se-1)/tau):>14.8f}")

print("\n" + "="*120)
print("If (E1)+(E2) EXACT then  So/Se = (1-S1b)^{-1} * Sig0^{-1} ... no: So/Se = So*Se^{-1}.")
print("  So = 1/Sig0 (E2);  Se = 1-S1b (E1)  =>  So/Se = 1/[ Sig0 (1-S1b) ].")
print("  R1: So/Se->1  <=>  Sig0*(1-S1b) -> 1.")
print("  Using lem:cos S1b~1-cos w => 1-S1b~cos w; Sigma_0~w sin w (thm). So Sig0*(1-S1b)~ w sin w cos w.")
print("  At travel poles sin w_m=+-1, cos w_m=O(sqrt tau): w sin w cos w ~ +-w*O(sqrt tau). w~sqrt(2/tau)")
print("  => w*sqrt(tau) ~ sqrt 2 = O(1). So the product is O(1), consistent with ->1. CHECK the product:")
print(f"{'m':>2} | {'Sig0*(1-S1b)':>14} {'w sinw cosw':>13} {'w sinw (1-S1b)':>15}")
for m in [1,2,4,8,16,24,32]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(120/(1-q))
    Se,So=Se_So(q); S1b=Sbulk(1,q); Sig0=Sigma(0,q)
    sinw=mp.sin(w); cosw=mp.cos(w)
    print(f"{m:>2} | {mp.nstr(Sig0*(1-S1b),10):>14} {float(w*sinw*cosw):>13.7f} {float(w*sinw*(1-S1b)):>15.8f}")
