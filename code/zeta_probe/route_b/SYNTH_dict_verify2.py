import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*128)
print("PART 2.  AT TRAVEL POLES (Sigma_1_travel=1). Question: do So,Se,P12 have CLEAN lem:cos asymptotics here?")
print("  Known lem:cos forms (PROVEN-numerically): S1_bulk ~ 1-cos w ; S0_bulk ~ w sin w. w=sqrt(2/tau).")
print("  Dictionary (PART 1, exact): Se=1-S1b, So=(p/2q)S0b, b0=S0b/(1-S1b), t1=P12/Se, b1=S1b/Se.")
print("="*128)

# At travel poles, evaluate the BULK blocks S1b, S0b and compare to 1-cos w, w sin w.
# If S1b ~ 1-cos w and S0b ~ w sin w hold AT the travel poles too, then:
#   Se = 1 - S1b ~ 1-(1-cos w) = cos w      -> but cos w_m ~ O(sqrt tau) (VANISHES at travel poles!)
#   So = (p/2q) S0b ~ (p/2q) w sin w
#   b0 = S0b/(1-S1b) ~ w sin w / cos w = w tan w   -> blows up?  but b0*tau->2.  Need cos w correction.
# This is the crux: at travel poles, w_m ~ (m+3/2)pi where cos w ~ 0.  Test directly.
print(f"{'m':>3} {'w':>9} | {'S1b':>11} {'1-cos w':>11} {'r1':>9} | {'S0b':>11} {'w sin w':>11} {'r0':>9} | {'cos w':>11} {'Se':>11}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.5*float(w))
    S1b=Sbulk(1,q); S0b=Sbulk(0,q); Se=1-S1b
    cw=mp.cos(w); sw=mp.sin(w)
    r1 = S1b/(1-cw) if abs(1-cw)>1e-30 else mp.nan
    r0 = S0b/(w*sw) if abs(w*sw)>1e-30 else mp.nan
    print(f"{i:>3} {float(w):>9.3f} | {float(S1b):>11.6f} {float(1-cw):>11.6f} {float(r1):>9.5f} | {float(S0b):>11.5f} {float(w*sw):>11.5f} {float(r0):>9.5f} | {float(cw):>11.3e} {float(Se):>11.6f}")
    mp.mp.dps=60

print()
print("KEY OBSERVATION CHECK: at travel poles cos w_m is small but NOT exactly 0 (w_m != (m+1/2)pi exactly).")
print("  The naive 'Se=1-S1b ~ cos w -> 0' FAILS because S1b is NOT exactly 1-cos w (subleading matters).")
print("  Let's see the TRUE value of Se=1-S1b at poles vs cos w:")
print(f"{'m':>3} {'w':>9} {'Se=1-S1b':>13} {'cos w':>13} {'Se-cos w':>13} {'(Se-cosw)/sqrt(tau)':>20}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.6*float(w))
    S1b=Sbulk(1,q); Se=1-S1b
    cw=mp.cos(w)
    print(f"{i:>3} {float(w):>9.3f} {float(Se):>13.8f} {float(cw):>13.3e} {float(Se-cw):>13.8f} {float((Se-cw)/mp.sqrt(tau)):>20.8f}")
    mp.mp.dps=60
