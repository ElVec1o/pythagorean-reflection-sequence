import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("PART 10.  CENTRAL TRANSFER CHECK: is Se = 1 - S1_bulk EXACTLY the lem:cos-controlled object?")
print("  lem:cos decomposition of the BULK block: S1_bulk = (1-cos w) + T1 + T2,")
print("    W = w*exp(-tau/2),  T1 = cos w - cos W (EXACT, elementary),  T2 = saddle (lem:Bbounded).")
print("  => Se = 1 - S1_bulk = cos w - T1 - T2 = cos W - T2.   So Se = cos W - T2.")
print("  TEST: Se ?= cos W - T2  where T2 = S1_bulk-(1-cos w)-T1 (so this is exact by construction);")
print("  the CONTENT is whether cos W and T2 each have the claimed saddle size so Se~sqrt(tau/2) sin w.")
print("="*120)
print(f"{'m':>3} {'w':>9} {'W=w e^-t/2':>11} {'cos W':>13} {'T2':>13} {'cos W - T2':>13} {'Se':>13} {'match':>9}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.8*float(w))
    W=w*mp.e**(-tau/2)
    S1b=Sbulk(1,q); Se=1-S1b
    T1=mp.cos(w)-mp.cos(W)
    T2=S1b-(1-mp.cos(w))-T1
    print(f"{i:>3} {float(w):>9.3f} {float(W):>11.4f} {float(mp.cos(W)):>13.8f} {float(T2):>13.8f} {float(mp.cos(W)-T2):>13.8f} {float(Se):>13.8f} {float(abs((mp.cos(W)-T2)-Se)):>9.1e}")
    mp.mp.dps=60

print()
print("  So Se = cos W - T2 EXACTLY (T1 cancels). Now the saddle sizes AT the travel pole:")
print("   - cos W = cos(w e^{-tau/2}): test cos(W)/sqrt(tau) -> ? (this is the bulk's effective phase)")
print("   - T2: lem:cos saddle = Re[B_{s*} e^{iW}] ~ (sqrt2/36) sqrt(tau) sin W (PROVEN leading, lem:Bbounded)")
print(f"{'m':>3} {'cos W/sqrt(tau)':>16} {'T2/sqrt(tau)':>14} {'(cosW-T2)/sqrt(tau)':>20} {'sin w/sqrt2':>13}")
for i in [2,4,8,16,32,40]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.8*float(w))
    W=w*mp.e**(-tau/2)
    S1b=Sbulk(1,q); T1=mp.cos(w)-mp.cos(W); T2=S1b-(1-mp.cos(w))-T1
    sw=mp.sin(w)
    print(f"{i:>3} {float(mp.cos(W)/mp.sqrt(tau)):>16.8f} {float(T2/mp.sqrt(tau)):>14.8f} {float((mp.cos(W)-T2)/mp.sqrt(tau)):>20.8f} {float(sw/mp.sqrt(2)):>13.8f}")
    mp.mp.dps=60
