import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("PART 14.  HONEST decomposition: which inputs does R1 truly need? Separate ELEMENTARY vs lem:cos pieces.")
print("="*120)
print("  Se = cos W - T2,   cos W = cos w cos(d) + sin w sin(d),  d := w-W = w(1-e^{-tau/2}).")
print("  d = sqrt(tau/2) - tau^{3/2}/(4 sqrt2)*... (ELEMENTARY, no lem:cos). cos d, sin d ELEMENTARY.")
print("  => Se = cos w cos d + sin w sin d - T2.")
print("     * sin w sin d  : ELEMENTARY, leading = sin w * sqrt(tau/2)  (the dominant piece).")
print("     * cos w cos d  : cos w is lem:cos-small (~(sqrt2/36)sqrt(tau)sin w); times cos d~1.")
print("     * T2           : lem:cos saddle ~ (sqrt2/36)sqrt(tau) sin W ~ (sqrt2/36)sqrt(tau) sin w.")
print("  The lem:cos pieces (cos w cos d) and (-T2) are EACH O(sqrt tau) and CANCEL to O(tau^{3/2}).")
print()
print(" Test: does [sin w sin d] ALONE already give Se to leading order (i.e. is the lem:cos part subleading)?")
print(f"{'m':>3} {'w':>9} {'Se/sqrt(tau)':>14} {'sin w sin d/sqrt(tau)':>22} {'lemcos part/sqrt(tau)':>22}")
for i in [1,2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.0*float(w))
    W=w*mp.e**(-tau/2); d=w-W
    S1b=Sbulk(1,q); Se=1-S1b
    cw=mp.cos(w); sw=mp.sin(w)
    T1=cw-mp.cos(W); T2=S1b-(1-cw)-T1
    elem = sw*mp.sin(d)            # ELEMENTARY dominant piece
    lemcos_part = cw*mp.cos(d) - T2   # the two lem:cos pieces (should cancel to O(tau^{3/2}))
    print(f"{i:>3} {float(w):>9.3f} {float(Se/mp.sqrt(tau)):>14.8f} {float(elem/mp.sqrt(tau)):>22.8f} {float(lemcos_part/mp.sqrt(tau)):>22.8f}")
    mp.mp.dps=60

print()
print("  VERDICT on the column 'lemcos part/sqrt(tau)': if it -> 0, then the DOMINANT Se asymptotic is")
print("  PURELY ELEMENTARY (sin w sin d), and lem:cos only controls a SUBLEADING cancellation. If it -> const !=0,")
print("  then lem:cos (the value (sqrt2/36) for both cos w AND T2) is load-bearing at leading order.")
print()
print("  Check the cancellation rate: lemcos_part / tau^{1.0} (is it O(tau)? => subleading vs sqrt(tau)):")
print(f"{'m':>3} {'lemcos_part/tau':>16} {'lemcos_part/sqrt(tau)':>22}")
for i in [4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.0*float(w))
    W=w*mp.e**(-tau/2); d=w-W
    S1b=Sbulk(1,q); cw=mp.cos(w); sw=mp.sin(w)
    T1=cw-mp.cos(W); T2=S1b-(1-cw)-T1
    lemcos_part = cw*mp.cos(d) - T2
    print(f"{i:>3} {float(lemcos_part/tau):>16.8f} {float(lemcos_part/mp.sqrt(tau)):>22.8f}")
    mp.mp.dps=60
