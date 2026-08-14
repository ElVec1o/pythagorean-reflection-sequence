import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*128)
print("PART 6.  Is Se ~ sin(w)sqrt(tau/2) a CONSEQUENCE of lem:cos, or a NEW asymptotic?")
print("  lem:cos (PROVEN-modulo-cited-Olver via lem:Bbounded): S1_bulk = (1-cos w) + E1(w), E1=O(sqrt tau).")
print("  The saddle gives E1 ~ -(sqrt2/36)sqrt(tau)*sin w*<factor>. Test S1_bulk-(1-cos w) vs sqrt(tau) sin w.")
print("="*128)
print(f"{'m':>3} {'w':>9} {'E1=S1b-(1-cosw)':>17} {'E1/sqrt(tau)':>14} {'E1/(sqrt(tau)sin w)':>20}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.8*float(w))
    S1b=Sbulk(1,q)
    E1=S1b-(1-mp.cos(w))
    sw=mp.sin(w)
    print(f"{i:>3} {float(w):>9.3f} {float(E1):>17.10f} {float(E1/mp.sqrt(tau)):>14.8f} {float(E1/(mp.sqrt(tau)*sw)):>20.10f}")
    mp.mp.dps=60

print()
print("  So Se = 1-S1b = cos w - E1.  At poles cos w_m = (some O(sqrt tau)) and E1 = O(sqrt tau).")
print("  Se/sqrt(tau) = cos w/sqrt(tau) - E1/sqrt(tau).  We found Se/sqrt(tau)->sin w/sqrt2=+-0.70711.")
print("  Decompose: cos w_m/sqrt(tau) and -E1/sqrt(tau), check they sum to sin w/sqrt2:")
print(f"{'m':>3} {'cos w/sqrt(tau)':>16} {'-E1/sqrt(tau)':>15} {'sum':>13} {'sin w/sqrt2':>13}")
for i in [2,4,8,16,32,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.8*float(w))
    S1b=Sbulk(1,q); E1=S1b-(1-mp.cos(w))
    cw=mp.cos(w); sw=mp.sin(w)
    s=cw/mp.sqrt(tau)-E1/mp.sqrt(tau)
    print(f"{i:>3} {float(cw/mp.sqrt(tau)):>16.8f} {float(-E1/mp.sqrt(tau)):>15.8f} {float(s):>13.8f} {float(sw/mp.sqrt(2)):>13.8f}")
    mp.mp.dps=60

print()
print("="*128)
print("PART 7.  CRITICAL: is Se->0 (sin w sqrt(tau/2)) the SAME extreme-phase statement lem:Bbounded controls?")
print("  lem:extremephase controls E(w)=Sigma_1_TRAVEL-(1-cos w) at w=m*pi. Here we need S1_BULK behaviour")
print("  AT THE TRAVEL POLE w_m=sqrt(2/tau_m)~(m+3/2)pi.  These are DIFFERENT phases & DIFFERENT block (bulk).")
print("  So the relevant question: does lem:Bbounded's machinery cover the BULK block S1_bulk too?")
print("  Memory says: 'lem:Bbounded covers S_1 (bulk) too => same closes the bulk poles for (2)/U'.")
print("  Test: cos(w_m)/sqrt(tau) -> sqrt2/36 = 0.0392837 (the lem:cos saddle constant)? (it's the cos-side):")
sd=mp.sqrt(2)/36
print(f"  sqrt2/36 = {float(sd):.10f}")
print(f"{'m':>3} {'w':>9} {'cos w/sqrt(tau)':>16} {'vs sqrt2/36':>13}")
for i in [2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f"{i:>3} {float(w):>9.3f} {float(mp.cos(w)/mp.sqrt(tau)):>16.10f} {float(sd):>13.10f}")
