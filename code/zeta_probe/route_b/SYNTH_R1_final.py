import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("PART 15.  Is R1 (So/Se->1) fully ELEMENTARY (modulo S0_bulk~w sin w, S1_bulk-(1-cosw)=O(sqrt tau))?")
print("="*120)
print("  Se = cos W - T2 ; So = (p/2q) S0_bulk. Define the ELEMENTARY models:")
print("    Se_el = sin w sin d            (d=w-W; we just showed Se = Se_el + o(sqrt tau))")
print("    So_el = (p/2q) W sin W         (the companion 'shifted' numerator)")
print("  Test So_el/Se_el and whether So/Se tracks it. Both should -> 1.")
print()
print(f"{'m':>3} {'w':>9} {'So/Se':>13} {'So_el/Se_el':>13} {'diff':>11} {'(So/Se-1)/tau':>15} {'(So_el/Se_el-1)/tau':>20}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    W=w*mp.e**(-tau/2); d=w-W
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    Se=1-S1b; So=(p/(2*q))*S0b
    Se_el=mp.sin(w)*mp.sin(d)
    So_el=(p/(2*q))*W*mp.sin(W)
    r=So/Se; r_el=So_el/Se_el
    print(f"{i:>3} {float(w):>9.3f} {float(r):>13.9f} {float(r_el):>13.9f} {float(r-r_el):>11.2e} {float((r-1)/tau):>15.8f} {float((r_el-1)/tau):>20.8f}")
    mp.mp.dps=60

print()
print("  Observation: if (So_el/Se_el-1)/tau also -> 1/2, the ELEMENTARY model reproduces R1's rate. Then R1")
print("  reduces to: (i) S0_bulk ~ w sin w [L1, theorem], (ii) S1_bulk-(1-cos w)=O(sqrt tau) [lem:cos, the")
print("  bound NOT the exact value], (iii) elementary shift algebra. The leading 1/sqrt2 is elementary; the")
print("  ->1 ratio needs the O(sqrt tau) BOUND on the lem:cos remainder (so Se's subleading doesn't spoil it).")
print()
print("="*120)
print("PART 16.  R2 honest: t1/tau->1/4. Decompose P12 elementarily too. P12 from cocycle; test P12 vs (Se,So).")
print("="*120)
# t1 = P12/Se. Also from resolvent: s=(q/p)t1 and b0=(2q/p)So/Se. Is there an EXACT relation t1 <-> So,Se?
# The Mobius B(g)=(b0+g c)/(1-g t1), c=t0 b1 - b0 t1. There may be a 2nd q-series for t1 like So for b0.
# Empirically t1/tau->1/4 and (t1/tau-1/4)/tau->1/16. Test if t1 = (something elementary)*(So or Se).
print("  Test candidate: t1 =? (1/2)*Se*? or t1/Se vs sqrt(tau). And the cleaner s=(q/p)t1->1/4.")
print(f"{'m':>3} {'w':>9} {'t1':>14} {'t1/Se':>13} {'t1/(Se sqrt(tau))':>18} {'s':>12} {'(s-1/4)/tau':>13}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(55/(1-q))
    mp.mp.dps=60
    b0,b1,t0,t1,L,qp=raw(q,N)
    S1b=Sbulk(1,q); Se=1-S1b
    s=(q/p)*t1
    print(f"{i:>3} {float(w):>9.3f} {float(t1):>14.9f} {float(t1/Se):>13.8f} {float(t1/(Se*mp.sqrt(tau))):>18.8f} {float(s):>12.9f} {float((s-mp.mpf(1)/4)/tau):>13.8f}")
