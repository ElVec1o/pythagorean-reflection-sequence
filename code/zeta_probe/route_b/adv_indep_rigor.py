import mpmath as mp, math
exec(open('adv_indep_mech.py').read().split('polestr=')[0])  # reuse defs
polestr=[l.strip() for l in open("poles.txt") if l.strip()]

print("="*110)
print("RIGOR PROBE: WHAT does R1 actually consume? Decompose Se at the pole.")
print(" At pole Sigma1=1 EXACTLY (defn). E1 (EXACT off-pole): Se=1-S1b. So Se=Sigma1-S1b at pole.")
print(" Write Sigma1=(1-cos w)+e_T,  S1b=(1-cos w)+e_B, with e=subleading. Then:")
print("   Se = Sigma1-S1b = e_T-e_B   (the (1-cos w) LEADING term CANCELS EXACTLY).")
print(" Q: is the LEADING (1-cos w) really identical in Sigma1 and S1b? Print 1-cos w vs each.")
print("="*110)
sqrt2=mp.sqrt(2)
print(f"{'m':>3} {'w':>7} | {'1-cos w':>11} {'Sigma1-1':>12} {'S1b-1':>12} | {'(Sig1-(1-cosw))':>15} {'(S1b-(1-cosw))':>15}")
for m in [4,8,16,32,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.6*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau)
    S1b=Sbulk(1,q,8000); Sig1=Sigma(1,q,8000)
    cosw=mp.cos(w)
    # at the pole Sigma1=1, so Sigma1-1=0. (1-cosw) is NOT 0; it's the leading model.
    # e_T := Sigma1 - (1-cosw);  here Sigma1=1 so e_T = 1-(1-cosw)=cosw.
    eT=Sig1-(1-cosw)
    eB=S1b-(1-cosw)
    print(f"{m:>3} {float(w):>7.2f} | {float(1-cosw):>11.7f} {float(Sig1-1):>12.3e} {float(S1b-1):>12.7f} | {float(eT):>15.8f} {float(eB):>15.8f}")
print(" NOTE Sigma1-1=0 at pole (machine), so Se=1-S1b=-(S1b-1). The leading (1-cosw) sits in BOTH eT,eB and cancels in Se=eT-eB.")

print()
print("="*110)
print("KEY: Se = -(S1b-1) at pole (since Sigma1=1, E1 => Se=1-S1b). So R1 only needs ONE block S1b,")
print(" plus the EXACT E2 for So. Verify Se = -(S1b-1) directly at poles (this is the actual content):")
print("="*110)
for m in [4,8,16,32,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.6*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    N=int(80/(1-q)); J=2*int(float(w))+250
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    S1b=Sbulk(1,q,8000); S0b=Sbulk(0,q,8000)
    print(f"m={m:>3}: Se={float(Se):.8e}  -(S1b-1)={float(-(S1b-1)):.8e}  diff={mp.nstr(abs(Se+(S1b-1)),3)}")
    # and So = (p/2q) S0b EXACT
    print(f"      So={float(So):.8e}  (p/2q)S0b={float((p/(2*q))*S0b):.8e}  diff={mp.nstr(abs(So-(p/(2*q))*S0b),3)}")

print()
print("="*110)
print("SO R1 reduces to (BOTH exact identities, no decomposition):")
print("   So/Se = [(p/2q) S0b] / [1-S1b]   at the pole.")
print("   -> need: S0b ~ w sinw (numerator-asymptotic THEOREM) and (1-S1b)=Se ~ (1/sqrt2)sqtau sinw.")
print("   The latter = -(S1b-1): the bulk block S1b's DEVIATION from 1 at the travel pole.")
print("   Since at the pole cos w = -(c_T)sqtau sinw + O(tau) (from Sigma1=1=(1-cosw)+c_T sqtau sinw),")
print("   S1b-1 = -cos w + c_B sqtau sinw +O(tau) = (c_T+c_B... wait sign) -> this is where SUBLEADING enters.")
print("="*110)
print("DIRECT TEST: at pole, is (1-S1b) governed by cos w (leading) or sqtau sinw (subleading)?")
print(" If pole forces cos w = O(sqtau), then 1-S1b ~ (subleading). Confirm cos w_m ~ c_T sqtau sinw:")
for m in [4,8,16,32,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.6*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau)
    cosw=mp.cos(w); sinw=mp.sin(w); sqtau=mp.sqrt(tau)
    ratio=cosw/(sqtau*sinw)
    print(f"m={m:>3} w={float(w):.2f}: cos w={float(cosw):+.6e}  cos w/(sqtau sinw)={float(ratio):+.6f} (->sqrt2/36={float(sqrt2/36):.6f}? sign/val)")
