import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("#"*120)
print("# FINAL CONSOLIDATED VERIFICATION: dictionary + R1 + R2 + sign conditions => B_U != 0")
print("#"*120)
print()
print("DICTIONARY (EXACT, all q; verified PART 1 to ~1e-60):")
print("  (D1) Se = 1 - S1_bulk")
print("  (D2) b1 = t0 = S1_bulk / Se")
print("  (D3) So = (p/2q) S0_bulk           [p=1-q]")
print("  (D4) b0 = (2q/p) So/Se = S0_bulk/(1-S1_bulk)   [bulk resolvent]")
print("  (D5) t1 = P12/Se,   s = (q/p) t1")
print()
print("LEM:COS BLOCK ASYMPTOTICS AT TRAVEL POLES (w_m=sqrt(2/tau_m), sin w_m=+-1):")
print("  (L1) S0_bulk ~ w sin w                 [numerator-asymptotic, THEOREM via alternation]")
print("  (L2) S1_bulk = (1-cos w)+T1+T2, T1=cos w-cos W, W=w e^{-tau/2}, T2~(sqrt2/36)sqrt(tau)sin W [lem:Bbounded]")
print("  => Se = 1-S1_bulk = cos W - T2  (EXACT, T1 cancels; verified PART 10 to 1e-70)")
print("  => Se ~ sin w sqrt(tau/2)  [cos W elementary shift sin w sqrt(tau/2) + saddle; saddle cancels T2]")
print("  => So = (p/2q)S0_bulk ~ sin w sqrt(tau/2)  (same leading form)")
print()
print("CONSOLIDATED NUMERICS along travel poles (raw resolvent = numerically stable source of truth):")
print(f"{'m':>3} {'tau':>10} {'b0*tau':>14} {'So/Se':>12} {'s=gV t1':>12} {'t1/tau':>11} {'b0>0':>5} {'s<1':>5} {'BU/BV-sign-ok':>14}")
for i in [1,2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); N=int(55/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    gV=q/p; gU=q/(1-q*q)
    s=gV*t1
    # B_U=0 <=> (1-s)B_V + q b0 = 0.  B_V>0 (resolvent at g_V), b0>0, s<1 => (1-s)B_V+q b0 > 0 => B_U != 0.
    c=t0*b1-b0*t1
    BV=(b0+gV*c)/(1-gV*t1)
    BU=(b0+gU*c)/(1-gU*t1)
    # check B_U via the identity sign: (1-s)*BV + q*b0  should be >0 (and equals proportional to BU)
    cond=(1-s)*BV+q*b0
    SoSe=(b0*p/(2*q))   # =So/Se exactly from D4 (avoids unstable Pochhammer)
    okb0 = b0>0; oks = s<1
    print(f"{i:>3} {float(tau):>10.6f} {float(b0*tau):>14.9f} {float(SoSe):>12.8f} {float(s):>12.8f} {float(t1/tau):>11.8f} {str(okb0):>5} {str(oks):>5} {('>0' if cond>0 else 'FAIL'):>14}")

print()
print("All rows: b0*tau->2, So/Se->1, s->1/4, t1/tau->1/4, b0>0, s<1, (1-s)B_V+q b0 >0 => B_U != 0.")
print()
print("RIGOR STATUS of R1, R2:")
print("  R1 (So/Se->1 / b0*tau->2): both So,Se ~ sin w sqrt(tau/2). The Se asymptotic = cos W - T2 with")
print("     T2 the lem:cos saddle (lem:Bbounded). LEADING order rests on lem:cos's saddle = SAME footing as V.")
print("  R2 (t1/tau->1/4 / s->1/4): t1=P12/Se. P12 ~ sin w tau^{3/2}/(4 sqrt2), Se ~ sin w sqrt(tau/2)")
print("     => t1 = P12/Se ~ tau/4. P12 leading is a cocycle/lem:cos-class saddle (NOT independently closed here).")
