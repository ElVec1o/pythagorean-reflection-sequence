import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*128)
print("PART 3.  Pin the constants. Se ~ C_e*sqrt(tau), So ~ (p/2q) w sin w. Derive R1: b0*tau->2 and R2: t1/tau->1/4")
print("="*128)
# From PART 1 (exact): b0 = S0b/(1-S1b) = So*(2q/p)/Se.
#   b0*tau = tau * So*(2q/p)/Se.
# At poles: So=(p/2q)*S0b ~ (p/2q)*(w sin w); Se ~ C_e sqrt(tau).
#   => b0*tau ~ tau*(2q/p)*(p/2q)(w sin w)/(C_e sqrt(tau)) = tau*(w sin w)/(C_e sqrt(tau))
#            = sqrt(tau)*w*sin w / C_e.  And w=sqrt(2/tau) => sqrt(tau)*w = sqrt(2).
#   => b0*tau ~ sqrt(2)*sin w_m / C_e.  With sin w_m=+-1 and b0*tau->2 (POSITIVE) => need
#            sqrt(2)*sin w_m / C_e = 2  with the sign of Se matching so the ratio is +2.
# So the claim R1 (b0*tau->2) is EQUIVALENT to:  Se / sin(w_m) -> sqrt(2)/2 * sqrt(tau) = sqrt(tau/2).
# i.e. Se ~ sin(w_m)*sqrt(tau/2).  Let's TEST that (Se has the SIGN of sin w_m and magnitude sqrt(tau/2)):
print("R1 reduces to:  Se ~ sin(w_m)*sqrt(tau/2).  Test Se/(sin w_m) and compare to sqrt(tau/2):")
print(f"{'m':>3} {'w':>9} {'sin w':>9} {'Se':>13} {'Se/sin w':>13} {'sqrt(tau/2)':>13} {'ratio':>11}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.6*float(w))
    S1b=Sbulk(1,q); Se=1-S1b
    sw=mp.sin(w)
    target=mp.sqrt(tau/2)
    print(f"{i:>3} {float(w):>9.3f} {float(sw):>9.4f} {float(Se):>13.8f} {float(Se/sw):>13.8f} {float(target):>13.8f} {float((Se/sw)/target):>11.7f}")
    mp.mp.dps=60

print()
print("So the constant C_e=0.66782... should be sqrt(1/2)/|...|? Check: Se/sin w ~ sqrt(tau/2) means")
print("  Se/sqrt(tau) ~ sin(w_m)*sqrt(1/2) = +-0.7071.  But earlier (Se-cosw)/sqrt(tau)->0.6678.")
print("  These differ because cos w_m is NOT negligible vs Se! Both ~sqrt(tau). Let's get Se/sqrt(tau) directly:")
print(f"{'m':>3} {'w':>9} {'sin w':>7} {'Se/sqrt(tau)':>14} {'sin w/sqrt2':>12} {'cos w/sqrt(tau)':>15}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.6*float(w))
    S1b=Sbulk(1,q); Se=1-S1b
    sw=mp.sin(w); cw=mp.cos(w)
    print(f"{i:>3} {float(w):>9.3f} {float(sw):>7.3f} {float(Se/mp.sqrt(tau)):>14.8f} {float(sw/mp.sqrt(2)):>12.8f} {float(cw/mp.sqrt(tau)):>15.8f}")
    mp.mp.dps=60
