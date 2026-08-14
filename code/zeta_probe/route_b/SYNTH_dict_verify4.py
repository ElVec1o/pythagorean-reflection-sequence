import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*128)
print("PART 4.  R1 = So/Se->1 because BOTH ~ sin(w)*sqrt(tau/2).  Test the two leading forms together.")
print("="*128)
print("  So=(p/2q)S0b, S0b~w sin w => So ~ (p/2q) w sin w.  p=1-q~tau, w=sqrt(2/tau) => (p/2q)w -> sqrt(tau/2).")
print("  Se=1-S1b ~ sin w*sqrt(tau/2) (PART 3).  So So/Se -> [sqrt(tau/2) sin w]/[sqrt(tau/2) sin w] = 1.")
print()
print(f"{'m':>3} {'w':>9} {'So/sqrt(tau)':>14} {'Se/sqrt(tau)':>14} {'sin w/sqrt2':>13} {'So/Se':>12} {'So/Se-1':>11}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.0*float(w))
    S1b=Sbulk(1,q); Se=1-S1b
    Se2,So=Se_So(q)               # exact Pochhammer So
    sw=mp.sin(w)
    print(f"{i:>3} {float(w):>9.3f} {float(So/mp.sqrt(tau)):>14.8f} {float(Se/mp.sqrt(tau)):>14.8f} {float(sw/mp.sqrt(2)):>13.8f} {float(So/Se):>12.8f} {float(So/Se-1):>11.2e}")
    mp.mp.dps=60

print()
print("CONFIRM the chain numerically: b0*tau = (So/Se)*(2q/p)*tau, and (2q/p)*tau -> 2.")
print(f"{'m':>3} {'So/Se':>12} {'(2q/p)tau':>12} {'product':>12} {'b0*tau(raw)':>13} {'match':>9}")
for i in [1,2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); N=int(60/(1-q))
    mp.mp.dps=60
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se2,So=Se_So(q)
    prod=(So/Se2)*(2*q/p)*tau
    print(f"{i:>3} {float(So/Se2):>12.8f} {float((2*q/p)*tau):>12.8f} {float(prod):>12.8f} {float(b0*tau):>13.8f} {float(abs(prod-b0*tau)):>9.1e}")

print()
print("="*128)
print("PART 5.  R2 = t1/tau -> 1/4.  t1=P12/Se. Need P12 asymptotic. Test P12 ~ ? *sqrt(tau).")
print("="*128)
# t1=P12/Se, Se~sin w sqrt(tau/2). t1/tau->1/4 => P12 ~ (1/4)*tau*Se ~ (1/4)*tau*sin w*sqrt(tau/2)
#   = (1/4) sin w * tau^{3/2}/sqrt2.  Test P12/(tau^{3/2}) and P12/(Se*tau).
print(f"{'m':>3} {'w':>9} {'P12':>15} {'P12/Se':>13} {'t1/tau':>12} {'P12/(Se*tau)':>14} {'->1/4?':>9}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    mp.mp.dps=80
    P12,P22,P11,P21=cocycle(q,N)
    Se=P22
    t1=P12/Se
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(P12,8):>15} {float(P12/Se):>13.8f} {float(t1/tau):>12.8f} {float(P12/(Se*tau)):>14.8f} {float(P12/(Se*tau)):>9.6f}")
    mp.mp.dps=60
