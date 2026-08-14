import mpmath as mp
mp.mp.dps=120
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# R1: b0*tau -> 2.  b0 = S0b/(1-S1b) = S0b/Se.  So b0*tau = tau*S0b/Se.
# lem:cos leading: S1b ~ 1-cos w (so Se=1-S1b ~ cos w), S0b ~ w sin w.
# At travel poles cos(w_m)->0, so naive tau*S0b/Se ~ tau*(w sin w)/cos w blows up. The TRUE limit is 2.
# => Se=1-S1b at travel poles is NOT ~cos w_m alone; the subleading sqrt(tau) correction DOMINATES
#    (cos w_m itself is O(sqrt tau), same order as the lem:cos correction E=S1-(1-cos w)~c1 sqrt(tau)).
# Let me measure Se/sqrt(tau) and S0b/w  (i.e. S0b/(w sin w) won't work since sin w_m=+-1) at poles.
print("R1 mechanism at travel poles. sin w_m = +-1 (extreme phase).")
print(f"{'m':>3} {'tau':>11} {'w':>9} {'sin w':>9} {'Se':>13} {'Se/sqrt(tau)':>14} {'S0b':>11} {'S0b/w':>10} {'b0*tau':>11}")
for m in [1,2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); S0b=Sblk(0,q)
    print(f"{m:>3} {float(tau):>11.7f} {float(w):>9.4f} {float(mp.sin(w)):>9.5f} {float(Se):>13.8f} {float(Se/mp.sqrt(tau)):>14.8f} {float(S0b):>11.4f} {float(S0b/w):>10.5f} {float(b0*tau):>11.8f}")

# So b0*tau = tau*S0b/Se. With S0b ~ (sin w_m) * w * X  and Se ~ sqrt(tau)*Y:
#   b0*tau = tau * w * sin w * X / (sqrt(tau) Y) = sqrt(tau)*w * sin w * X/Y = sqrt(2) sin w X/Y (since sqrt(tau)*w=sqrt2)
# => b0*tau -> sqrt2 * sin w * (S0b/w)/(Se/sqrt tau).  For ->2 need sin w*(S0b/w)/(Se/sqrt tau) -> sqrt2.
print("\nDecompose: b0*tau = sqrt2 * [sin w * (S0b/w)] / [Se/sqrt(tau)]   (since sqrt(tau)*w=sqrt2)")
print(f"{'m':>3} {'sinw*(S0b/w)':>14} {'Se/sqrt(tau)':>14} {'ratio':>12} {'sqrt2=':>10} {'b0*tau':>11}")
for m in [2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); S0b=Sblk(0,q)
    num=mp.sin(w)*(S0b/w); den=Se/mp.sqrt(tau)
    print(f"{m:>3} {float(num):>14.8f} {float(den):>14.8f} {float(num/den):>12.8f} {float(mp.sqrt(2)):>10.6f} {float(b0*tau):>11.8f}")
