import mpmath as mp
mp.mp.dps=120
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Fact 2: Se=1-S1b satisfies (1-S1b)*w -> 1 at travel poles.
# lem:cos: S1b = (1-cos w) + E_b,  E_b ~ c sqrt(tau) sin w (bulk extreme-phase correction).
# So 1-S1b = cos w - E_b.  At travel poles need (cos w_m - E_b)*w_m -> 1.
# Travel poles: Sigma_1^travel=1 => w_m are roots of TRAVEL block=1, NOT bulk. There cos w_m = O(sqrt tau).
# Let me get the precise relation cos(w_m) and E_b at poles.
print("Fact 2:  Se=1-S1b,  (1-S1b)*w -> 1 ?   And decomposition cos w - E_b.")
print(f"{'m':>3} {'tau':>11} {'w':>9} {'Se*w':>12} {'cos w * w':>12} {'(cosw-E)*w':>12} {'E=S1b-(1-cosw)':>15}")
for m in [1,2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    S1b=Sblk(1,q); Se=1-S1b
    E=S1b-(1-mp.cos(w))
    print(f"{m:>3} {float(tau):>11.7f} {float(w):>9.4f} {float(Se*w):>12.8f} {float(mp.cos(w)*w):>12.6f} {float((mp.cos(w)-E)*w):>12.8f} {float(E):>15.8f}")

# Both cos w*w (->? ) and E*w matter. Show their individual w-scaled limits and the travel-pole constraint.
# The travel pole condition Sigma_1^T=1 fixes w_m s.t. cos(w_m) = c_T sqrt(tau) (extreme phase of TRAVEL).
# Print cos(w_m)/sqrt(tau) and E_bulk/sqrt(tau):
print("\nTravel-pole extreme-phase content (everything /sqrt(tau)):")
print(f"{'m':>3} {'cos w/sqrt(tau)':>16} {'E_bulk/sqrt(tau)':>17} {'Se/sqrt(tau)':>14} {'->1/sqrt2=0.7071':>16}")
for m in [2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); st=mp.sqrt(tau)
    S1b=Sblk(1,q); Se=1-S1b
    E=S1b-(1-mp.cos(w))
    print(f"{m:>3} {float(mp.cos(w)/st):>16.8f} {float(E/st):>17.8f} {float(Se/st):>14.8f} {float(1/mp.sqrt(2)):>16.8f}")
