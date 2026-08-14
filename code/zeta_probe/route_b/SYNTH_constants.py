import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*100)
print("PART 8.  Identify constants in closed form (the lem:cos saddle bookkeeping).")
print("="*100)
c_E1   = -mp.sqrt(2)*mp.mpf(17)/36     # candidate: E1/(sqrt(tau) sin w) -> -sqrt2*17/36
c_cos  =  mp.sqrt(2)/36                # cos w/sqrt(tau) -> sqrt2/36 (lem:cos saddle)
c_Se   =  1/mp.sqrt(2)                 # Se/sqrt(tau) -> sin w/sqrt2 (=1/sqrt2 in magnitude)
print(f"candidate E1 const  -sqrt2*17/36 = {float(c_E1):.12f}   (numerics ->) -0.66782108")
print(f"candidate cos const  sqrt2/36     = {float(c_cos):.12f}   (numerics ->)  0.03928371")
print(f"check sum: sqrt2/36 + sqrt2*17/36 = sqrt2*18/36 = sqrt2/2 = {float(c_cos+(-c_E1)):.12f}  vs 1/sqrt2={float(c_Se):.12f}")
print(f"  => Se/sqrt(tau) -> sqrt2/36 + sqrt2*17/36 = sqrt2*18/36 = sqrt2/2 = 1/sqrt2.  CLEAN.")
print()
print("So the EXACT leading saddle decomposition at travel poles is:")
print("  cos(w_m)         ~  (sqrt2/36)   sqrt(tau) sin w_m   [via |sin w_m|=1; sign tracks]")
print("  S1_bulk-(1-cosw) ~ -(sqrt2*17/36) sqrt(tau) sin w_m")
print("  Se=1-S1b = cos w - E1 ~ (sqrt2/36 + sqrt2*17/36) sqrt(tau) sin w = (sqrt2/2) sqrt(tau) sin w")
print("           = sqrt(tau/2) sin w_m   [matches PART 3 to 1e-5 rel]")
print()
# Now SAME for So. So=(p/2q)S0b, S0b~w sin w. Let's get the exact subleading of So/sqrt(tau).
print("="*100)
print("PART 9.  So leading constant.  So/sqrt(tau) -> sin w/sqrt2 too (PART 4). Verify the chain gives 1/4 for R2.")
print("="*100)
# t1 -> ? We have b0 = So/Se *(2q/p). And the resolvent Mobius: B(g)=(b0+g*c)/(1-g*t1), c=t0*b1-b0*t1.
# s=(q/p)t1. R2 says s->1/4. Equivalent t1/tau->1/4 (since (q/p)tau->1).
# From dict: t1=P12/Se. So R2 <=> P12/(Se*tau)->1/4 <=> P12 ~ (1/4) Se tau ~ (1/4)(sqrt(tau/2)sin w)tau.
# i.e. P12 ~ (1/4) sin w * tau^{3/2}/sqrt2 = sin w tau^{3/2}/(4 sqrt2).
print("R2 <=> P12 ~ sin(w) tau^{3/2}/(4 sqrt2).  Test P12/(tau^{3/2}) -> sin w/(4 sqrt2)=+-0.176777:")
print(f"{'m':>3} {'w':>9} {'P12/tau^1.5':>15} {'sin w/(4 sqrt2)':>16} {'ratio':>11}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(55/(1-q))
    mp.mp.dps=80
    P12,P22,P11,P21=cocycle(q,N)
    sw=mp.sin(w)
    target=sw/(4*mp.sqrt(2))
    print(f"{i:>3} {float(w):>9.3f} {float(P12/tau**mp.mpf('1.5')):>15.10f} {float(target):>16.10f} {float((P12/tau**mp.mpf('1.5'))/target):>11.7f}")
    mp.mp.dps=60
