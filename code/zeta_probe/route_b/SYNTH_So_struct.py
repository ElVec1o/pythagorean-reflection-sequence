import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("PART 13.  So structure: So=(p/2q)S0_bulk. Does S0_bulk have a lem:cos decomposition like S1_bulk?")
print("  Companion engine (numerator-asymptotic): S0_bulk ~ w sin w. Subleading? Test S0b vs W sin W form.")
print("  Conjecture (mirror of Se=cos W - T2): S0_bulk = W sin W + (saddle T2^num).")
print("="*120)
print(f"{'m':>3} {'w':>9} {'S0b':>14} {'w sin w':>14} {'W sin W':>14} {'S0b-W sin W':>14}")
for i in [1,2,4,8,16,24,32,40]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.8*float(w))
    W=w*mp.e**(-tau/2)
    S0b=Sbulk(0,q)
    print(f"{i:>3} {float(w):>9.3f} {float(S0b):>14.7f} {float(w*mp.sin(w)):>14.7f} {float(W*mp.sin(W)):>14.7f} {float(S0b-W*mp.sin(W)):>14.7f}")
    mp.mp.dps=60

print()
print("  So = (p/2q) S0_bulk. p=1-q. (p/2q) = (1-q)/(2q). With q=e^{-tau}: (1-q)/(2q)=(e^{tau}-1)/2=tau/2+tau^2/4+..")
print("  So ~ (tau/2)(W sin W).  W sin W: W~w-sqrt(tau/2), so W sin W = (w-sqrt(t/2))sin(w-sqrt(t/2)).")
print("  Compare So and Se leading TO HIGHER ORDER. Key: is So/Se -> 1 controlled, or needs lem:cos subleading?")
print(f"{'m':>3} {'So/sqrt(tau)':>14} {'Se/sqrt(tau)':>14} {'(So-Se)/tau':>14} {'So/Se-1':>13} {'(So/Se-1)/tau':>15}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    Se=1-S1b; So=(p/(2*q))*S0b
    print(f"{i:>3} {float(So/mp.sqrt(tau)):>14.8f} {float(Se/mp.sqrt(tau)):>14.8f} {float((So-Se)/tau):>14.8f} {float(So/Se-1):>13.2e} {float((So/Se-1)/tau):>15.8f}")
    mp.mp.dps=60

print()
print("CRUCIAL: (So/Se-1)/tau -> a finite constant? If yes, So/Se-1 = O(tau) -> 0 is RIGOROUS given")
print("  the leading forms match (both sin w sqrt(tau/2)) and the DIFFERENCE So-Se is O(tau^{3/2}).")
print("  So-Se = (p/2q)S0b - (1-S1b). Both ~ sin w sqrt(tau/2). The difference being O(tau^{3/2})")
print("  is what makes So/Se = 1 + O(tau).  Check (So-Se)/tau^{1.5} bounded:")
print(f"{'m':>3} {'(So-Se)/tau^1.5':>16}")
for i in [4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    Se=1-S1b; So=(p/(2*q))*S0b
    print(f"{i:>3} {float((So-Se)/tau**mp.mpf('1.5')):>16.8f}")
    mp.mp.dps=60
