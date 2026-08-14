import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# At travel poles: confirm Se=1-S1b, So=(p/2q)S0b EXACTLY, and their lem:cos asymptotics.
# Travel pole => Sigma_1^travel=1 (that's the pole def). But Se,S0b are BULK blocks (S1b ~ 1-cos w).
# lem:cos: S1b ~ 1-cos w => Se=1-S1b ~ cos w.  S0b ~ w sin w => So=(p/2q)S0b, p~tau, => So ~ (tau/2) w sin w.
# Check b0*tau->2: b0=S0b/(1-S1b)=S0b/Se ~ (w sin w)/cos w = w tan w. But at TRAVEL poles cos w_m ->0!
# That is the subtlety: bulk blocks evaluated at TRAVEL poles (where cos w ~ O(sqrt tau), NOT exactly 0).
print("AT TRAVEL POLES: Se=1-S1b, So=(p/2q)S0b, b0=S0b/Se, and lem:cos leading forms")
print(f"{'m':>3} {'tau':>10} {'w':>9} {'cos w':>11} {'Se':>12} {'1-S1b':>12} {'b0*tau':>11} {'s=(q/p)t1':>11}")
for m in [1,2,4,8,16,32,48,64,80]:
    if m>len(poles): break
    q=poles[m-1]; N=int(55/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q); S0b=Sblk(0,q); S1b=Sblk(1,q)
    s=(q/p)*t1
    print(f"{m:>3} {float(tau):>10.6f} {float(w):>9.4f} {float(mp.cos(w)):>11.6f} {float(Se):>12.7f} {float(1-S1b):>12.7f} {float(b0*tau):>11.7f} {float(s):>11.7f}")
    # relative threshold (Pochhammer Se_clf cancellation ~1e42 terms, bulk Lambert trunc => scale w/ block size)
    relSe=abs(Se-(1-S1b))/(abs(Se)+1)
    relSo=abs(So-(p/(2*q))*S0b)/(abs(So)+1)
    relb0=abs(b0-S0b/Se)/(abs(b0)+1)
    assert relSe<mp.mpf(10)**(-10), (m,relSe)
    assert relSo<mp.mpf(10)**(-10), (m,relSo)
    assert relb0<mp.mpf(10)**(-10), (m,relb0)

print("\nIDENTITIES Se=1-S1b, So=(p/2q)S0b, b0=S0b/Se hold at ALL sampled poles (asserts passed).")

# Now the lem:cos asymptotic content of R1:
# b0*tau = tau*S0b/Se = tau*S0b/(1-S1b).  lem:cos: 1-S1b ~ cos w; S0b ~ w sin w.
# At travel pole cos w_m ~ O(sqrt tau). But b0*tau->2 NOT via w tan w (->inf). So the SUBLEADING of
# S0b and (1-S1b) matters. Print the lem:cos leading vs actual to see the cancellation structure.
print("\nlem:cos leading forms at travel poles (cos w small => subleading rules):")
print(f"{'m':>3} {'1-S1b':>12} {'cos w':>12} {'S0b':>12} {'w sin w':>12} {'b0*tau':>11} {'tau*wsinw/cosw':>14}")
for m in [4,8,16,32,64]:
    if m>len(poles): break
    q=poles[m-1]; N=int(55/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    S0b=Sblk(0,q); S1b=Sblk(1,q)
    naive=tau*(w*mp.sin(w))/mp.cos(w)
    print(f"{m:>3} {float(1-S1b):>12.7f} {float(mp.cos(w)):>12.7f} {float(S0b):>12.5f} {float(w*mp.sin(w)):>12.5f} {float(b0*tau):>11.7f} {float(naive):>14.5f}")
