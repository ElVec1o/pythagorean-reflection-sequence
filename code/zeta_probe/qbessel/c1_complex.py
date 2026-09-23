import mpmath as mp
mp.mp.dps = 40
def B(q):
    s = mp.mpc(0); poch = mp.mpc(1); k = 0; qk2 = mp.mpc(1)
    while True:
        term = (-2*(1-q))**k * q**(k*k) / poch
        s += term
        if k > 5 and abs(term) < mp.mpf(10)**-45*(1+abs(s)): break
        poch *= (1-q**(2*k+1))*(1-q**(2*k+2)); k += 1
        if k > 4000: raise RuntimeError
    return s
# sign of S_e at travel poles: S_e = F(q,q)
def Se(q):
    return mp.nsum(lambda j: (-2*(1-q))**j*q**(j*(j+1))/mp.qp(q, q, 2*j), [0, mp.inf])
poles = ['0.449453630558948046125545825395706089225112809','0.913486638731047141696163474692948292895841542',
 '0.968041748897796712879013628111998908356772023','0.983579024832211895849276568660483203787250667',
 '0.990037396098083430693402966861837943133173023','0.993320999283196473429823216642215642074129799',
 '0.995213946155402358474695797894519799324053804','0.996403233360127229780702410971546504847898589',
 '0.997198755821726541686867042944788347210719899','0.997756894996171356935282772804393640232281569']
mp.mp.dps = 80
print("sign S_e(q_m) vs (-1)^(m-1):", [(m+1, int(mp.sign(Se(mp.mpf(p)))), (-1)**m) for m, p in enumerate(poles)])
mp.mp.dps = 40
# B on negative axis
print("B(-r) for r=0.5,0.9,0.99:", [mp.nstr(B(mp.mpf(-r)), 6) for r in (0.5, 0.9, 0.99)])
# complex zeros near q=-1 and near e^{2pi i/3}: Newton from a grid in t, q = zeta*exp(-t)
for zeta, name in [(mp.mpf(-1), '-1'), (mp.exp(2j*mp.pi/3), 'e^{2pi i/3}')]:
    roots = []
    for a in [0.03, 0.05, 0.08, 0.12, 0.18]:
        for b in [-0.3, -0.2, -0.12, -0.06, 0, 0.06, 0.12, 0.2, 0.3]:
            t0 = mp.mpc(a, b)
            try:
                t = mp.findroot(lambda t: B(zeta*mp.exp(-t)), t0, tol=1e-30, maxsteps=60)
            except Exception:
                continue
            if mp.re(t) > 0.01 and abs(t) < 0.4 and all(abs(t-r) > 1e-8 for r in roots):
                roots.append(t)
    roots.sort(key=lambda t: abs(t))
    print(f"zeta={name}: zeros t (q = zeta e^-t), sorted by |t|:")
    for t in roots[:14]:
        q = zeta*mp.exp(-t)
        print(f"   t={mp.nstr(t,10)}  arg(t)/deg={mp.nstr(mp.arg(t)*180/mp.pi,6)}  |q|={mp.nstr(abs(q),6)}  1/t={mp.nstr(1/t,8)}")
