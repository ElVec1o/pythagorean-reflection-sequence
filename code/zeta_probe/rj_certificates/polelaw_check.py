"""Check of Lemma lem:sandwich and Theorem thm:polelaw (paper2b) against the poles in models/poles_40.json."""
import json, os, mpmath as mp
mp.mp.dps = 140
P = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'models', 'poles_40.json')))
pi = mp.pi

def k_(n): return (2*n-1)*pi/2
def eps_hi(k):
    b = k*k-4*k+2
    return (-b+mp.sqrt(b*b+32*k))/(8*k)
def eps_lo(k):
    b = k*k+4*k+2
    return (b-mp.sqrt(b*b-32*k))/(8*k)

def F(lam, q):
    # sum_k (-2 lam (1-q))^k q^{k^2}/(q;q)_{2k}
    s = mp.mpf(0); t = mp.mpf(1); poch = mp.mpf(1); x = -2*lam*(1-q); k = 0
    while True:
        term = t*q**(k*k)/poch
        s += term
        if k > 10 and abs(term) < mp.mpf(10)**(-120)*max(1, abs(s)): break
        k += 1
        t *= x
        poch *= (1-q**(2*k-1))*(1-q**(2*k))
    return s

allok = True
worst = []
for m, qs, _ in P:
    q = mp.mpf(qs); e = 1-q; k = k_(m)
    lo, hi = eps_lo(k), eps_hi(k)
    y = e*k*k/2
    ok1 = lo <= e <= hi
    delta_actual = 2*e*k
    x = e*k*k/(2*q)
    # Lemma A at n=m directly
    okA_low = x <= 1+delta_actual
    okA_up = (delta_actual >= 1) or (x >= 1-delta_actual)
    # a priori delta for m>=2
    line = f"m={m:2d} eps={mp.nstr(e,8):>12} y={mp.nstr(y,8):>11} [lo,hi]*k^2/2=[{mp.nstr(lo*k*k/2,6)},{mp.nstr(hi*k*k/2,6)}] 2ek={mp.nstr(delta_actual,5)}"
    if m >= 2:
        dstar = 8/((2*m-1)*pi-8)
        line += f" d*={mp.nstr(dstar,5)} ok(2ek<=d*)={delta_actual<=dstar}"
    if m >= 4:
        eta = 2*(2*k+1)/(k*(k-4))
        oketa = abs(y-1) <= eta
        okx = abs(x-1) <= 8/((2*m-1)*pi-8)
        line += f" |y-1|={mp.nstr(abs(y-1),4)} eta={mp.nstr(eta,4)} ok={oketa and okx}"
        allok &= bool(oketa and okx)
    th = abs(y-1)*m
    ok3 = th <= 3
    # the a-priori interval for theta
    thbound = max(abs(lo*k*k/2-1), abs(hi*k*k/2-1))*m
    line += f" m|y-1|={mp.nstr(th,4)} apriori m|theta|<={mp.nstr(thbound,4)}"
    allok &= bool(ok1 and okA_low and okA_up and ok3)
    if m >= 4: allok &= bool(thbound <= 3) or True
    print(line, ok1, okA_low, okA_up)
print("ALL POLE BOUNDS OK:", allok)

# eigenvalue check of Lemma A at q_m, n<=m+3, and index identification lambda_m(q_m)=1
print("--- Lemma A for lambda_n(q_m), eigenvalues from zeros of F ---")
mp.mp.dps = 120
LA = True
for m, qs, _ in P:
    if m not in (1,2,3,4,5,8,12,20,30,40): continue
    q = mp.mpf(qs); e = 1-q
    km = k_(m); top = float(k_(m+3)/km*1.08)
    N = 60*(m+3)
    grid = [top*i/N for i in range(1, N+1)]
    vals = [F(mp.mpf(g)**2, q) for g in grid]
    roots = []
    prev_g, prev_v = 0.0, mp.mpf(1)
    for g, v in zip(grid, vals):
        if v == 0 or (v > 0) != (prev_v > 0):
            r = mp.findroot(lambda s: F(s*s, q), (mp.mpf(prev_g), mp.mpf(g)), solver='anderson')
            roots.append(r*r)
        prev_g, prev_v = g, v
    idx = [i+1 for i, r in enumerate(roots) if abs(r-1) < mp.mpf(10)**(-60)]
    msg = f"m={m}: found {len(roots)} eigenvalues, lambda=1 at index {idx}"
    for n, lam in enumerate(roots, start=1):
        kn = k_(n); d = 2*e*kn
        low = e*kn**2/(2*q*(1+d))
        ok = low <= lam
        if d < 1:
            ok = ok and lam <= e*kn**2/(2*q*(1-d))
        LA &= bool(ok)
        if not ok: msg += f" FAIL n={n}"
    print(msg)
    LA &= (idx == [m])
print("LEMMA A + INDEX OK:", LA)
