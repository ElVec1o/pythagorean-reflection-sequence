#!/usr/bin/env python3
# ROUTE D3.2 -- CLEAN discrete-LG amplitude law + ERROR-CONTROL FUNCTION.
#
# Recursion:  z_{n+1} + z_{n-1} = b_n z_n,  b_n = 2 cos k_n  (oscillatory bulk).
# Transfer matrix  M_n = [[b_n, -1],[1,0]],  (z_{n+1},z_n)^T = M_n (z_n,z_{n-1})^T.
#
# (A) Clean amplitude law.  Build a COMPLEX solution that locally tracks e^{+i sum k}.
#     A single-mode complex solution Z_n (no standing wave) should obey
#         |Z_n|^2 sin k_n = const   (the discrete LG amplitude invariant),
#     equivalently  R_n sqrt(sin k_n) = const with R_n = |Z_n|.
#     We get a single-mode solution by complex initial data matched to the local
#     plane wave at n=1:  Z_1 = e^{i k_1}, Z_0 = 1  (so Z_1/Z_0 ~ e^{i k_1}).
#     This is NOT an exact eigen-solution but the *least* contaminated; we measure
#     the conserved combo via the proper LG invariant which removes the wobble:
#         J_n := (Z_{n+1} - e^{-i k_n} Z_n)(conj)(...)  -- too fiddly.
#     SIMPLER & RIGOROUS: use the EXACT modulus invariant for a complex solution
#     of a symmetric (unit off-diagonal) recursion:
#         Wronskian W = Z_n conj(Z_{n-1}) - Z_{n-1} conj(Z_n) = 2i Im(Z_n conj Z_{n-1})
#         is EXACTLY constant (real recursion, so conj(Z) is also a solution; their
#         Wronskian is conserved). And  Im(Z_n conj Z_{n-1}) = |amp|^2 sin k_n  for a
#         locally-plane-wave => |amp|^2 = W/(2i sin k_n) => |amp|^2 sin k_n = W/2i = const.
#     => The invariant we TEST is  Q_n := Im( Z_n * conj(Z_{n-1}) ), which is EXACTLY
#        constant (Wronskian/2). The LG content is then that |Z_n|^2 sin k_n ~ Q_n,
#        i.e.  |Z_n|^2 sin k_n / Q_n -> 1  (THIS is the LG amplitude law, error = LG error).
#
# (B) Error-control function.  Discrete LG (Wong-Li / Olver) error bound is governed by
#     the total variation of the "second difference of the slowly-varying part".
#     Define  F_n := 1/sqrt(sin k_n)  (the LG amplitude factor).  The error-control
#     function is  H = sum_n |Delta^2 log F_n| + sum_n |Delta(k_n) - k_n + ...|, but the
#     clean modern form (Spigler-Vianello) bounds the relative LG error by
#         Var := sum_{n} | g_n |,   g_n = (LG defect) =
#                second central difference of the amplitude / coupling.
#     We compute the practical error-control total variation
#         TV := sum_n | F_{n+1} - 2 F_n + F_{n-1} | / F_n   (curvature of amplitude)
#       + sum_n | k_{n+1} - 2 k_n + k_{n-1} |               (curvature of phase)
#     over the oscillatory bulk, and report whether TV stays BOUNDED (uniformly in tau)
#     or BLOWS UP as tau->0.  Boundedness of TV  <=>  Poincare-valid LG with controlled
#     remainder.  This is the crux for the C^infty/Poincare conclusion.

import mpmath as mp
mp.mp.dps = 40

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))

def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2:
        return None
    return mp.acos(bn/2)

def run(tau):
    q = mp.e**(-tau)
    cosh_term = 2*mp.cosh(mp.mpf("1.5")*tau)
    ratio = (cosh_term-2)/(2*(1-q)*q**mp.mpf("0.5"))
    nstar = mp.log(ratio)/(2*mp.log(q)) if 0<ratio<1 else mp.mpf(50)
    Nosc = int(float(nstar))  # last fully-oscillatory index (approx)

    # ---- (A) complex single-mode solution ----
    k1 = kfun(1, q)
    Z = [mp.mpf(1), mp.e**(1j*k1)]   # Z_0, Z_1
    n = 1
    while True:
        bn = bcoef(n, q)
        if abs(bn) >= 2:
            break
        Z.append(bn*Z[n] - Z[n-1])
        n += 1
        if n > Nosc + 5 or n > 6000:
            break
    Nlast = len(Z) - 1
    # Wronskian Q_n = Im(Z_n conj Z_{n-1}) should be EXACTLY constant
    Q = [mp.im(Z[m]*mp.conj(Z[m-1])) for m in range(1, Nlast+1)]
    Qspread = (max(Q)-min(Q))/abs(sum(Q)/len(Q))
    # LG amplitude law:  |Z_n|^2 sin k_n / Q_n -> 1 ?
    amp_law = []
    for m in range(1, Nlast):
        km = kfun(m, q)
        if km is None: break
        val = abs(Z[m])**2 * mp.sin(km) / Q[m-1]
        amp_law.append((m, val))
    # report amp_law in bulk (skip ends where boundary/turning effects)
    lo = max(2, Nlast//8); hi = Nlast - max(3, Nlast//8)
    bulk = [v for (m,v) in amp_law if lo<=m<=hi]
    if bulk:
        almin, almax = min(bulk), max(bulk)
    else:
        almin=almax=mp.nan

    # ---- (B) error-control total variation ----
    ks = []
    m = 1
    while True:
        km = kfun(m, q)
        if km is None: break
        ks.append((m, km))
        m += 1
        if m > Nosc+2: break
    # amplitude factor F = 1/sqrt(sin k)
    Fs = [(m, 1/mp.sqrt(mp.sin(km))) for (m,km) in ks]
    # second differences over the bulk
    TV_amp = mp.mpf(0); TV_phase = mp.mpf(0)
    kv = [km for (_,km) in ks]; Fv=[f for (_,f) in Fs]
    for i in range(1, len(kv)-1):
        TV_phase += abs(kv[i+1] - 2*kv[i] + kv[i-1])
        TV_amp   += abs(Fv[i+1] - 2*Fv[i] + Fv[i-1]) / Fv[i]
    # also the FIRST-difference variation of log-amplitude (the classic LG error fn
    # is the total variation of d/dn log F, i.e. sum |Delta log F| is the phase budget,
    # but the *error* is sum |Delta^2 ...|). Report both.
    TV_logF1 = mp.mpf(0)
    logF = [mp.log(f) for f in Fv]
    for i in range(1, len(logF)):
        TV_logF1 += abs(logF[i]-logF[i-1])

    print(f"tau={float(tau):.4f}  N_osc~{Nlast}  (n*={mp.nstr(nstar,5)})")
    print(f"   (A) Wronskian Q_n const: relspread={mp.nstr(Qspread,4)}  (sanity, should be ~0)")
    print(f"       LG amp law |Z|^2 sin k / Q in bulk: [{mp.nstr(almin,8)}, {mp.nstr(almax,8)}]  (target 1)")
    print(f"   (B) error-control TV(2nd diff): phase={mp.nstr(TV_phase,6)}  amp={mp.nstr(TV_amp,6)}")
    print(f"       total TV = {mp.nstr(TV_phase+TV_amp,6)}   |  TV(|Delta logF|, phase budget)={mp.nstr(TV_logF1,6)}")
    print()
    return (tau, Nlast, Qspread, almin, almax, TV_phase, TV_amp, TV_logF1)

results=[]
for tau in [mp.mpf("0.1"), mp.mpf("0.05"), mp.mpf("0.02"), mp.mpf("0.01"), mp.mpf("0.005")]:
    results.append(run(tau))

print("=== TV scaling as tau->0 (the crux) ===")
print(" tau      TV_phase     TV_amp      TV_total    TV_total*? ")
for r in results:
    tau=r[0]; tvp=r[5]; tva=r[6]; tot=tvp+tva
    print(f" {float(tau):.4f}  {mp.nstr(tvp,6):>11}  {mp.nstr(tva,6):>10}  {mp.nstr(tot,6):>10}   tot/sqrt(tau)={mp.nstr(tot/mp.sqrt(tau),5)}")
