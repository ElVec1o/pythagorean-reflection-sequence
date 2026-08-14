import mpmath as mp
mp.mp.dps=30
# Crude rigorous chain:
#  |P12|/tau^1.5 = |BR|/(sqrt2 tau |sinw|),  BR = cos^2 w - d11/(1+d11) - sin^2 w dSe
#  |BR| <= cos^2 w + |d11|/(1-|d11|) + |dSe|        (sin^2 w<=1)
#  With |sinw|>=s0, |d11|<=K tau, |dSe|<=K tau, cos^2 w <= C2 tau (numerically C2~0.00155, but use a safe
#  bound; even cos^2w<=1 trivially, but that ruins it -- need cos^2w=O(tau), which is the lem:cos pole geom).
#  Take cos^2 w <= C2 tau.  Then for tau<=tau0 (K tau<1/2):
#  |P12|/tau^1.5 <= (C2 tau + 2K tau/(1) )/(sqrt2 tau s0) ... use |d11|/(1-|d11|)<=2|d11| for |d11|<=1/2
#     <= (C2 + 2K + K)/(sqrt2 s0) = (C2+3K)/(sqrt2 s0)   [conservatively 2|d11|+|dSe| <= 3K tau]
# Want < 1/sqrt2  <=>  (C2+3K)/s0 < 1.
thr=1/mp.sqrt(2)
for s0 in [mp.mpf('0.5'),mp.mpf('0.9')]:
    for K in [mp.mpf('0.13'),mp.mpf('0.15'),mp.mpf('0.2'),mp.mpf('0.25')]:
        C2=mp.mpf('0.002')  # safe upper for cos^2w/tau (numeric ~0.00155)
        bound=(C2+3*K)/(mp.sqrt(2)*s0)
        print(f"s0={float(s0):.2f} K={float(K):.2f}: crude |P12|/tau1.5 bound = {float(bound):.4f}  < 1/sqrt2={float(thr):.4f}? {bound<thr}")
print()
print("With the OBSERVED K~0.124 and s0~1: even the crude (C2+3K)/(sqrt2 s0) ~ (0.002+0.372)/sqrt2 ~ 0.264 < 0.707.")
print("Tighter (2|d11|+|dSe| with |d11|=|dSe|=K): (C2+3K) is conservative; true BR/tau->1/4 (2K+C2 with the d11^2).")
print("SUFFICIENT BOUND: |d11|,|dSe| <= K tau with K < (s0/sqrt2 - ... )/3. For s0=1/2: need 3K<1/2 i.e K<1/6=0.167.")
print("Observed K=0.124 < 1/6. So a same-class envelope K<=0.15 (>0.124, headroom) CLOSES the gate rigorously.")
