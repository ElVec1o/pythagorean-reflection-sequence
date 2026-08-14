"""
Part 4: ASSEMBLY tension.

Colleague claim: the crude D_p-dressed m-series is ASYMPTOTIC/DIVERGENT, so the
prompt's strategy  sum_{m>=2} sup|L_m| <= 2 C_D sum (A'' sqrt tau)^m/m!  is NOT a
literal convergent majorant.  Closure needs (i) sharp e^{p^2/(2w)} + truncation, or
(ii) the TRUE L_m decay ~ tau^{(m+1)/2}.

BUT there is ALSO an existing file lemcos_tail_PROOF.py that claims a DIFFERENT,
genuinely-convergent majorant:
   sup|L_m| <= (2/m!) tau^{2m} E[C2t(N/2)^m],  N~Poisson(w),
   sum_{m>=2} ... = 2 E[Psi(tau^2 C2t(N/2))]  (Psi=e^x-1-x),  finite and O(tau).
This uses the per-p bound  |D_p(W)| <= 2^{-p} T_p(w)  (Touchard), NOT the (w/2)^p form.

KEY QUESTION: are these consistent?  Is the Touchard per-p bound 2^{-p} T_p(w) the
"correct" uniform-in-p device that the colleague's e^{p^2/(2w)} is a (looser) restatement
of?  T_p(w)=E[N^p], N~Poisson(w). sup_[0,w]|D_p| <= 2^{-p} T_p(w) = 2^{-p} E[N^p].
For comparison (w/2)^p e^{p^2/(2w)}:  is 2^{-p}E[N^p] <= (w/2)^p e^{p^2/(2w)} i.e.
E[N^p] <= w^p e^{p^2/(2w)} ?  (Poisson moment vs lognormal-type bound.)
"""
import mpmath as mp, sympy as sp
mp.mp.dps = 40

# Touchard per-p bound vs colleague sharp bound vs TRUE sup
def Dp_series(p, W, K=600):
    s = mp.mpf(0)
    for k in range(0, K+1):
        kp = (mp.mpf(0) if p > 0 else mp.mpf(1)) if k == 0 else mp.mpf(k)**p
        t = (-1)**k * kp * W**(2*k) / mp.factorial(2*k)
        s += t
        if k > float(W)+10 and abs(t) < mp.mpf('1e-40')*max(abs(s), mp.mpf(1)):
            break
    return s
def supDp(p, w, N=1000):
    best = mp.mpf(0)
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        v = (mp.mpf(0) if p > 0 else mp.mpf(1)) if Wv == 0 else abs(Dp_series(p, Wv))
        best = max(best, v)
    return best
def Tp(p, w):  # Touchard T_p(w)=E[N^p], N~Poisson(w); via Stirling-2 sum
    return sum(int(sp.functions.combinatorial.numbers.stirling(p, r, kind=2))*w**r for r in range(p+1))

print("="*70)
print("Compare 3 per-p bounds at w=20:  sup|D_p|  <=  2^-p T_p(w) [Touchard, RIGOROUS]")
print("   and colleague claim (w/2)^p e^{p^2/(2w)} [sharp, conjectural]")
print("="*70)
w = mp.mpf('20')
print(f"  {'p':>3} {'sup|D_p|':>14} {'2^-p T_p(w)':>16} {'(w/2)^p e^..':>16} {'Touch/sup':>10} {'sharp/sup':>10}")
for p in [0, 4, 8, 12, 16, 20, 24, 28]:
    s = supDp(p, w)
    tb = Tp(p, w)/mp.mpf(2)**p
    cb = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
    print(f"  {p:>3} {float(s):>14.4g} {float(tb):>16.4g} {float(cb):>16.4g} {float(tb/s):>10.3g} {float(cb/s):>10.3g}")

print()
print("Is Touchard 2^-p T_p(w) <= colleague sharp (w/2)^p e^{p^2/(2w)} ?")
print("(i.e. E[N^p] <= w^p e^{p^2/(2w)}, Poisson moment bound)")
allle = True
for w in [mp.mpf('5'), mp.mpf('20'), mp.mpf('80')]:
    for p in range(0, 40):
        lhs = Tp(p, w); rhs = w**p * mp.e**(mp.mpf(p*p)/(2*w))
        if lhs > rhs*(1+mp.mpf('1e-25')):
            allle = False
            print(f"   VIOLATION w={float(w)} p={p}: E[N^p]/w^p e^.. = {float(lhs/rhs):.4f}")
            break
print(f"   E[N^p] <= w^p e^{{p^2/(2w)}} for w in 5,20,80, p<40: {'HOLDS' if allle else 'FAILS'}")

print()
print("="*70)
print("ASSEMBLY: crude D_p-dressed m-series -- divergent (asymptotic)?")
print("  term(m) = (2/m!) tau^{2m} sum_p [j^p](C2t^m) * sup|D_p|_dressed")
print("  using DRESSED bound (w/2)^p e^{p^2/(2w)} for sup|D_p|, w=sqrt(2/tau)")
print("="*70)
jj = sp.symbols('j')
C2t = (jj+1)*(2*jj+3)*(4*jj+5)/72
for tval in ['0.01', '0.001']:
    tau = mp.mpf(tval); w = mp.sqrt(2/tau)
    print(f"  tau={tval}, w={float(w):.1f}:")
    terms = []
    for m in range(2, 40):
        Q = sp.Poly(sp.expand(C2t**m), jj)
        s = mp.mpf(0)
        for k in range(Q.degree()+1):
            c = abs(mp.mpf(str(Q.coeff_monomial(jj**k))))
            dressedDp = (w/2)**k * mp.e**(mp.mpf(k*k)/(2*w))   # beta=1/2 (sharp)
            s += c * dressedDp
        term = 2/mp.factorial(m) * tau**(2*m) * s
        terms.append((m, term))
    # find minimum
    mn = min(terms, key=lambda x: float(x[1]) if x[1] > 0 else 1e300)
    print(f"    minimal term at m*={mn[0]}, value={float(mn[1]):.3g}")
    print(f"    term(2)={float(terms[0][1]):.3g}  term(10)={float(terms[8][1]):.3g}  "
          f"term(20)={float(terms[18][1]):.3g}  term(39)={float(terms[-1][1]):.3g}")
    # is it eventually increasing? (divergent)
    growing = terms[-1][1] > terms[-2][1]
    print(f"    term(39)>term(38)? {'YES -> diverging tail (asymptotic series)' if growing else 'no'}")
