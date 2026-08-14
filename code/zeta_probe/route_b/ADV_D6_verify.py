"""
INDEPENDENT adversarial verification of the D6 shortcut derivation.
I re-derive everything from scratch and check at HIGH precision.

Key claims under test:
  [E1] det P = 1 exactly (per-step det = 1)
  [E2] P11 + P21 = 1 - Sig_t  for ALL q
  [E3] At a pole (Sig_t=1): P12 = 1/P11 - Se  exactly
  [S2] cos(w) - T2_Se = O(tau^{3/2}),  T2_Se = cos(W) - Se
  GATE: |P12|/tau^{3/2} -> 1/(4 sqrt2) = 0.17678, sup << 1/sqrt2

CRITICAL: poles.txt is only 40 digits. I will Newton-refine each pole to full
working precision before any "exact identity" test, exactly as the derivation
says it did, AND I will independently check that the unrefined residual tracks
the pole-location error.
"""
import mpmath as mp

# ---- independent cocycle (transcribed from the spec, then sanity-checked) ----
def cocycle_full(q, N):
    # Two independent solution columns of the same 2x2 step map M_n:
    #   column A = (x,y) starts (0,1)
    #   column B = (X,Y) starts (1,0)
    # The 2x2 transfer matrix P after N steps maps (initial)->(final):
    #   P @ [0,1]^T = [x,y]^T  ;  P @ [1,0]^T = [X,Y]^T
    # so  P = [[X, x],[Y, y]]  (columns are B then A).
    # D6/spec convention (their cocycle returns Y,y = P12,Se):
    #   P11=X, P12=Y, P21=x, P22=y=Se.
    x = mp.mpf(0); y = mp.mpf(1); X = mp.mpf(1); Y = mp.mpf(0)
    qn = mp.mpf(1)
    for n in range(1, N+1):
        qn *= q; q2n = qn*qn; q3n = q2n*qn
        xn = x*(1+2*q2n) - 2*y*qn
        yn = 2*x*q3n + y*(1-2*q2n)
        Xn = X*(1+2*q2n) - 2*Y*qn
        Yn = 2*X*q3n + Y*(1-2*q2n)
        x, y, X, Y = xn, yn, Xn, Yn
    # Return in D6 convention: P11, P12, P21, P22
    return X, Y, x, y

# Spec cocycle (their exact code) to fix the P12/Se labeling unambiguously:
def cocycle_spec(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y   # P12, Se

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

# Newton-refine a pole: solve Sig_t(q)=1
def refine_pole(q0, iters=6):
    q = mp.mpf(q0)
    h = mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0 = Sig_t(q) - 1
        fp = (Sig_t(q+h) - Sig_t(q-h))/(2*h)
        dq = f0/fp
        q = q - dq
        if abs(dq) < mp.mpf(10)**(-(mp.mp.dps-8)):
            break
    return q

poles = [mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*94)
print("INDEPENDENT D6 VERIFICATION")
print("="*94)

# ---------- Step 0: resolve labeling. Which spec output is P12? ----------
mp.mp.dps = 60
q = mp.mpf('0.97'); N = int(160/(1-q))
P12s, Ses = cocycle_spec(q, N)
P11, P12, P21, P22 = cocycle_full(q, N)
print("\n[labeling] spec P12 =", mp.nstr(P12s,8), " my X,Y,x,y =",
      mp.nstr(P11,8), mp.nstr(P12,8), mp.nstr(P21,8), mp.nstr(P22,8))
print("           spec Se  =", mp.nstr(Ses,8))
# Resolve: D6 returns X,Y,x,y = P11,P12,P21,P22. Spec returns Y,y = P12,Se.
print("           spec_P12 == my P12 (=Y)?", mp.nstr(P12s-P12,3))
print("           spec_Se  == my P22 (=y)?", mp.nstr(Ses-P22,3))

# ---------- [E1] per-step determinant is exactly 1 (symbolic + numeric) ----------
print("\n[E1] per-step det M_n = (1+2q^{2n})(1-2q^{2n}) - (-2q^n)(2q^{3n}) = 1 - 4q^{4n}+4q^{4n} = 1")
mp.mp.dps = 80
for qf in ['0.90','0.97','0.995']:
    q = mp.mpf(qf); N = int(160/(1-q))
    P11,P12,P21,P22 = cocycle_full(q,N)
    detP = P11*P22 - P12*P21
    print(f"   q={qf}:  det(assembled P) - 1 = {mp.nstr(detP-1,4)}")

# ---------- [E2] P11 + P21 = 1 - Sig_t  for ALL q ----------
print("\n[E2] P11 + P21 = 1 - Sig_t   (claimed exact for ALL q)")
for qf in ['0.90','0.95','0.97','0.99','0.995']:
    q = mp.mpf(qf); N = int(200/(1-q))
    P11,P12,P21,P22 = cocycle_full(q,N)
    St = Sig_t(q)
    res = (P11+P21) - (1-St)
    print(f"   q={qf}:  (P11+P21) - (1-Sig_t) = {mp.nstr(res,4)}   [P11={mp.nstr(P11,6)} P21={mp.nstr(P21,6)} Sig_t={mp.nstr(St,6)}]")

# ---------- [E3] at poles: P12 = 1/P11 - Se. UNREFINED vs Newton-refined ----------
print("\n[E3] At poles (Sig_t=1): P21=-P11, det=1 => P12 = 1/P11 - Se (EXACT)")
print("     Comparing UNREFINED (40-digit) pole vs Newton-REFINED pole.")
print(f"   {'m':>3} {'tau':>10} {'Sig_t-1 (unref)':>16} {'E3 resid unref':>16} {'Sig_t-1 (ref)':>14} {'E3 resid ref':>14}")
for m in [4,8,16,32,60]:
    q0 = poles[m-1]; tau0 = -mp.log(q0); w = mp.sqrt(2/tau0)
    mp.mp.dps = 50 + int(3.0*float(w))
    q0 = poles[m-1]; tau0 = -mp.log(q0); N = int(110/(1-q0))
    # unrefined
    P11,P12,P21,P22 = cocycle_full(q0,N)
    St0 = Sig_t(q0)
    e3_unref = P12 - (1/P11 - P22)
    # refined
    qr = refine_pole(q0)
    Nr = int(110/(1-qr))
    P11r,P12r,P21r,P22r = cocycle_full(qr,Nr)
    Str = Sig_t(qr)
    e3_ref = P12r - (1/P11r - P22r)
    print(f"   {m:>3} {float(tau0):>10.3e} {mp.nstr(St0-1,3):>16} {mp.nstr(e3_unref,3):>16} {mp.nstr(Str-1,3):>14} {mp.nstr(e3_ref,3):>14}")
    mp.mp.dps = 50
