import mpmath as mp, pickle
mp.mp.dps = 60
bn = [mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
N = len(bn)
print(f"have b_0..b_{N-1}")

# sign pattern
print("sign(b_n):", "".join("+" if b>0 else ("-" if b<0 else "0") for b in bn))

# Pade-Borel: diagonal Pade [L/L] of B(t)=sum b_n t^n. Use mpmath.pade.
# pade needs taylor coeffs; we have N=14 -> can do up to [6/6] (needs 13 coeffs) or [6/7].
def pade_eval(L, M, t):
    # build [L/M] from bn (needs L+M+1 <= N)
    p,q = mp.pade(bn[:L+M+1], L, M)
    num = mp.polyval(p[::-1], t); den = mp.polyval(q[::-1], t)
    return num/den

# Probe |B(t)| on R_+ via several Pade orders; compare to raw truncation.
print("\n=== |B(t)| on R_+ : Pade-Borel [6/6],[6/7],[5/7] vs partial sum ===")
print(f"{'t':>6} {'PS(t)':>14} {'P[6/6]':>14} {'P[6/7]':>14} {'P[5/7]':>14}")
for t in [mp.mpf(x) for x in ['0.5','1','2','3','4','4.5','5','6','8','10','15','20','30']]:
    ps = sum(bn[n]*t**n for n in range(N))
    p66 = pade_eval(6,6,t); p67=pade_eval(6,7,t); p57=pade_eval(5,7,t)
    print(f"{float(t):>6} {mp.nstr(ps,8):>14} {mp.nstr(p66,8):>14} {mp.nstr(p67,8):>14} {mp.nstr(p57,8):>14}")
