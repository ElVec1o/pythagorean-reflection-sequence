import mpmath as mp, pickle
mp.mp.dps = 60
bn=[mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
N=len(bn)
def pade_B(L,M):
    p,q=mp.pade(bn[:L+M+1],L,M)
    return lambda s: mp.polyval(p[::-1],s)/mp.polyval(q[::-1],s)
# Use only the convergent-tail (denominator>=numerator) approximants that agreed in the BL test
Bs = {'[6/7]':pade_B(6,7),'[5/8]':pade_B(5,8),'[4/8]':pade_B(4,8),'[5/7]':pade_B(5,7),'[3/9]':pade_B(3,9)}
print("Growth of |B(t)| on R_+ (denominator-heavy Pade only):")
print(f"{'t':>6} " + " ".join(f"{k:>11}" for k in Bs))
for t in [mp.mpf(x) for x in ['1','5','10','25','50','100','250','500','1000','5000']]:
    print(f"{float(t):>6} " + " ".join(f"{mp.nstr(abs(Bs[k](t)),5):>11}" for k in Bs))
# Each [L/M] with M>L decays like t^{L-M} at infinity -> ARTIFICIALLY forces decay.
# So Pade CANNOT prove the true large-t law; it only shows B is BOUNDED on any finite range
# and consistent with slow growth. State this honestly.
print("\nNOTE: [L/M] with M>L ->0 as t->inf by construction (rational degree). So these CONFIRM")
print("boundedness on probed range but CANNOT certify the asymptotic growth law from 14 coeffs.")
