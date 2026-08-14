import mpmath as mp, pickle
mp.mp.dps = 60
bn = [mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
an = [mp.mpf(s) for s in pickle.load(open('/tmp/an_vals.pkl','rb'))]
data = pickle.load(open('/tmp/poles_data.pkl','rb'))
ms=sorted(data.keys())
N=len(bn)

# DEFINITIVE CONSISTENCY TEST:
# g(tau) = (1/tau) ∫_0^∞ B(tau u) e^{-u} du = ∫_0^∞ B(s) e^{-s/tau} ds/tau  (Borel-Laplace).
# i.e. g(tau) = (1/tau)∫_0^∞ B(s) e^{-s/tau} ds. True g(tau)=dev/sqrt(tau/2) at a pole.
# If our Pade-Borel B(s) (using denominator-heavy approx) reproduces the TRUE dev_m to many
# digits, then B is CORRECT on R_+ AND its growth there is at most what the Laplace integral
# tolerates (sub-exponential at the scale 1/tau). This is the program's own NS-a confirmation,
# re-done from scratch here, and simultaneously bounds B on R_+.
def pade_B(L,M):
    p,q=mp.pade(bn[:L+M+1],L,M)
    return lambda s: mp.polyval(p[::-1],s)/mp.polyval(q[::-1],s)
B67 = pade_B(6,7); B58=pade_B(5,8); B48=pade_B(4,8)

mp.mp.dps=200
# true dev at several m; recompute w precisely from stored string (high prec)
W={m:mp.mpf(data[m][0]) for m in ms}
def true_g(m):
    tau=2/W[m]**2
    dev=(m+mp.mpf(1)/2)*mp.pi - W[m]
    return dev/mp.sqrt(tau/2), tau

print("Borel-Laplace sum of Pade-Borel B vs TRUE g(tau):")
print(f"{'m':>3} {'tau':>10} {'true g':>16} {'BL[6/7]':>16} {'digits':>7}")
for m in [6,8,10,12,16,20,25,30]:
    g_true, tau = true_g(m)
    # Laplace: g = (1/tau)∫_0^∞ B(s) e^{-s/tau} ds.  B from low-prec pade (dps60 enough for B).
    integ = mp.quad(lambda s: B67(s)*mp.e**(-s/tau), [0, tau, 5*tau, 20*tau, mp.inf])
    g_bl = integ/tau
    dig = -mp.log10(abs((g_bl-g_true)/g_true)) if g_bl!=g_true else mp.inf
    print(f"{m:>3} {mp.nstr(tau,6):>10} {mp.nstr(g_true,12):>16} {mp.nstr(g_bl,12):>16} {mp.nstr(dig,4):>7}")
