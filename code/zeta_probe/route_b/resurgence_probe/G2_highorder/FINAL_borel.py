"""Comprehensive final Borel analysis. Reads an_cache.pkl (best a_n). Runs all discriminators."""
import mpmath as mp, pickle, numpy as np
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=45
Nrel=max(n for n in an if agree[n]>=10)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
print("="*70)
print(f"FINAL BOREL ANALYSIS  (b_1..b_{Nrel} reliable >=10 dig)")
print("="*70)
A=4*mp.sqrt(2)*mp.e**(1j*mp.atan(2))
print(f"Working hypothesis A = 4*sqrt2*exp(i*arctan 2) = {mp.nstr(A,9)}")
print(f"   |A|={mp.nstr(abs(A),9)}  arg={mp.nstr(mp.arg(A)*180/mp.pi,7)} deg\n")
# 1. Pade conj-pair drift, last orders
def pade_roots(L,M):
    p,q=mp.pade([mp.mpf(b[i]) for i in range(L+M+1)],L,M)
    return sorted(np.roots([complex(x) for x in q][::-1]),key=abs)
print("--- Pade conjugate-pair nearest singularity vs order ---")
seq=[]
for tot in range(8,Nrel):
    L=tot//2; M=tot-L
    if L+M>Nrel: break
    try:
        r=pade_roots(L,M)
        cand=[z for z in r if 30<abs(np.degrees(np.angle(z)))<150]
        if cand:
            z=cand[0]; seq.append((tot,abs(z),abs(np.degrees(np.angle(z)))))
    except: pass
for t,R,th in seq:
    print(f"  ord{t}: |A|={R:.4f} |arg|={th:.3f}   (cand |A|=5.6569 |arg|=63.43)")
if len(seq)>=3:
    Rs=[s[1] for s in seq[-4:]]; ths=[s[2] for s in seq[-4:]]
    print(f"  => last-4 mean |A|={np.mean(Rs):.4f}+-{np.std(Rs):.4f}, |arg|={np.mean(ths):.3f}+-{np.std(ths):.3f}")
# 2. envelope test |b_n||A|^n bounded?
print("\n--- |b_n|*|A|^n (bounded&non-decaying => |A| correct; growing => |A| too big) ---")
RA=abs(A); vals=[abs(b[n])*RA**n for n in range(2,Nrel+1)]
print(f"  range over n=2..{Nrel}: min={float(min(vals)):.3f} max={float(max(vals)):.3f} last={float(vals[-1]):.3f}")
# 3. test wrong |A| to bracket: try 5.3, 5.66, 6.0, 6.28
print("\n--- bracket |A|: growth rate of max(|b_n| R^n) over last 5 n for trial R ---")
for Rtry in [5.0,5.3,5.5,5.6569,5.8,6.0,6.283]:
    v=[abs(b[n])*Rtry**n for n in range(Nrel-4,Nrel+1)]
    # geometric trend
    g=(v[-1]/v[0])**(mp.mpf(1)/4) if v[0]>0 else mp.mpf('nan')
    print(f"  R={Rtry:.4f}: max-tail growth/step={float(g):.4f}  (=1 ideal; <1 R too big; >1 R too small)")
