#!/usr/bin/env python3
# Hunt the irreducible bedrock constant s1 (subleading of R/(tau^{5/2} sin w)) against EXOTIC transcendentals.
# Usage:  python3 hunt_s1.py bedrock90.csv
import sys, math, itertools
import mpmath as mp
mp.mp.dps = 120

# --- load high-precision c2 = |R/(tau^{5/2} sin w)| per pole from the Rust CSV ---
rows=[]
for ln in open(sys.argv[1] if len(sys.argv)>1 else 'bedrock90.csv'):
    ln=ln.strip()
    if not ln or ln.startswith('m,') or ln.startswith('#'): continue
    p=ln.split(',')
    if len(p)<11 or p[8]=='nan': continue
    rows.append((int(p[0]), mp.mpf(p[10]), abs(mp.mpf(p[8])/mp.mpf(p[9]))))
rows.sort(key=lambda x:x[1])  # ascending tau (shallow..deep)
C = mp.mpf(1891)*mp.sqrt(2)/10368            # known elementary leading
print(f"# {len(rows)} poles; leading C = 1891 sqrt2/10368")

# --- Neville/Richardson extrapolate s1 = lim (c2-C)/tau, watch the stable-digit plateau ---
def neville(xs, ys):
    n=len(ys); P=[mp.mpf(v) for v in ys]
    for k in range(1,n):
        for i in range(n-1,k-1,-1):
            P[i]=((-xs[i-k])*P[i]-(-xs[i])*P[i-1])/((-xs[i])-(-xs[i-k]))
    return P[n-1]
xs=[r[1] for r in rows]; g=[(r[2]-C)/r[1] for r in rows]
prev=None
for K in range(6, min(len(rows),28)+1, 2):
    v=neville(xs[:K], g[:K])
    agree = '' if prev is None else f"agree~{int(-mp.log10(abs(v-prev)+mp.mpf(10)**-115))}d"
    prev=v
print(f"# s1 = {mp.nstr(v,40)}  (stable to ~{agree})")
s1=v
S1=[("s1",s1),("s1*4sqrt2",s1*4*mp.sqrt(2)),("s1*1296",s1*1296),("s1*sqrt2",s1*mp.sqrt(2))]

# --- the EXOTIC transcendental basis (plausible for a q-Bessel/q-Airy turning-point connection) ---
g13=mp.gamma(mp.mpf(1)/3); g23=mp.gamma(mp.mpf(2)/3); g16=mp.gamma(mp.mpf(1)/6)
B = {
 '1':mp.mpf(1), 'sqrt2':mp.sqrt(2), 'sqrt3':mp.sqrt(3), 'pi':mp.pi, 'pi^2':mp.pi**2,
 'log2':mp.log(2), 'log3':mp.log(3), 'zeta3':mp.zeta(3), 'Catalan':mp.catalan,
 'gamma_E':mp.euler, 'logGlaisher':mp.log(mp.glaisher),
 'Gamma(1/3)^3':g13**3, 'Gamma(2/3)^3':g23**3, 'Gamma(1/6)^2':g16**2,
 'Ai(0)':mp.airyai(0), "Ai'(0)":mp.airyai(0,1),
 '3^(1/3)':mp.mpf(3)**(mp.mpf(1)/3), 'sqrt2 pi':mp.sqrt(2)*mp.pi, 'sqrt2 log2':mp.sqrt(2)*mp.log(2),
}
names=list(B); vals=[B[n] for n in names]

def trust_pslq(target, sub_names, maxc=10**4):
    sub=[B[n] for n in sub_names]
    r=mp.pslq([target]+sub, maxcoeff=maxc, maxsteps=2*10**5)
    if not r or r[0]==0: return None
    spend=sum(math.log10(abs(c)) for c in r if c!=0)
    rhs=" + ".join(f"({r[i+1]})*{sub_names[i]}" for i in range(len(sub_names)) if r[i+1]!=0)
    return (r, spend, rhs)

print("\n# === PSLQ search (trustworthy = spend << ~90 available digits) ===")
# 2- and 3-term subsets of the exotic basis (keeps height low => trustworthy)
hits=[]
for tname,tval in S1:
    for size in (1,2,3):
        for sub in itertools.combinations(names, size):
            res=trust_pslq(tval, list(sub))
            if res:
                r,spend,rhs=res
                if spend < 45 and abs(r[0])<10**5:   # trustworthy + meaningful
                    hits.append((tname, spend, r[0], rhs))
                    print(f"  {tname}: spend~{spend:.0f}d   {r[0]}*{tname} = {rhs}")
if not hits:
    print("  NO trustworthy relation found in exotic basis (2-3 term subsets).")
    print("  => s1 is not a low-complexity combination of these transcendentals.")
print("\n# (raise basis/maxc or send the CSV back for a deeper/wider sweep.)")
