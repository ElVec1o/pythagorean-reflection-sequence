import mpmath as mp, pickle, numpy as np
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=45
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
def pade_roots(L,M):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    return sorted(np.roots([complex(x) for x in q][::-1]),key=abs)
tot=Nrel-1; L=tot//2; M=tot-L
r=pade_roots(L,M)
print(f"ALL Pade [{L}/{M}] poles (order {tot}), sorted by |z|:")
print("  if first conj pair = the cut, others should be SCATTERED (single cut + noise),")
print("  or form an arithmetic/geometric FAMILY (accumulation).")
for z in r:
    print(f"   |z|={abs(z):7.4f}  arg={np.degrees(np.angle(z)):+8.2f}  z={z.real:+.3f}{z.imag:+.3f}i")
# accumulation family candidate: travel-pole images t_m ~ |A|*(m/(m-?))? or t_m=|A_1|*m?
print("\n  ratios |z_{k+1}|/|z_k| (geometric family => constant; arithmetic => ->1):")
mods=sorted(set(round(abs(z),3) for z in r))
for i in range(1,len(mods)):
    print(f"    {mods[i]}/{mods[i-1]} = {mods[i]/mods[i-1]:.3f}")
