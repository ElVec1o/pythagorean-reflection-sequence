import mpmath as mp, pickle, numpy as np
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
mp.mp.dps=45
Nrel=max(n for n in an if agree[n]>=10)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]
def pade_roots(L,M):
    p,q=mp.pade([b[i] for i in range(L+M+1)],L,M)
    return sorted(np.roots([complex(x) for x in q][::-1]),key=abs)
print("Track the 2 nearest conj-pairs across orders (genuine sing=stable; Stahl-cut=poles migrate):")
print(f"{'ord':>4} {'|A1|':>7} {'arg1':>7}   {'|A2|':>7} {'arg2':>7}")
for tot in range(10,Nrel):
    L=tot//2; M=tot-L
    if L+M>Nrel: break
    try:
        r=pade_roots(L,M)
        cand=[z for z in r if 30<abs(np.degrees(np.angle(z)))<150 and abs(z)<12]
        # take first two distinct |z|
        if len(cand)>=1:
            z1=cand[0]
            z2=next((z for z in cand if abs(abs(z)-abs(z1))>0.05), None)
            s=f"{tot:>4} {abs(z1):7.3f} {abs(np.degrees(np.angle(z1))):7.2f}"
            if z2 is not None: s+=f"   {abs(z2):7.3f} {abs(np.degrees(np.angle(z2))):7.2f}"
            print(s)
    except: pass
print("\nInterpretation: if |A1| stays ~5.5-5.7 & arg~60-63 across orders = stable dominant sing.")
print("If a 2nd stable sing exists at fixed |A2| => multiple actions. If |A2| migrates => cut/noise.")
