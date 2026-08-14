import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

# y_n is the bulk dressing solution. Continuum: define t=q^n in (0,1]. 
# y_n should ~ scaled Bessel. The term 2q^{3n}/(y_n y_{n-1}).
# Since y_n -> Se (const) for large n, and q^{3n}->0, the SUM is dominated by SMALL n (boundary layer).
# But t1/tau->1/4 with tau->0, so the sum ~ tau/4 -> 0. Where does the sum mass sit?
i=8
q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
mp.mp.dps=50+int(2.0*float(w)); N=int(60/(1-q))
yh=cocyc_y(q,N)
qn=mp.mpf(1); terms=[]
for n in range(1,N+1):
    qn=qn*q; t=2*qn**3/(yh[n]*yh[n-1]); terms.append((n,float(qn),float(yh[n]),float(t)))
S=sum(t[3] for t in terms)
print(f"m={i} tau={float(tau):.5f} t1={S:.7f} t1/tau={S/float(tau):.6f}")
print("Term profile (where mass sits): n, q^n, y_n, term, cumfrac")
cum=0
for (n,qnv,ynv,tv) in terms:
    cum+=tv
    if n<=12 or n%50==0 or (cum/S>0.5 and cum/S-tv/S<=0.5):
        print(f"  n={n:>4} q^n={qnv:.5f} y_n={ynv:>9.5f} term={tv:>12.3e} cum/S={cum/S:.4f}")
