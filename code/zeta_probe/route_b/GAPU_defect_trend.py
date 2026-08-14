"""
GAP-U honesty check: do the relative defect coefficients
   d11 = (P11/(w sin w) - 1)/tau ,   dSe = (Se*w/sin w - 1)/tau
stay BOUNDED < 1/6 as m->infty (gate holds asymptotically), or do they GROW (like the V-side
absolute bound degraded sqrt(tau)->tau^1/4)?  The gate needs max(|d11|,|dSe|) < 1/6.
STEP A: verify P11 = S0bulk(=Sblk(0,q)) and Se = 1-S1bulk(=Sblk(1,q)) via the cocycle at small m (fast forms).
STEP B: sweep m=1..80 with the FAST Sblk forms; report d11,dSe,max and the trend (converge vs grow).
Scalar mpmath. dps scales with w.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12,Se,P11,P21
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2))-2*q**(k+1)/(1-q**(k+1))
def Sblk(k,q,J=200000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+10)) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("STEP A: cocycle P11,Se  vs  fast S0b=Sblk(0), 1-S1b=Sblk(1)  (confirm fast forms):")
print(f"{'m':>3}{'P11(coc)':>16}{'S0b(fast)':>16}{'rel':>9} | {'Se(coc)':>14}{'1-S1b':>14}{'rel':>9}")
for m in [1,2,4,8]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(1.2*float(w)); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N); S0b=Sblk(0,q); S1b=Sblk(1,q)
    r1=abs(P11-S0b)/(abs(P11)+1); r2=abs(Se-(1-S1b))/(abs(Se)+1)
    print(f"{m:>3}{float(P11):>16.6f}{float(S0b):>16.6f}{float(r1):>9.1e} | {float(Se):>14.8f}{float(1-S1b):>14.8f}{float(r2):>9.1e}")
    mp.mp.dps=30

print("\nSTEP B: sweep m=1..80 with FAST forms; d11,dSe coefficients and gate max<1/6:")
print(f"{'m':>4}{'tau':>11}{'w':>9}{'cos w':>11}{'d11':>10}{'dSe':>10}{'max':>9}{'<1/6?':>7}")
maxall=mp.mpf(0); maxm=0; rows=[]
for m in range(1,81):
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(1.2*float(w))
    sw=mp.sin(w); S0b=Sblk(0,q); S1b=Sblk(1,q); Se=1-S1b
    d11=(S0b/(w*sw)-1)/tau; dSe=(Se*w/sw-1)/tau
    k=max(abs(d11),abs(dSe))
    if k>maxall: maxall=k; maxm=m
    rows.append((m,float(tau),float(d11),float(dSe),float(k)))
    if m<=12 or m%8==0 or m>=78:
        print(f"{m:>4}{float(tau):>11.6f}{float(w):>9.3f}{float(mp.cos(w)):>11.6f}{float(d11):>10.5f}{float(dSe):>10.5f}{float(k):>9.5f}{str(k<mp.mpf(1)/6):>7}")
    mp.mp.dps=30
print(f"\nMAX over m=1..80: {float(maxall):.6f} at m={maxm}   gate 1/6=0.16667   PASS={maxall<mp.mpf(1)/6}")
# trend: last 20 vs first 20
import statistics
last=[r[4] for r in rows[-20:]]; first=[r[4] for r in rows[:20]]
print(f"mean max(d11,dSe): first20={statistics.mean(first):.5f}  last20={statistics.mean(last):.5f}  (flat=>bounded, rising=>danger)")
print(f"d11 last5: {[round(r[2],5) for r in rows[-5:]]}")
print(f"dSe last5: {[round(r[3],5) for r in rows[-5:]]}")
