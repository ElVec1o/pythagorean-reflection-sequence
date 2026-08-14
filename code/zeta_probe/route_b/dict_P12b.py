import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
exec(open('dict_P12.py').read().split('def block')[0])  # gets cocycle
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q); S0b=Sblk(0,q); S1b=Sblk(1,q); Sig0=Sigma(0,q); Sig1=Sigma(1,q)
    P12,P22,P11,P21=cocycle(q,N)
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,S0b=S0b,S1b=S1b,
                Sig0=Sig0,Sig1=Sig1,P12=P12,P22=P22,P11=P11,P21=P21,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]
print("[D] P21 ?= -S0b  and  P22=Se  =>  det: P11*Se + P12*S0b = 1")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: P21={float(d['P21']):+.9f} -S0b={float(-d['S0b']):+.9f} diff={float(abs(d['P21']+d['S0b'])):.1e} "
          f"| P11*Se+P12*S0b={float(d['P11']*d['Se']+d['P12']*d['S0b']):+.9f}")

# P11 is the remaining unknown. Is P11 a bulk block too? P11 relates to b1=S1b/Se. Check P11 vs S1b:
print("\n[E] P11 candidates: P11 ?= 1+S1b? , (1+S1b)/Se?, b1-related")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: P11={float(d['P11']):+.8f}  1+b1={float(1+d['b1']):+.8f}  "
          f"(1+S1b)/Se?={float((1+d['S1b'])/d['Se']):+.8f}  b1+? ")

# Recall t0=u0[0], t1=u1[0]. Maybe P11 ties to t0. Check P11 vs combos of t0,t1.
# Actually from t1=P12/Se we have P12=t1*Se. Let's instead DIRECTLY find P12's lem:cos asymptotic
# by relating it to So and S0b via the determinant + a second cocycle identity.
# Backward channel: t0,t1=u[0]. raw gives t0=b1 (=S1b/Se). Try P12 = (something)*Se + (something).
# Cleanest: just verify s=(q/p)t1 = (q/p)P12/Se and find P12's leading form at poles numerically.
print("\n[F] R2 at travel poles: t1, t1/tau, P12, P12/(Se*tau):")
print(f"{'m':>3} {'tau':>10} {'w':>9} {'t1/tau':>11} {'P12':>12} {'Se':>11} {'P12/Se=t1':>12}")
for m in [1,2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle(q,N)
    print(f"{m:>3} {float(tau):>10.6f} {float(w):>9.4f} {float(t1/tau):>11.7f} {float(P12):>12.7f} {float(P22):>11.7f} {float(P12/P22):>12.7f}")
