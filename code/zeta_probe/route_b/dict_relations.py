import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*110)
print("TEST CANDIDATE EXACT RELATIONS (>=6 sig figs => identity)")
print("="*110)

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    Se=Se_clf(q); So=So_clf(q)
    Sig0=Sigma(0,q); Sig1=Sigma(1,q); S0b=Sblk(0,q); S1b=Sblk(1,q)
    P12=t1*Se
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,SUM=SUM,Se=Se,So=So,
                Sig0=Sig0,Sig1=Sig1,S0b=S0b,S1b=S1b,P12=P12,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]
print("\n[R-A]  Se ?= 1 - S_1^bulk")
for q in qs:
    d=block(q); print(f"  q={float(q):.3f}: Se={float(d['Se']):+.10f}  1-S1b={float(1-d['S1b']):+.10f}  diff={float(abs(d['Se']-(1-d['S1b']))):.1e}")

print("\n[R-B]  So ?= simple combo of S_0^bulk, Sigma_0 ...")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: So={float(d['So']):+.10f}  S0b={float(d['S0b']):+.10f}  Sig0={float(d['Sig0']):+.10f}  "
          f"-S0b*(1-q)?={float(-d['S0b']*(1-q)):+.8f}")

print("\n[R-C]  P12=t1*Se ?= combo ; t1 relations")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: P12={float(d['P12']):+.10f}  t1={float(d['t1']):+.8f}  S0b={float(d['S0b']):+.8f}  Sig0={float(d['Sig0']):+.8f}")
