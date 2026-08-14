import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q); S0b=Sblk(0,q); S1b=Sblk(1,q); Sig0=Sigma(0,q); Sig1=Sigma(1,q)
    return dict(q=q,tau=tau,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,S0b=S0b,S1b=S1b,Sig0=Sig0,Sig1=Sig1,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]
print("[A] b1*Se ?= S1b  (i.e. b1=S1b/Se=(1-Se)/Se):")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: b1*Se={float(d['b1']*d['Se']):+.10f}  S1b={float(d['S1b']):+.10f}  1-Se={float(1-d['Se']):+.10f}  diff={float(abs(d['b1']*d['Se']-d['S1b'])):.1e}")

# Now t1=P12/Se. t0=b1. Find P12=t1*Se. Try P12 = combinations of S0b,S1b,So,Se,Sig.
print("\n[B] P12=t1*Se, search:")
for q in qs:
    d=block(q); P12=d['t1']*d['Se']; p=d['p']; q_=d['q']
    print(f"  q={float(q_):.3f}: P12={float(P12):+.10f}  S0b={float(d['S0b']):.6f}  "
          f"(p/2q)*S1b={float((p/(2*q_))*d['S1b']):+.8f}  So*?")

# Hypothesis from pattern: source-q^b gave numerator S0b=(2q/p)So; source-q^{2b} l1 gave numerator
# b1*Se=S1b=1-Se. The t-channel (backward u[0]): t0=b1, and t1 likely = (p/2q)*(1-S1b-related).
# Try P12 = (p/(2q))*(1 - Se) = (p/2q)*S1b:
print("\n[C] P12 ?= (1-q)/(2q) * S1b   <=>   (2q/(1-q))*P12 = S1b = 1-Se:")
for q in qs:
    d=block(q); P12=d['t1']*d['Se']; p=d['p']; q_=d['q']
    cand=(p/(2*q_))*d['S1b']
    print(f"  q={float(q_):.3f}: P12={float(P12):+.10f}  (p/2q)S1b={float(cand):+.10f}  diff={float(abs(P12-cand)):.1e}")
