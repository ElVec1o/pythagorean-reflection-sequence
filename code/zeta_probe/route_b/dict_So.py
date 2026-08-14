import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    Se=Se_clf(q); So=So_clf(q)
    Sig0=Sigma(0,q); Sig1=Sigma(1,q); S0b=Sblk(0,q); S1b=Sblk(1,q)
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,SUM=SUM,Se=Se,So=So,
                Sig0=Sig0,Sig1=Sig1,S0b=S0b,S1b=S1b,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]

# b0=(2q/p)So/Se and Se=1-S1b. Bulk resolvent G0b=S0b/(1-S1b)=S0b/Se.
# So compare b0 with bulk resolvent G0b = S0b/Se:
print("[1] b0 vs bulk resolvent S0b/Se, and (2q/p)So/Se identity check:")
for q in qs:
    d=block(q); p=d['p']
    G0b=d['S0b']/d['Se']
    print(f"  q={float(q):.3f}: b0={float(d['b0']):+.8f}  S0b/Se={float(G0b):+.8f}  "
          f"(2q/p)So/Se={float((2*q/p)*d['So']/d['Se']):+.8f}")

# => is (2q/p)*So == S0b ?  i.e. So = p/(2q) * S0b ?
print("\n[2]  So ?= (1-q)/(2q) * S0b   <=>   (2q/(1-q)) So = S0b")
for q in qs:
    d=block(q); p=d['p']
    print(f"  q={float(q):.3f}: So={float(d['So']):+.10f}  (p/(2q))S0b={float((p/(2*q))*d['S0b']):+.10f}  "
          f"diff={float(abs(d['So']-(p/(2*q))*d['S0b'])):.1e}")

print("\n[3] CONSEQUENCE if both: b0 = (2q/p)*So/Se = S0b/(1-S1b) = bulk resolvent G0b")
for q in qs:
    d=block(q)
    print(f"  q={float(q):.3f}: b0={float(d['b0']):+.10f}  G0b=S0b/(1-S1b)={float(d['S0b']/(1-d['S1b'])):+.10f}  "
          f"diff={float(abs(d['b0']-d['S0b']/(1-d['S1b']))):.1e}")
