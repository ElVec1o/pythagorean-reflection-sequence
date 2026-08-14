import mpmath as mp
mp.mp.dps=60
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  #P12,P22,P11,P21

def block(q):
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se=Se_clf(q); So=So_clf(q); S0b=Sblk(0,q); S1b=Sblk(1,q); Sig0=Sigma(0,q); Sig1=Sigma(1,q)
    P12,P22,P11,P21=cocycle(q,N)
    return dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,Se=Se,So=So,S0b=S0b,S1b=S1b,
                Sig0=Sig0,Sig1=Sig1,P12=P12,P22=P22,P11=P11,P21=P21,p=1-q)

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95'),mp.mpf('0.97')]
print("All cocycle entries + blocks. Note P22=Se confirmed earlier.")
print(f"{'q':>7} {'P11':>11} {'P12':>11} {'P21':>11} {'P22=Se':>11} | {'S0b':>10} {'S1b':>10} {'So':>10}")
for q in qs:
    d=block(q)
    print(f"{float(q):>7.3f} {float(d['P11']):>11.6f} {float(d['P12']):>11.6f} {float(d['P21']):>11.6f} {float(d['P22']):>11.6f} | {float(d['S0b']):>10.5f} {float(d['S1b']):>10.5f} {float(d['So']):>10.5f}")

# t1=P12/Se. R2: t1/tau->1/4, i.e. s=(q/p)t1->1/4 => P12/(p Se)... (q/p)*tau->1 so t1~tau/4 => P12~Se*tau/4.
# Search P12 in terms of blocks. P12=t1*Se. Try P12 = (1/2)*(So - something), or det relation.
# Cocycle determinant: det = P11 P22 - P12 P21. For these transfer matrices det = prod(1+2q2n)(1-2q2n)+...
print("\ndet P = P11*P22-P12*P21:")
for q in qs:
    d=block(q)
    det=d['P11']*d['P22']-d['P12']*d['P21']
    print(f"  q={float(q):.3f}: det={float(det):+.10f}")

# Candidate R2 forms for P12:
print("\nP12 candidates (want exact):")
for q in qs:
    d=block(q); p=d['p']; q_=d['q']
    print(f"  q={float(q_):.3f}: P12={float(d['P12']):+.9f}  So/2={float(d['So']/2):+.9f}  "
          f"(p/2q)*P11={float((p/(2*q_))*d['P11']):+.9f}  P11={float(d['P11']):+.7f}")
