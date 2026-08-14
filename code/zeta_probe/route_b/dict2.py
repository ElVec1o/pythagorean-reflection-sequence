import mpmath as mp
mp.mp.dps = 60
exec(open('dict_U_vs_lemcos.py').read().split('poles=')[0])
poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

print("="*130)
print("REFINED DICTIONARY  -- chasing exact relations")
print("="*130)
# Test families:
#  (a) Se ~ ? cos w / something ; So ~ ?  -> So/Se -> 1
#  (b) Sig0 ~ w sin w (theorem). Is Se*Sig0 a clean constant? Is Se*w^2 clean?
#  (c) P12 ~ ? ; t1/tau -> 1/4
rows=[]
for m in [1,2,3,4,6,8,12,16,24,32,48,64]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    Se,So=Se_So(q)
    Sig1=Sigma(1,q); Sig0=Sigma(0,q); S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    P12=t1*Se
    sinw=mp.sin(w); cosw=mp.cos(w)
    rows.append(dict(m=m,q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,SUM=SUM,Se=Se,So=So,P12=P12,
                     Sig1=Sig1,Sig0=Sig0,S1b=S1b,S0b=S0b,sinw=sinw,cosw=cosw))

print("\n[A] Se,So vs cos w and the bulk block. Test Se ?= (1-S1b)*?, and Se*w, So*w:")
print(f"{'m':>2} {'Se':>11} {'1-S1b':>10} {'Se/(1-S1b)':>11} {'Se*w':>10} {'cosw':>9} {'Se*Sig0':>11} {'So*Sig0':>11}")
for r in rows:
    print(f"{r['m']:>2} {float(r['Se']):>11.6f} {float(1-r['S1b']):>10.6f} {float(r['Se']/(1-r['S1b'])):>11.6f} {float(r['Se']*r['w']):>10.6f} {float(r['cosw']):>9.5f} {float(r['Se']*r['Sig0']):>11.7f} {float(r['So']*r['Sig0']):>11.7f}")

print("\n[B] Is Se*Sig0 -> -1 ? (i.e. Se ~ -1/Sig0 ~ -1/(w sin w)). And So*Sig0 -> -1 too (since So/Se->1).")
print(f"{'m':>2} {'Se*Sig0':>12} {'So*Sig0':>12} {'Se*S0b':>12} {'(Se*Sig0+1)/tau':>16}")
for r in rows:
    print(f"{r['m']:>2} {float(r['Se']*r['Sig0']):>12.8f} {float(r['So']*r['Sig0']):>12.8f} {float(r['Se']*r['S0b']):>12.8f} {float((r['Se']*r['Sig0']+1)/r['tau']):>16.6f}")

print("\n[C] t1 / P12 structure. t1=P12/Se. Test P12*w, P12*Sig0, t1*w^2, t1/tau:")
print(f"{'m':>2} {'t1':>11} {'t1*w*w':>11} {'4*t1/tau':>10} {'P12':>13} {'P12*Sig0':>12} {'P12*w':>12}")
for r in rows:
    print(f"{r['m']:>2} {float(r['t1']):>11.7f} {float(r['t1']*r['w']*r['w']):>11.6f} {float(4*r['t1']/r['tau']):>10.6f} {float(r['P12']):>13.8f} {float(r['P12']*r['Sig0']):>12.7f} {float(r['P12']*r['w']):>12.7f}")

print("\n[D] SUM structure. SUM->1/2. Test (SUM-1/2)/tau^2, SUM vs So/Se: b0=(2q/p)So/Se and b0=2q/p+2SUM => SUM=(q/p)(So/Se-1).")
print(f"{'m':>2} {'SUM':>11} {'(q/p)(So/Se-1)':>15} {'diff':>10} {'(SUM-.5)/tau':>13}")
for r in rows:
    q=r['q']; p=1-q
    pred=(q/p)*(r['So']/r['Se']-1)
    print(f"{r['m']:>2} {float(r['SUM']):>11.7f} {float(pred):>15.8f} {float(abs(r['SUM']-pred)):>10.1e} {float((r['SUM']-mp.mpf(1)/2)/r['tau']):>13.6f}")
