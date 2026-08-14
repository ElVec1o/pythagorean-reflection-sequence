import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

# P21=-S0b => S0b=-P21. Define bulk blocks with index-shifted sources to catch P11,P12.
# The bulk S-blocks: S0b uses alpha(k)=2q^{k+1}/(1-q^{k+1}); S1b is the Sigma_1-bulk.
# P11 is the (1,0)-init TOP entry; P12 the (0,1)-init TOP entry. By the SL2 structure & the proven
# P21=-S0b, P22=Se, the natural lem:cos identities are:
#   P11 = ??? ;  P12 = ???  with P11*Se+P12*S0b=1.
# Test whether P11 and P12 individually are S-blocks with sources shifted by the cocycle's first step
# (init (1,0) vs (0,1) just changes which Lambert tower). Concretely try:
#   P12 ?= (p/(2q)) * (1 - S1b_shift)   or   P12 ?= So * f
# Empirically pin P12's lem:cos amplitude: P12*w/tau -> 1/4 with sign sin w.  And So=(p/2q)S0b,
# S0b~w sin w => So ~ (tau/2) sin w (since p~tau, w*... ). Check So*w/tau and compare to P12*w/tau:
print("Compare So and P12 leading forms (both ~ sin w amplitude):")
print(f"{'m':>3} {'So':>13} {'So*w/tau':>11} {'P12*w/tau':>11} {'P12/So':>10} {'Se*w':>10}")
for m in [1,2,4,8,16,32]:
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    P12,P22,P11,P21=cocycle_full(q,N)
    So=So_clf(q)
    print(f"{m:>3} {float(So):>13.8f} {float(So*w/tau):>11.7f} {float(P12*w/tau):>11.7f} {float(P12/So):>10.6f} {float(P22*w):>10.6f}")

# Also: t1/tau = P12/(Se tau). And t0=b1=S1b/Se. The resolvent (I-M)^{-1} structure gives the
# OFF-DIAGONAL element. Let me check the cleanest closed identity for s:
# s=(q/p)t1. Numerically s=1/4+tau/16. Is there s = (1/4)(1-S1b-correction)?... Let me see if
# s relates to So/Se and Se via a clean SL2 formula: s=(q/p)P12/Se, and P11 Se+P12 S0b=1 =>
# P12=(1-P11 Se)/S0b. Hmm needs P11.
# Final: confirm the SIGN structure (the heart of why ratio->1/4 not 0/inf): Se*w and P12*w/tau share sign.
print("\nSign structure (extreme phase: both carry sin w_m = (-1)^{m+1}):")
for m in range(1,13):
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    P12,P22,P11,P21=cocycle_full(q,N)
    sw=mp.sin(w)
    print(f"  m={m:>2}: sin w={float(sw):+.4f}  sign(Se*w)={int(mp.sign(P22*w))}  sign(P12)={int(mp.sign(P12))}  t1/tau=(P12*w/tau)/(Se*w)={float((P12*w/tau)/(P22*w)):.7f}")
