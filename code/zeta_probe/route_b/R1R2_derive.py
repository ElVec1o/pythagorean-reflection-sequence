import mpmath as mp
mp.mp.dps=50
def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*110)
print("(R1) via dictionary: So/Se = [S0*p/(2q)]/(1-S1).  At poles -> 1.")
print(" Using PROVEN asymptotics S0~w sin w, S1~1-cos w (BULK), and the bulk pole-structure.")
print("="*110)
# We don't recompute bulk via Lambert (unstable at high poles). Instead use the EXACT Pochhammer
# Se,So and verify So/Se->1, plus show what the asymptotic predicts.
# So/Se = So/Se. At a travel pole, 1-S1bulk = Se. We test So/Se directly and the asymptotic model:
#   So ~ (p/2q) * w sin w ;  Se = 1-S1bulk ~ cos w  (since S1~1-cos w => 1-S1~cos w)
#   => So/Se ~ (p/2q) w sin w / cos w = (p/2q) w tan w.
# But (p/2q) w = (1-q)/(2q) * sqrt(2/tau). With tau=-ln q ~ p for q->1, w~sqrt(2/p),
#   (p/2q)w ~ (p/2) sqrt(2/p) = sqrt(p/2)/sqrt(1)... ->0. So leading gives 0*tan w form.
# The point: at poles cos w_m is NOT ~0 here (Se = 1-S1bulk is O(1) like 0.07..0.21, NOT vanishing).
# Wait: travel pole is Sigma_1_TRAVEL=1, NOT S1_bulk=1. So at travel poles, S1_bulk is generic,
# Se=1-S1bulk is a generic O(1) number. So So/Se->1 is a statement about BULK blocks at the
# special TRAVEL-pole locations.
print(f"{'m':>3} {'w':>9} {'So/Se':>14} {'So':>14} {'Se':>14} {'So/Se-1':>12} {'(So/Se-1)/tau':>14}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); J=int(8*w)+150
    Se,So=SeSo(q,J)
    r=So/Se
    print(f"{i:>3} {float(w):>9.3f} {float(r):>14.9f} {float(So):>14.8f} {float(Se):>14.8f} {float(r-1):>12.2e} {float((r-1)/tau):>14.6f}")

print()
print("="*110)
print("(R2): t1/tau -> 1/4. t1=P12/Se. Check (t1/tau-1/4) and (t1/tau-1/4)/tau (rate).")
print("="*110)
print(f"{'m':>3} {'w':>9} {'t1':>16} {'t1/tau':>14} {'t1/tau-1/4':>14} {'(.)/tau':>12}")
for i in [1,2,4,8,16,24,32,40,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; N=int(120/(1-q)); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); J=int(8*w)+150
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    t1=P12/Se
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(t1,10):>16} {float(t1/tau):>14.9f} {float(t1/tau-mp.mpf(1)/4):>14.2e} {float((t1/tau-mp.mpf(1)/4)/tau):>12.5f}")
