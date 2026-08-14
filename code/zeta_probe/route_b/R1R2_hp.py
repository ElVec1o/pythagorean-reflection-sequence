import mpmath as mp
# need J >~ w^2/2 ~ 1/tau terms and dps high enough to survive (2p)^j q^{j^2} cancellation
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

poles=[l.strip() for l in open('poles.txt') if l.strip()]

print(f"{'m':>3} {'w':>9} {'So/Se':>14} {'(So/Se-1)/tau':>14} {'t1/tau':>14} {'(t1/tau-1/4)/tau':>17}")
for i in [1,2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    mp.mp.dps=60
    q=mp.mpf(poles[i-1]); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    # set precision and J to survive q^{j^2}(2p)^j: peak term magnitude ~ exp(w^2/8)? use big dps
    mp.mp.dps=int(float(w))*2+80
    q=mp.mpf(poles[i-1]); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    J=int(float(w)**2/2)+200
    N=int(150/float(p))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    r=So/Se; t1=P12/Se
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(r,11):>14} {mp.nstr((r-1)/tau,8):>14} {mp.nstr(t1/tau,11):>14} {mp.nstr((t1/tau-mp.mpf(1)/4)/tau,8):>17}")
