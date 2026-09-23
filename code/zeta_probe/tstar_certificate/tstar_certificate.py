import mpmath as mp
from mpmath import iv
iv.dps=30; mp.mp.dps=30
DEL=iv.mpf('0.25')  # target delta
def rho_parts(q):  # works for mp or iv q
    M = iv if isinstance(q, type(iv.mpf(1))) else mp
    one=M.mpf(1)
    c=q*M.sqrt((one-q)/2)
    db=(one-q)*c/(one-c)
    R=M.exp(c/((one-c)*(one-db)))*(one+c)/(q*(one-c))
    K=30; S=M.mpf(0); qs=one
    for k in range(1,K+1):
        qs=qs*q; S+=qs/(R-(R-one)*qs)
    qK=qs*q
    Phi1=2*(S+M.log(R/(R-(R-one)*qK))/((R-one)*M.log(one/q)))
    RHS=(2*q-one)/(one-q)
    return Phi1,RHS
# point check + min ratio
mn=(9,None)
for i in range(1,20000):
    q=mp.mpf(0.5)+mp.mpf(i)/40000
    P,R=rho_parts(q)
    if R>0 and P/R<mn[0]: mn=(P/R,q)
print('min ratio on grid',mn)
# interval certification of Phi1 - (iv.mpf(1)+DEL)RHS > 0 on [1/2, 1-1e-6]
lo=mp.mpf(0.5); bad=0; n=0
def ok(a,b):
    Q=iv.mpf([a,b]); P,R=rho_parts(Q)
    return (P - (iv.mpf(1)+DEL)*R).a > 0
stack=[]
edges=[mp.mpf(0.5)]
# geometric mesh toward 1
x=mp.mpf(0.5)
while x<1-mp.mpf('1e-6'):
    h=min(mp.mpf('0.002'),(1-x)/50)
    stack.append((x,x+h)); x+=h
fail=[]
for a,b in stack:
    if not ok(a,b):
        # bisect a few times
        sub=[(a,b)];good=True
        for _ in range(8):
            nxt=[]
            for (c,d) in sub:
                if not ok(c,d): m=(c+d)/2; nxt+=[(c,m),(m,d)]
            sub=nxt
            if not sub: break
        if sub: fail.append((a,b))
    n+=1
print('intervals',n,'failures',len(fail), fail[:3], 'last',x)
