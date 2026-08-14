import mpmath as mp
mp.mp.dps=40
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
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot

print("Pin So/S0 exactly. Values: q=0.85->0.08823529, 0.9->0.05555556, 0.95->0.02631579, 0.99->0.005050505")
print("Note 0.0882352=3/34? 0.05555=1/18, 0.0263157=1/38, 0.00505=1/198. Denominators 34,18,38,198?")
print(f"{'q':>8} {'So/S0':>16} {'1/(So/S0)':>16} {'p*(1+q)/2?':>14} {'p/(2q)?':>14} {'p*(2-p)/2?':>12}")
for qf in ['0.85','0.9','0.95','0.99','0.997']:
    q=mp.mpf(qf); p=1-q; J=int(90/(1-q))
    Se,So=SeSo(q,J); b0=Sb(0,q)
    r=So/b0
    print(f"{qf:>8} {mp.nstr(r,11):>16} {mp.nstr(1/r,11):>16} {mp.nstr(p*(1+q)/2,8):>14} {mp.nstr(p/(2*q),8):>14} {mp.nstr(p*(2-p)/2,8):>12}")
# 1/(So/S0): q=0.9 ->18. p=0.1. 1/r=18 = 2*9 = 2/p^2? p^2=0.01, 2/p^2=200 no. 18=2(1+q)/p? =2*1.9/0.1=38 no.
# q=0.9: 1/r=18. q=0.99: 1/r=198. q=0.95:1/r=38. q=0.85:1/r=11.333.
# differences: 38-18=20 for dq=0.05; pattern 1/r ~ 2/p - 2? q=0.9: 2/0.1-2=18 YES. q=0.99:2/0.01-2=198 YES. q=0.95:2/0.05-2=38 YES. q=0.85:2/0.15-2=11.333 YES!
print()
print("HYPOTHESIS: 1/(So/S0) = 2/p - 2 = 2q/p  => So/S0 = p/(2q)  => So = S0*p/(2q) = S0*(1-q)/(2q)")
print(f"{'q':>8} {'So/S0':>18} {'p/(2q)':>18} {'diff':>12}")
for qf in ['0.85','0.9','0.95','0.99','0.997','0.85','0.7']:
    q=mp.mpf(qf); p=1-q; J=int(90/(1-q))
    Se,So=SeSo(q,J); b0=Sb(0,q)
    print(f"{qf:>8} {mp.nstr(So/b0,13):>18} {mp.nstr(p/(2*q),13):>18} {mp.nstr(So/b0-p/(2*q),5):>12}")
