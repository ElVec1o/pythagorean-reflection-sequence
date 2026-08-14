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

print("t1 vs candidate closed forms. t1=P12/Se.")
print(f"{'q':>8} {'t1':>16} {'tau/4':>14} {'p/4':>14} {'(1-q)/(2(1+q))':>16}")
for qf in ['0.7','0.85','0.9','0.95','0.99','0.997','0.999']:
    q=mp.mpf(qf); N=int(120/(1-q)); p=1-q; J=int(160/(1-q)); tau=-mp.log(q)
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    t1=P12/Se
    print(f"{qf:>8} {mp.nstr(t1,11):>16} {mp.nstr(tau/4,8):>14} {mp.nstr(p/4,8):>14} {mp.nstr(p/(2*(1+q)),9):>16}")

print()
print("Structure of P12: compare to So,S0,Se and shifts.")
print(f"{'q':>8} {'P12':>14} {'So':>14} {'P12+So':>14} {'P12/So':>12} {'P12/Se':>12}")
for qf in ['0.85','0.9','0.95','0.99']:
    q=mp.mpf(qf); N=int(120/(1-q)); p=1-q; J=int(160/(1-q))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    print(f"{qf:>8} {mp.nstr(P12,8):>14} {mp.nstr(So,8):>14} {mp.nstr(P12+So,7):>14} {mp.nstr(P12/So,7):>12} {mp.nstr(P12/Se,7):>12}")

# Maybe P12 = derivative w.r.t a parameter. The grading-1 cocycle weights q3n by q^? differently.
# Actually: in cocycle, source-0 col uses initial (x,y)=(0,1); source-1 uses (X,Y)=(1,0).
# So P12=Y comes from initial (1,0). This is a DIFFERENT solution of the SAME recursion.
# The two solutions: (x,y) and (X,Y) span the 2D solution space. Wronskian-like.
# t1=Y_N/y_N. Let me check the Wronskian W = x*Y - X*y is constant (product of det of each step).
print()
print("Cocycle Wronskian W_n = x*Y - X*y. det of step matrix = (1+2q2n)(1-2q2n)+4q3n*qn = 1-4q4n+4q4n=1")
print("So det=1 each step => W constant = W_0 = x0*Y0-X0*y0 = 0*0-1*1 = -1.")
print(f"{'q':>8} {'x*Y-X*y':>16}")
for qf in ['0.85','0.9','0.99']:
    q=mp.mpf(qf); N=int(120/(1-q))
    P12,P22,P11,P21=cocycle(q,N)  # Y,y,X,x
    Y,y,X,x=P12,P22,P11,P21
    print(f"{qf:>8} {mp.nstr(x*Y-X*y,12):>16}")
