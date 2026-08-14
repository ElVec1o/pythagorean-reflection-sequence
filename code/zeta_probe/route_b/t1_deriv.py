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
def P12f(q):
    return cocycle(q, int(200/(1-q)))[0]
def Sef(q,J=None):
    if J is None: J=int(250/(1-q))
    return SeSo(q,J)[0]

# The second solution of a 2nd-order recursion is the "log-derivative partner".
# Test t1=P12/Se against d/dq related quantities of Se. Specifically the standard
# reduction-of-order: P12 = Se * sum (Wronskian / Se^2 step). Let's instead just test
# whether t1 equals a SIMPLE expression in So,Se and their q-derivatives.
print("Test t1 vs derivative combos of Se,So:")
print(f"{'q':>7} {'t1':>14} {'q*Se_q/Se':>14} {'-So/Se':>12} {'p*Se_q/(2 Se)':>14}")
h=mp.mpf('1e-25')
for qf in ['0.85','0.9','0.95','0.99']:
    q=mp.mpf(qf); p=1-q
    P12=P12f(q); Se=Sef(q)
    t1=P12/Se
    Sep=(Sef(q+h)-Sef(q-h))/(2*h)  # dSe/dq
    So=SeSo(q,int(250/p))[1]
    print(f"{qf:>7} {mp.nstr(t1,8):>14} {mp.nstr(q*Sep/Se,8):>14} {mp.nstr(-So/Se,7):>12} {mp.nstr(p*Sep/(2*Se),8):>14}")
