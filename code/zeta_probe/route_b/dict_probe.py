import mpmath as mp
mp.mp.dps=40

# ---------- exact Se, So (q-Pochhammer sums) ----------
def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So

# ---------- exact cocycle P12=Y, P22=y ----------
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  #P12,P22,P11,P21

# ---------- travel blocks Sigma_0, Sigma_1 ----------
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot
# ---------- bulk blocks S_0, S_1 ----------
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*120)
print("DICTIONARY PROBE: Se, So, P12 vs travel(Sig0,Sig1) and bulk(S0,S1) blocks")
print("="*120)
print(f"{'q':>10} {'Se':>13} {'So':>13} {'P12':>13} | {'Sig1':>12} {'1-Sig1':>12} {'Sig0':>12} {'S1':>12} {'S0':>12}")
for qf in ['0.85','0.9','0.93','0.97','0.99']:
    q=mp.mpf(qf); N=int(50/(1-q)); p=1-q; J=int(70/(1-q))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    s1=Sig(1,q);s0=Sig(0,q);b1=Sb(1,q);b0=Sb(0,q)
    print(f"{qf:>10} {float(Se):>13.7f} {float(So):>13.7f} {float(P12):>13.7f} | {float(s1):>12.7f} {float(1-s1):>12.7f} {float(s0):>12.7f} {float(b1):>12.7f} {float(b0):>12.7f}")

print()
print("Try candidate identities (ratios should be constant if proportional):")
print(f"{'q':>10} {'Se/(1-Sig1)':>13} {'Se/(1-S1)':>13} {'So/Sig0':>12} {'So/S0':>12} {'P12/Sig0':>12} {'P12/S0':>12} {'So*w':>12}")
for qf in ['0.9','0.95','0.99','0.997']:
    q=mp.mpf(qf); N=int(60/(1-q)); p=1-q; J=int(90/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    s1=Sig(1,q);s0=Sig(0,q);b1=Sb(1,q);b0=Sb(0,q)
    def sf(x):
        try: return f"{float(x):>12.6f}"
        except: return f"{'inf':>12}"
    print(f"{qf:>10} {sf(Se/(1-s1)):>13} {sf(Se/(1-b1)):>13} {sf(So/s0)} {sf(So/b0)} {sf(P12/s0)} {sf(P12/b0)} {sf(So*w)}")
