import mpmath as mp
mp.mp.dps=60

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
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=30000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
def A_(k,q): return 2*q/(1-q**(k+1))
def C_(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=30000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_(k+2*j,q)*prod; prod*=C_(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot

print("CANDIDATE EXACT IDENTITIES (off-pole, high precision):")
print(f"{'q':>7} {'Se':>14} {'1-S1blk':>14} {'Se-(1-S1blk)':>14}   {'So':>14} {'cand_So':>14} {'So-cand':>12}")
for qf in ['0.8','0.85','0.9','0.93','0.95','0.97','0.99']:
    q=mp.mpf(qf); N=int(60/(1-q)); J=int(95/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    Se,So=SeSo(q,J)
    sb1=Sb(1,q); sb0=Sb(0,q); s0=Sig(0,q); s1=Sig(1,q)
    cand_Se=1-sb1
    # guess So relation candidates -- test So vs S0blk/w, Sig0*Se/.., etc later; placeholder
    cand_So=mp.mpf(0)
    print(f"{qf:>7} {mp.nstr(Se,9):>14} {mp.nstr(cand_Se,9):>14} {mp.nstr(Se-cand_Se,4):>14}   {mp.nstr(So,9):>14} {mp.nstr(cand_So,9):>14} {mp.nstr(So-cand_So,4):>12}")

print()
print("So-relation hunt: print So and several blocks to find So's closed form:")
print(f"{'q':>7} {'w':>9} {'So':>14} {'S0blk':>14} {'S0blk/w':>12} {'Sig0':>14} {'(1-q)/(q)*?':>12}")
for qf in ['0.8','0.85','0.9','0.93','0.95','0.97','0.99']:
    q=mp.mpf(qf); J=int(95/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    Se,So=SeSo(q,J); sb0=Sb(0,q); s0=Sig(0,q)
    print(f"{qf:>7} {float(w):>9.3f} {mp.nstr(So,9):>14} {mp.nstr(sb0,9):>14} {mp.nstr(sb0/w,7):>12} {mp.nstr(s0,9):>14} {mp.nstr(So*w,7):>12}")
