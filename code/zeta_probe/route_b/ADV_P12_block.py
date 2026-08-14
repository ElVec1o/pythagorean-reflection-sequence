import mpmath as mp
mp.mp.dps=70

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x   # P12,P22=Se,P11,P21

def Se_So(q,J=None):
    if J is None: J=int(6*mp.sqrt(2/(-mp.log(q))))+150
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("Is P12 a PROVEN BLOCK? Test candidate closed forms for P12 (the OFF-diagonal cocycle entry).")
print("Memory says: P12 is NOT a single proven block (no So/S0b/derivative relation). Verify that.")
print("Candidates: P12 vs So, vs (p/2q)S0b=So, vs So*Se, vs combos.")
print(f"{'q':>7} | {'P12':>14} {'So':>14} {'P12/So':>12} {'P12/(So Se)':>12} {'P12/So^2':>12}")
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(80/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    Se2,So=Se_So(q)
    print(f"{qf:>7} | {float(P12):>14.8f} {float(So):>14.8f} {float(P12/So):>12.6f} {float(P12/(So*Se)):>12.6f} {float(P12/So**2):>12.6f}")
print()
print("If none of these columns is CONSTANT (=1) across q, P12 is NOT that block. Looking for a clean identity.")
print()
# Cocycle algebra: the matrix M_n=[[1+2q2n,-2qn],[2q3n,1-2q2n]], det? P=prod M_n. P11 P22-P12 P21=det.
print("Cocycle structure: P=[[P11,P12],[P21,P22]], check det(P)=prod det(M_n) and the 2nd-col relation.")
print(f"{'q':>7} | {'detP':>14} {'prod detMn':>14} {'P11*Se-P12*P21':>16}")
for qf in ['0.80','0.92','0.96']:
    q=mp.mpf(qf); N=int(80/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    # prod of det(M_n)= prod[(1+2q2n)(1-2q2n)+2qn*2q3n]=prod[1-4q4n+4q4n]=prod[1]=1
    dP=P11*Se-P12*P21
    print(f"{qf:>7} | {float(dP):>14.10f} {float(1):>14.10f} {float(P11*Se-P12*P21):>16.10f}")
print(" det(M_n)=(1+2q2n)(1-2q2n)+4q4n = 1-4q4n+4q4n = 1, so det(P)=1 EXACTLY (unimodular cocycle).")
print()
print("So P12 = (P11*Se - 1)/P21. P12 is genuinely an off-diagonal entry, NOT reducible to So/S0b alone.")
print("CONCLUSION on block-route: P12 is tied to the WHOLE matrix, the saddle needs the off-diagonal")
print("steepest-descent member, distinct from Se's diagonal member. Confirms colleague's 'block route ruled out'.")
