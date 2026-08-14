import mpmath as mp
mp.mp.dps=70

def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-170) and j>60: break
    return tot

# So is the "odd" analogue of Se=1-S1blk. Bulk S0blk is the bulk NUMERATOR.
# Guess: So = c * S0blk for some elementary c(q)?  ratio So/S0blk:
print("ratio So/S0blk and So/(q*S0blk) etc — look for elementary multiplier:")
print(f"{'q':>7} {'So/S0blk':>16} {'*(1-q)':>14} {'So/S0blk/(1-q)':>16} {'So*(1-q)/(q*S0blk)':>18}")
for qf in ['0.8','0.85','0.9','0.93','0.95','0.97','0.99','0.995']:
    q=mp.mpf(qf); J=int(95/(1-q)); p=1-q
    Se,So=SeSo(q,J); sb0=Sb(0,q)
    r=So/sb0
    print(f"{qf:>7} {mp.nstr(r,12):>16} {mp.nstr(r*p,9):>14} {mp.nstr(r/p,12):>16} {mp.nstr(So*p/(q*sb0),12):>18}")

print()
# Maybe So relates to S1blk-derivative or a SHIFTED bulk sum S_0 with offset.
# Recall Se=1-S1blk where S1blk=Sb(1). The odd partner of Sb(1) is Sb(0). Test So vs Sb(0) with
# the SAME structural transform that took Sb(1)->1-Sb(1)=Se. For Se: Se=1-Sb(1). For So maybe So = -Sb(0)*(1-q)/(2q)? check:
print("test So = -(1-q)/(2q) * S0blk  ?  and other rational multiples:")
print(f"{'q':>7} {'So':>16} {'-(p/2q)S0blk':>16} {'diff':>12} {'(2q/p)So/S0blk':>16}")
for qf in ['0.8','0.85','0.9','0.93','0.95','0.97','0.99']:
    q=mp.mpf(qf); J=int(95/(1-q)); p=1-q
    Se,So=SeSo(q,J); sb0=Sb(0,q)
    cand=-(p/(2*q))*sb0
    print(f"{qf:>7} {mp.nstr(So,11):>16} {mp.nstr(cand,11):>16} {mp.nstr(So-cand,4):>12} {mp.nstr((2*q/p)*So/sb0,11):>16}")
