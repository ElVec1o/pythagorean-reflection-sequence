import mpmath as mp
mp.mp.dps=90
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

# P11~w (large). It is the (1,0)-init top entry. The bulk numerator S0b~w sin w is the (1,0)... no.
# Test P11 vs S-blocks scaled. P11 is the partner of P21=-S0b in the SAME column. For an SL2 transfer
# product with a "numerator" column (P11,P21), maybe P11 = 1 + (bulk S1-type with shifted source).
# Try: P11 vs Sigma-blocks, vs derivative-type. Just probe a basis:
qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]
print("P11 vs candidate blocks (P11 is the large ~w entry):")
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
# even tower with q^{j^2}:
def Ea(q,J=400):
    p=1-q; return sum((-2*p)**j*q**(j*j)/qpoch(q,2*j) for j in range(J))
def Eb(q,J=400):  # 1 + sum...
    p=1-q; return sum((-2*p)**j*q**(j*j+j)/qpoch(q,2*j) for j in range(J))  # = Se
for q in qs:
    P12,P22,P11,P21=cocycle_full(q,int(70/(1-q)))
    print(f" q={float(q):.2f}: P11={float(P11):+.8f}  Ea(q^{{j^2}})={float(Ea(q)):+.8f}  S0b/Se*?  b0={float(P11):.4f}")

# Direct structural: P11=(1-P12*S0b)/Se from det. And t1=P12/Se=>P12=t1*Se. So P11=(1-t1*Se*S0b)/Se
# =1/Se - t1*S0b. Since b0=S0b/Se, P11=1/Se - t1*S0b. Check:
print("\nP11 = 1/Se - t1*S0b  (from det=1 & t1=P12/Se):")
for q in qs:
    N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle_full(q,N)
    Se=Se_clf(q); S0b=Sblk(0,q)
    cand=1/Se - t1*S0b
    print(f"  q={float(q):.2f}: P11={float(P11):+.9f}  1/Se-t1*S0b={float(cand):+.9f}  diff={float(abs(P11-cand)):.1e}")

# So everything reduces to: 1/Se (=> Se*w->1, R1b) and t1*S0b. t1~tau/4, S0b~w sin w => t1*S0b ~ (tau/4)w sin w
# ~ O(sqrt tau) -> 0. So P11 ~ 1/Se ~ w. P11*Se->1 automatically. This is CONSISTENT but circular for R2
# (uses t1). The independent content of R2 is genuinely P12*w/tau->1/4. Confirm it's NOT derivable from
# R1 alone: it needs the cocycle's own subleading. Print the cleanest reduced statement set.
print("\nCONCLUSION: R2's independent content = P12*w/tau->1/4 (cocycle off-diag subleading).")
print("This is a lem:cos-CLASS extreme-phase amplitude (P12 carries sign sin w_m, |P12|*w/tau->1/4),")
print("but P12 has NO single proven closed block (unlike Se=1-S1b, So=(p/2q)S0b, P21=-S0b).")
