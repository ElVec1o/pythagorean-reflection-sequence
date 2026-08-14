import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  # P12,P22,P11,P21

# P22=Se=1-S1b, P21=-S0b. By the SAME q-Pochhammer machinery (Se,So are j-sums), P11,P12 should be
# sibling q-series. Se=sum_j (-2p)^j q^{j(j+1)}/(q;q)_{2j};  So=sum_j (-2p)^j q^{j(j+2)} p/(q;q)_{2j+1}.
# S0b=(2q/p)So => P21=-S0b=-(2q/p)So. So the SECOND column (P12,P22) involves Se & ? ; FIRST (P11,P21)
# involves S0b & P11.
# GUESS the partner series. The two independent solutions of the cocycle: even/odd j Pochhammer towers.
# Define:
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_(q,J=400):
    p=1-q; return sum((-2*p)**j*q**(j*(j+1))/qpoch(q,2*j) for j in range(J))
def So_(q,J=400):
    p=1-q; return sum((-2*p)**j*q**(j*(j+2))*p/qpoch(q,2*j+1) for j in range(J))
# candidate P11 series (odd tower, the X-column complement): try the j-sum with q^{j(j-1)} / (q;q)_{2j} ...
def Pa(q,J=400):  # try shifted: q^{j^2}/(q;q)_{2j}
    p=1-q; return sum((-2*p)**j*q**(j*j)/qpoch(q,2*j) for j in range(J))
def Pb(q,J=400):  # q^{j(j+1)}/(q;q)_{2j+1} * 2q ...
    p=1-q; return sum((-2*p)**j*q**(j*(j+1))*2*q/qpoch(q,2*j+1) for j in range(1,J))

qs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]
print("Hunt P11,P12 q-series. P11~big, P12~small.")
for q in qs:
    P12,P22,P11,P21=cocycle_full(q,int(60/(1-q)))
    print(f" q={float(q):.2f}: P11={float(P11):+.7f} P12={float(P12):+.7f} | Pa={float(Pa(q)):+.7f} Pb={float(Pb(q)):+.7f} Se={float(Se_(q)):+.7f}")

# Different tack: P11,P12 obey the SAME 3-term recursion that generated Se,S0b. Instead of guessing
# the q-series, RELATE P11,P12 to S0b,Se via the SL2 + a SECOND known cocycle relation.
# We have det=1: P11 Se + P12 S0b = 1.  Need a 2nd eqn. The transfer matrix also satisfies a trace/
# transpose symmetry. Check P11 vs (something with S0b,Se). Try P11 = (1+? )/Se using a 2nd block.
# Actually: the column (P11,P21) is the cocycle applied to (1,0); (P12,P22) to (0,1). The b0/t-resolvent
# used these. Let me just confirm the REDUCED statements numerically hold (that's what matters for R2):
print("\nREDUCED R2 STATEMENTS (these are what R2 needs):")
print(" (i) Se*w -> 1  [= R1 fact2, lem:cos]   (ii) P12*w/tau -> 1/4   => t1/tau=(P12*w/tau)/(Se*w)->1/4")
for m in [4,8,16,32]:
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    P12,P22,P11,P21=cocycle_full(q,N)
    print(f"  m={m:>2}: Se*w={float(P22*w):.7f}  P12*w/tau={float(P12*w/tau):.7f}")
