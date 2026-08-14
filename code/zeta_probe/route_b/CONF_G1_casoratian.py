"""
G1: verify eq:qdiff exact recursion + Casoratian C_n=C0 q^{3n}; pin C0; set up the discrete Green's function.
Recursion (derived by eliminating x_n from M_n=[[1+2q^{2n},-2q^n],[2q^{3n},1-2q^{2n}]]):
   y_{n+1} = a_n y_n - q^3 y_{n-1},   a_n = 1+q^3-2(1-q)q^{2n+2}.
Two independent solutions y^{(1)} (from init [x,y]=[0,1]) and y^{(2)} (from [X,Y]=[1,0]); P12,Se are their N->inf limits.
Casoratian C_n = y^{(1)}_n y^{(2)}_{n+1} - y^{(1)}_{n+1} y^{(2)}_n  satisfies C_{n+1}=q^3 C_n => C_n = C_0 q^{3n}.
Discrete VoP: solution of u_{n+1}-a_n u_n+q^3 u_{n-1}=f_n is u_n = sum_m G(n,m) f_m,
   G(n,m) = (y^{(1)}_m y^{(2)}_n - y^{(1)}_n y^{(2)}_m)/C_m   (one-sided), C_m=C_0 q^{3m}.
"""
import mpmath as mp
mp.mp.dps = 40

def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=14):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def cocycle_seq(q,N):
    """Return the sequences y1_n (2nd comp, init [0,1]) and y2_n (2nd comp, init [1,0]), n=0..N."""
    # state vectors v=[a,b]; v_n = M_n...M_1 v_0; record 2nd component
    a1,b1=mp.mpf(0),mp.mpf(1)   # [x,y] init
    a2,b2=mp.mpf(1),mp.mpf(0)   # [X,Y] init
    y1=[b1]; y2=[b2]; qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        a1,b1=a1*(1+2*q2n)-2*b1*qn, 2*a1*q3n+b1*(1-2*q2n)
        a2,b2=a2*(1+2*q2n)-2*b2*qn, 2*a2*q3n+b2*(1-2*q2n)
        y1.append(b1); y2.append(b2)
    return y1,y2

m=6
q=refine(poles[m-1]); tau=-mp.log(q); w=mp.sqrt(2/tau)
N=40
y1,y2=cocycle_seq(q,N)
print(f"G1 verification at m={m}, tau={float(tau):.5f}, q={mp.nstr(q,10)}")
# (1) verify recursion y_{n+1}=a_n y_n - q^3 y_{n-1} on BOTH solutions
print("\n(1) recursion residual y_{n+1}-(a_n y_n - q^3 y_{n-1})  (a_n=1+q^3-2(1-q)q^{2n+2}):")
maxr=mp.mpf(0)
for n in range(1,N):
    an=1+q**3-2*(1-q)*q**(2*n+2)
    r1=y1[n+1]-(an*y1[n]-q**3*y1[n-1])
    r2=y2[n+1]-(an*y2[n]-q**3*y2[n-1])
    maxr=max(maxr,abs(r1),abs(r2))
print(f"    max |residual| over n=1..{N-1}, both solutions = {mp.nstr(maxr,4)}   (should be ~1e-{mp.mp.dps})")
# (2) Casoratian C_n = y1_n y2_{n+1} - y1_{n+1} y2_n ; check C_n/C_{n-1}=q^3 and C_n=C_0 q^{3n}
print("\n(2) Casoratian C_n = y1_n y2_{n+1} - y1_{n+1} y2_n  and ratio C_n/C_{n-1} (should = q^3):")
C=[y1[n]*y2[n+1]-y1[n+1]*y2[n] for n in range(N)]
C0=C[0]
print(f"    C_0 = {mp.nstr(C0,12)}")
for n in [1,5,10,20,30]:
    ratio=C[n]/C[n-1]
    closed=C0*q**(3*n)
    print(f"    n={n:>2}: C_n={mp.nstr(C[n],8)}  C_n/C_{{n-1}}={mp.nstr(ratio,12)}  C_n/(C0 q^{{3n}})={mp.nstr(C[n]/closed,12)}")
print(f"    q^3 = {mp.nstr(q**3,12)}")
# (3) identify C_0
print(f"\n(3) C_0 identification:  C_0={mp.nstr(C0,16)}")
for cand,name in [(mp.mpf(-2),'-2'),(-2*q,'-2q'),(mp.mpf(2),'2'),(2*q,'2q'),(mp.mpf(-1),'-1')]:
    print(f"      {name}={mp.nstr(cand,10)}  diff={mp.nstr(C0-cand,3)}")
print("\nGREEN'S FUNCTION now explicit: G(n,m)=(y1_m y2_n - y1_n y2_m)/(C_0 q^{3m}).")
print("=> G1 reduces VoP to summing G against the Bessel residual f_m=D[B]_m (G2). Casoratian decay q^{3m} is the key.")
