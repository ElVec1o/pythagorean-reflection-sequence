# pairing_check_i.py -- Room J, VERIFIED (floating point, not a certificate): closed forms of thm:RJ at the
# zeros of B near q=i (truncated operators), both roots x=+-sqrt(q); t1 from the operator vs -(1+S_-/S_e)/2.
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, sqrt, nstr, matrix, lu_solve
import sys
def ser(q,sh):
  s=mpc(0);poch=mpc(1);aa=-2*(1-q);k=0
  while True:
    if k>0: poch*=(1-q**(2*k-1))*(1-q**(2*k))
    term=aa**k*q**(k*k+sh*k)/poch; s+=term
    if k>10 and abs(term)<mpf(10)**(-mp.dps+5)*abs(s): return s
    k+=1
for j in [int(v) for v in sys.argv[1:]]:
    mp.dps=60
    t=findroot(lambda tt: ser(1j*exp(-tt),0),(6*log(2)+1j*pi)/(16*j+6-2j))
    q=1j*exp(-t); N=int(70/(-log(abs(q))*2.3))+20
    t1ser=-(1+ser(q,-1)/ser(q,1))/2
    mp.dps=35
    # travel kernel vector: R_s = 2 q^{s+1} sum_{s'} q^{max(s,s')} R_{s'}, s>=0 ; normalise sum q^s R_s = 1
    A=matrix(N,N); b=matrix(N,1)
    for s in range(N):
        for sp in range(N):
            A[s,sp]=(1 if s==sp else 0)-2*q**(s+1)*q**max(s,sp)
    for sp in range(N): A[N-1,sp]=q**sp
    b[N-1]=1
    R=lu_solve(A,b)
    # residual of dropped equation
    res=abs(R[N-1]-2*q**N*sum(q**max(N-1,sp)*R[sp] for sp in range(N)))
    # bulk Psi_b, b=1..N : Psi_b = 2q^b (q^b + sum_{a>=1} q^{max(a,b)} Psi_a)
    Bm=matrix(N,N); bb=matrix(N,1)
    for bi in range(N):
        bq=bi+1
        for ai in range(N):
            Bm[bi,ai]=(1 if ai==bi else 0)-2*q**bq*q**max(ai+1,bq)
        bb[bi]=2*q**(2*bq)
    Psi=lu_solve(Bm,bb)
    t1=sum(q**(bi+1)*Psi[bi] for bi in range(N))
    print('j',j,'q*',nstr(q,10),'t1 operator',nstr(t1,12),' t1 series',nstr(t1ser,12),flush=True)
    for xx in (sqrt(q),-sqrt(q)):
        for name,y,gg in (('U',q,q/(1-q**2)),('V',1,q/(1-q))):
            B0=1/(1-gg*t1); B0z=1+y*(B0-1); P=[B0*Psi[bi] for bi in range(N)]
            lam=[]
            for s in range(N):
                mu=B0*xx**(2*s+1)+sum(P[bi]/2*(xx**max(2*(bi+1)-1,2*s+1)+xx**max(2*(bi+1)+1,2*s+1)) for bi in range(N))
                E=(B0z if s==0 else B0)*xx**(2*s)+B0*xx**(2*s+2)+sum(P[bi]*(xx**max(2*s,2*(bi+1))+xx**max(2*s+2,2*(bi+1))) for bi in range(N))
                lam.append(E+2*mu)
            pair=sum(lam[s]*R[s] for s in range(N))
            if name=='U': cf=2*q*B0*(1+xx)/(1-xx)*(t1*(1-xx+q)/(1+q)+1/(2*xx))
            else: cf=2*q*(1+xx)/(1-q)*(t1+(1+xx)/(2*xx))/(1-gg*t1)
            print('j',j,'q',nstr(q,8),'N',N,'x',nstr(xx,5),name,'<lam,R>=',nstr(pair,12),' closed=',nstr(cf,12),' rel',nstr(abs(pair-cf)/abs(cf),3),' eqres',nstr(res,2),flush=True)
