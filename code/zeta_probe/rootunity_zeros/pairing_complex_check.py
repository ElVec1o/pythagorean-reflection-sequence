# pairing_complex_check.py -- direct check of the closed forms of thm:RJ at complex zeros q*_j (paper2a cor:Uminusone):
# <lambda^{(y)},R> from truncated operators vs (eq:RJclosed1),(eq:RJclosedq), both roots x=+-sqrt(q). Not a certificate.
# direct check of thm:RJ closed forms at complex zeros q*_j of 1-Sigma_1 (truncated operators)
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, sqrt, nstr, matrix, lu_solve, polylog
import sys
exec(open(__file__.replace('pairing_complex_check.py','t1_minusone.py')).read().split("phi=(1+sqrt(5))/2")[0])
L=log(4); Lp=lambda t: log(2*(1+exp(-t)))
x0=log(2+sqrt(5))/2
for j in [int(v) for v in sys.argv[1:]]:
    mp.dps=45
    t=(L+1j*pi)/(2*j+1)
    for it in range(60): t=(Lp(t)+1j*pi)/(2*j+1)
    Phi0=x0*L-x0**2-polylog(2,exp(-4*x0))/4+pi**2/24
    t=findroot(lambda tt: sums(-exp(-tt))[0]*exp(-Phi0/tt), t)
    q=-exp(-t); N=int(70/(-log(abs(q))*2.3))+20
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
