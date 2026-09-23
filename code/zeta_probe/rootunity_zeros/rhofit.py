from mpmath import mp, mpf, mpc, exp, log, pi, sqrt, nstr, findroot, matrix, lu_solve
mp.dps=50
src=open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/nondfinite/rootunity_check.py').read()
exec(src.split('guesses =')[0].replace("mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 110",""))
mp.dps=50
Lp=lambda t: log(2*(1+exp(-t)))
T=[];RU=[];RV=[]
for j in range(30,121,6):
    t=(log(4)+1j*pi)/(2*j+1)
    for it in range(80): t=(Lp(t)+1j*pi)/(2*j+1)
    q=-exp(-t)
    g,Se,Y,big=blocks(q,Jof(q)); x=sqrt(q); tt=-log(-q)
    t1=t1_Y3(q,Se,Y)
    bUp=t1*(1-x+q)/(1+q)+1/(2*x); bUm=t1*(1+x+q)/(1+q)-1/(2*x)
    bVp=t1+(1+x)/(2*x); bVm=t1-(1-x)/(2*x)
    T.append(tt); RU.append(((1-x)/(1+x))**4*(bUm/bUp)**2); RV.append(((1-x)/(1+x))**2*(bVm/bVp)**2)
    print(j, nstr(tt,8), 't1=',nstr(t1,10), '|g|/big=',nstr(abs(g)/big,3), flush=True)
def fit(R,deg):
    n=len(T); A=matrix(n,deg+1); b=matrix(n,1)
    for i in range(n):
        for k in range(deg+1): A[i,k]=T[i]**k
        b[i]=R[i]
    AH=A.H; c=lu_solve(AH*A,AH*b); return c
for name,R in (('U',RU),('V',RV)):
    for deg in (4,5,6):
        c=fit(R,deg); print(name,'deg',deg,' c0=',nstr(c[0],10),' c1=',nstr(c[1],10),' c2=',nstr(c[2],8))
