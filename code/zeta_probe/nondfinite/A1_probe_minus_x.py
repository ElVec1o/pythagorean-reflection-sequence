from mpmath import mp, mpf, findroot, sqrt
mp.dps=90
def poch(q,n):
    p=mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def series(q,J=420):
    g=mpf(0); Se=mpf(0); Y=mpf(0)
    p2=mpf(1) # (q;q)_{2j}
    a=mpf(1); b=mpf(1) # (q^2;q^2)_k, (q^5;q^2)_k
    for j in range(J):
        if j>0:
            p2*=(1-q**(2*j-1))*(1-q**(2*j))
            a*=(1-q**(2*j)); b*=(1-q**(2*j+3))
        g+=(-1)**j*2**j*q**(j*j)*(1-q)**j/p2
        Se+=(-2*(1-q))**j*q**(j*(j+1))/p2
        Y+=(-2)**j*(1-q)**j*q**(j*j+3*j)/(a*b)
    return g,Se,Y
guesses=[mpf('0.4494536306')]+[mpf(l.strip()) for l in open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/poles.txt').readlines()[:11]]
for m,g0 in enumerate(guesses,1):
    q=findroot(lambda t: series(t)[0], g0)
    g,Se,Y=series(q)
    P12=2*q**3/(1-q**3)*Y; t1=P12/Se; x=sqrt(q); tau=-mp.log(q)
    bVp=t1+(1+x)/(2*x); bVm=t1-(1-x)/(2*x); bUm=t1*(1+x+q)/(1+q)-1/(2*x)
    print(m, mp.nstr(q,15), 's=',mp.nstr(q/(1-q)*t1,8),'t1/tau=',mp.nstr(t1/tau,8),'bracketV(-x)/tau=',mp.nstr(bVm/tau,8),'bracketU(-x)=',mp.nstr(bUm,8))
