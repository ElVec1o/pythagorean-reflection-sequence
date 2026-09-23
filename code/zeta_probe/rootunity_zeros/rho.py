# residue ratios rho_U, rho_V (formula eq:rhom, extended verbatim to complex zeros) at zeros q_j=-e^{-tau_j} near q=-1
import sys
from mpmath import mp, mpf, mpc, exp, log, pi, sqrt, nstr, findroot
mp.dps=60
src=open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/nondfinite/rootunity_check.py').read()
exec(src.split('guesses =')[0].replace("mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 110",""))
mp.dps=60
Lp=lambda t: log(2*(1+exp(-t)))
for j in range(4,31,2):
    t=(log(4)+1j*pi)/(2*j+1)
    for it in range(60): t=(Lp(t)+1j*pi)/(2*j+1)
    q=-exp(-t)
    q=findroot(lambda qq: blocks(qq,Jof(qq))[0], q)
    g,Se,Y,big=blocks(q,Jof(q))
    x=sqrt(q)
    t1=t1_Y3(q,Se,Y); t1b=t1_psi(q)
    bUp=t1*(1-x+q)/(1+q)+1/(2*x); bUm=t1*(1+x+q)/(1+q)-1/(2*x)
    bVp=t1+(1+x)/(2*x); bVm=t1-(1-x)/(2*x)
    rU=((1-x)/(1+x))**4*(bUm/bUp)**2; rV=((1-x)/(1+x))**2*(bVm/bVp)**2
    print(j,'x=',nstr(x,8),'t1=',nstr(t1,8),'t1chk=',nstr(abs(t1-t1b)/abs(t1),2),'|rhoU|=',nstr(abs(rU),10),'rhoU=',nstr(rU,8),'|rhoV|=',nstr(abs(rV),10),flush=True)
