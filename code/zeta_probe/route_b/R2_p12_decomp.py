import mpmath as mp
# Goal: show P12 = (elementary E) + (saddle remainder R), where E ~ (1/2)(w-W)^2 sinw sin(w-W)
# and R is O(tau^2) (subleading to E~tau^{3/2}). Then t1=P12/Se with Se=E_S+R_S,
# E_S=sinw sin(w-W) (~sqrt(tau)), R_S=O(tau) [lem:cos]. 
# t1 = (E+R)/(E_S+R_S). Leading: E/E_S = (1/2)(w-W)^2 (EXACT ratio of elementary parts!) -> tau/4.
# The corrections R/E_S and (E/E_S)(R_S/E_S) are controlled by lem:cos bound (R,R_S=o(leading)).
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
# Define E = (1/2)(w-W)^2 sinw sin(w-W), R=P12-E. E_S=sinw sin(w-W), R_S=Se-E_S.
# Show R/tau^2 bounded and R_S/tau bounded (lem:cos), and the FULL ratio decomposition:
print(f"{'m':>3} {'tau':>9} {'R=P12-E':>13} {'R/tau^2':>10} {'R_S=Se-E_S':>12} {'R_S/tau':>9} {'t1':>11} {'(1/2)(w-W)^2':>13}")
for m in [2,4,8,16,24,32,40,48]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(1.3*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(50/p)
    W=w*mp.e**(-tau/2)
    P12,P22,P11,P21=cocycle(q,N); Se=P22
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW
    ES=sw*swW
    R=P12-E; RS=Se-ES
    t1=P12/Se
    print(f"{m:>3} {float(tau):>9.5f} {float(R):>13.3e} {float(R/tau**2):>10.5f} {float(RS):>12.3e} {float(RS/tau):>9.5f} {float(t1):>11.7f} {float(mp.mpf(1)/2*(w-W)**2):>13.9f}",flush=True)
    mp.mp.dps=40
