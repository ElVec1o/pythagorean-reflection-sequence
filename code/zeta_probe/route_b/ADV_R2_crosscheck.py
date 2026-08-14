"""
INDEPENDENT cross-check of the R2 refinement (1/(4sqrt2) is ELEMENTARY, not a saddle constant).

Different code path from ADV_*: P12 and Se computed via the SCALAR 3-term recursion
  y_{n+1} = (1+q^3 - 2(1-q) q^{2n+2}) y_n - q^3 y_{n-1},   n>=1
  Se : (y0,y1)=(1, 1-2q^2)        P12: (y0,y1)=(0, 2q^3)
cross-validated against the matrix cocycle M_n=[[1+2q^2n,-2q^n],[2q^3n,1-2q^2n]].

Claims tested (must ALL hold for the refinement):
 (a) scalar-rec P12,Se == matrix-cocycle P12,Se   (recursion calibrated correctly)
 (b) E/tau^1.5 -> 1/(4sqrt2)  with E=(1/2)(w-W)^2 sinw sin(w-W), W=w e^{-tau/2}  [ELEMENTARY]
 (c) R=P12-E STRICTLY subleading: R/tau^1.5 -> 0  (=> E captures the FULL tau^1.5 leading order)
 (d) decay rate of R: R/(tau^2 sinw) bounded => R=O(tau^2)  (sharper than o(tau^1.5))
 (e) t1=P12/Se -> tau/4   AND  the elementary E/E_S = (1/2)(w-W)^2 alone already -> tau/4
"""
import mpmath as mp

def matrix_cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y   # P12, P22=Se

def scalar_rec(q,N,y0,y1):
    q3=q*q*q
    ym1=y0; yc=y1
    for n in range(1,N):                       # produce y_{N} from y_1,y_0
        c=(1+q3-2*(1-q)*q**(2*n+2))
        ynext=c*yc-q3*ym1
        ym1,yc=yc,ynext
    return yc

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
print("m   tau        a=(w-W)/sqrt(t/2) b=.5(w-W)^2/(t/4) c=sin(wW)/(wW) | E/t^1.5  1/4sqrt2 | R/t^1.5   R/(t^2 sw) | t1/(t/4)  Eratio")
inv=1/(4*mp.sqrt(2))
maxabs_chk=mp.mpf(0)
for m in [2,4,8,12,16,20,24,28,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(1.2*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(55/(1-q))
    W=w*mp.e**(-tau/2); dwW=w-W; sw=mp.sin(w); swW=mp.sin(dwW)
    # (a) two independent computations of P12, Se
    P12m,Sem=matrix_cocycle(q,N)
    Se_s=scalar_rec(q,N,mp.mpf(1),1-2*q*q)
    P12_s=scalar_rec(q,N,mp.mpf(0),2*q*q*q)
    chk=max(abs(P12m-P12_s)/abs(P12m), abs(Sem-Se_s)/abs(Sem))
    maxabs_chk=max(maxabs_chk,chk)
    P12,Se=P12_s,Se_s                          # USE the scalar-rec values
    t15=tau**mp.mpf('1.5')
    E=mp.mpf(1)/2*dwW**2*sw*swW
    R=P12-E
    a=dwW/mp.sqrt(tau/2); b=(mp.mpf(1)/2*dwW**2)/(tau/4); c=swW/dwW
    t1=P12/Se
    Eratio=(mp.mpf(1)/2*dwW**2)/(tau/4)        # the EXACT-elementary E/E_S over tau/4
    print(f"{m:>2} {float(tau):>9.2e}  {float(a):>14.10f} {float(b):>15.11f} {float(c):>13.9f} | {float(E/t15):>8.6f} {float(inv):>8.6f} | {float(R/t15):>9.2e} {float(R/(tau**2*sw)):>10.5f} | {float(t1/(tau/4)):>9.6f} {float(Eratio):>8.5f}",flush=True)
    mp.mp.dps=30
print()
print(f"(a) max rel.diff scalar-rec vs matrix-cocycle over all m: {float(maxabs_chk):.2e}  (must be ~1e-40, confirms same object)")
print(f"1/(4sqrt2) = {float(inv):.12f}   ;  (1/2)*(1/2)^1.5 = {float(mp.mpf(1)/2*(mp.mpf(1)/2)**mp.mpf('1.5')):.12f}  (algebraic identity)")
print("VERDICT: if a,b,c -> 1, E/t^1.5 -> 1/(4sqrt2), R/t^1.5 -> 0, R/(t^2 sw) bounded, t1/(t/4) -> 1:")
print("  => P12 leading amplitude 1/(4sqrt2) is ELEMENTARY (not a saddle const); R=O(tau^2) is the only residual.")
