import mpmath as mp
mp.mp.dps=40
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y
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
print("Verify VoP structure: does normalized Bessel approx capture P12 to O(tau^2) (beating E's O(tau))?")
print(f"{'m':>2}{'tau':>9}{'N_emp=Y3/J32(W)':>17}{'(P12_B/P12-1)/tau^2':>20}{'(P12/E-1)/tau':>15}")
Nprev=None
for m in [2,4,6,8,10,14,20]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    N=int((mp.mp.dps+15)*2.3026/tau)+60
    P12,Se=cocycle(q,N)
    Y3=P12*(1-q**3)/(2*q**3)
    J32=mp.besselj(mp.mpf(3)/2,W)           # x=1
    Nemp=Y3/J32
    print(f"{m:>2}{float(tau):>9.5f}{mp.nstr(Nemp,12):>17}",end="")
    # use a fixed N (take from largest m as best estimate) - just check self-consistency via ratio to Y3
    # P12_B with N=Nemp would be exact; instead test if Nemp is CONSTANT (->the normalization) and P12_B with
    # the limiting N captures P12. Use N from this m's neighbor to avoid circularity: compare consecutive Nemp.
    E=mp.mpf('0.5')*(w-W)**2*mp.sin(w)*mp.sin(w-W)
    relE=(P12/E-1)/tau
    # P12_B using a GUESS N0 (limit). We'll infer N0 trend; here show Nemp and relE; P12_B accuracy needs fixed N0.
    print(f"{'':>20}{float(relE):>15.5f}")
print("\nIf N_emp -> a constant (the confluence normalization) and that's the only free param, then")
print("P12 = (2q^3/(1-q^3)) N0 J32(W)(1+O(tau^2)) and R=P12-E reduces to the ELEMENTARY [N0 J32(W)*(2q^3/(1-q^3)) - E].")
print("\nNow test with N0 = lim N_emp (Richardson from the two largest m): does P12_B beat E?")
# get N0 by extrapolating Nemp (fit N_emp = N0 + a tau)
ms=[20,30,40]; data=[]
for m in ms:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    Nn=int((mp.mp.dps+15)*2.3026/tau)+60;P12,Se=cocycle(q,Nn);Y3=P12*(1-q**3)/(2*q**3)
    data.append((tau,Y3/mp.besselj(mp.mpf(3)/2,W)))
# linear fit N_emp=N0+a tau using first two
(t0,n0),(t1,n1)=data[0],data[1]
a=(n1-n0)/(t1-t0); N0=n0-a*t0
print(f"  extrapolated N0={mp.nstr(N0,12)}  (a={mp.nstr(a,6)});  3/sqrt2={mp.nstr(3/mp.sqrt(2),10)}  36/35={mp.nstr(mp.mpf(36)/35,10)}")
for m in [2,4,6,8,10,14]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    Nn=int((mp.mp.dps+15)*2.3026/tau)+60;P12,Se=cocycle(q,Nn)
    J32=mp.besselj(mp.mpf(3)/2,W)
    P12_B=(2*q**3/(1-q**3))*N0*J32
    E=mp.mpf('0.5')*(w-W)**2*mp.sin(w)*mp.sin(w-W)
    print(f"  m={m:>2} tau={float(tau):.5f}: (P12_B/P12-1)/tau^2={float((P12_B/P12-1)/tau**2):>10.4f}   (P12/E-1)/tau={float((P12/E-1)/tau):>9.4f}")
