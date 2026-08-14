"""
SCOPING the Hahn-Exton _0phi_1 confluence subleading (U's lone open input, B(a2)).
Decisive feasibility questions:
  Q1  Clean integral/saddle rep?           -> verify Y3(1)=sum d_k = (1-q^3)/(2q^3) P12, build continuous F(k).
  Q2  Simple nondegenerate saddle, or uniform/Airy?  -> solve complex saddle F'(k*)=-i*pi, check F''!=0, isolated.
  Q3  Does leading SP = E (elementary)?     -> compare |leading SP| to |E|; then is R=P12-E the SUBLEADING SP term?
  Q4  Standard Olver next-order, or obstruction (saddle collides with pole / extreme phase)?

d_k = (-2)^k (1-q)^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k]   (eq:0phi1; (-1)^k pulled out for the residue sum)
g(k):=|d_k| without sign = 2^k (1-q)^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k], extended to complex k via
   (a;q^2)_k = (a;q^2)_inf / (a q^{2k};q^2)_inf.
Alternating sum  Y3 = sum_k (-1)^k g(k) = sum_k e^{i pi k} g(k); n=0 Poisson term = int e^{i pi k+F(k)} dk,
   saddle Phi'(k*)=0 with Phi(k)=i pi k+F(k), F=log g.  COMPLEX saddle (the i pi tilts it off the real axis).
"""
import mpmath as mp
mp.mp.dps = 40
I = mp.mpc(0, 1)

def cocycle_P12(q, N):
    x=mp.mpf(0);y=mp.mpf(1);Y=mp.mpf(0);X=mp.mpf(1);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y   # P12, Se

def qpoch_inf(a,q2,terms=None):
    """(a;q2)_inf = prod_{j>=0}(1-a q2^j)."""
    if terms is None: terms=int((mp.mp.dps+10)*2.3026/abs(mp.log(abs(q2)+mp.mpf('1e-300'))))+40
    p=mp.mpf(1) if not isinstance(a,mp.mpc) else mp.mpc(1); aj=a
    for j in range(terms):
        p*=(1-aj); aj*=q2
        if abs(aj)<mp.mpf(10)**(-(mp.mp.dps+8)): break
    return p

def make_F(q):
    """Return F(k)=log g(k) analytic in complex k, and Y3 via direct sum (check)."""
    q2=q*q
    P2inf=qpoch_inf(q2,q2); P5inf=qpoch_inf(q**5,q2)   # (q^2;q^2)_inf, (q^5;q^2)_inf
    def g(k):
        # (q^2;q^2)_k = P2inf/(q^{2k+2};q^2)_inf ; (q^5;q^2)_k = P5inf/(q^{2k+5};q^2)_inf
        denom1=P2inf/qpoch_inf(q**(2*k+2),q2)
        denom2=P5inf/qpoch_inf(q**(2*k+5),q2)
        return (2**k)*((1-q)**k)*q**(k*k+3*k)/(denom1*denom2)
    def F(k): return mp.log(g(k))
    return g,F

def Y3_sum(q):
    g,_=make_F(q); S=mp.mpf(0); k=0
    while True:
        t=((-1)**k)*g(k); S+=t
        if k>10 and abs(t)<mp.mpf(10)**(-(mp.mp.dps+6)): break
        k+=1
        if k>200000: break
    return S

# poles
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()] if __import__('os').path.exists('poles.txt') else None
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1);maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j;S+=2*q/(1-q**(k+1))*pr;pr*=2*q**(k+3)/(1-q**(k+2))-2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=14):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);dq=f0/fp;q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)):break
    return q

print("="*82)
print("SCOPING the q-Bessel confluence (U's B(a2)).  Per pole: verify rep, find complex saddle, test E=leading SP")
print("="*82)
mlist=[2,4,6,8,10] if poles else []
print(f"{'m':>2}{'tau':>9}{'w':>8}{'|P12|/t^1.5':>11}{'Y3 rep ok':>10}{'saddle k*':>22}{'F2!=0':>9}{'|lead SP|/|E|':>13}")
for m in mlist:
    q=refine(poles[m-1]); tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int((mp.mp.dps+15)*2.3026/tau)+60
    P12,Se=cocycle_P12(q,N)
    Y3=Y3_sum(q)
    rep_ok=abs((2*q**3/(1-q**3))*Y3 - P12)/abs(P12)   # should be ~1e-(dps)
    g,F=make_F(q)
    # complex saddle of Phi(k)=i pi k + F(k):  Phi'(k*)=0 => F'(k*) = -i pi
    def Fp(k,h=mp.mpf('1e-12')): return (F(k+h)-F(k-h))/(2*h)
    def Fpp(k,h=mp.mpf('1e-9')): return (F(k+h)-2*F(k)+F(k-h))/h**2
    # Newton from k0 ~ i w/2 (memory: k*=-5/4+i w/2)
    k0=mp.mpc(-1.25, float(w/2))
    ks=k0
    for _ in range(60):
        fp=Fp(ks)+I*mp.pi; fpp=Fpp(ks)
        if fpp==0: break
        dk=fp/fpp; ks=ks-dk
        if abs(dk)<mp.mpf(10)**(-20): break
    F2=Fpp(ks)
    # leading SP term of  sum (-1)^k g = n=0 Poisson:  int e^{i pi k+F} dk ~ e^{i pi k*+F(k*)} sqrt(2 pi/(-Phi''))
    Phi_ks=I*mp.pi*ks+F(ks)
    leadSP=mp.e**(Phi_ks)*mp.sqrt(2*mp.pi/(-F2))
    P12_lead=(2*q**3/(1-q**3))*leadSP
    E=mp.mpf('0.5')*(w-w*mp.e**(-tau/2))**2*mp.sin(w)*mp.sin(w-w*mp.e**(-tau/2))
    ratio=abs(P12_lead)/abs(E) if E!=0 else mp.inf
    print(f"{m:>2}{float(tau):>9.5f}{float(w):>8.4f}{float(abs(P12)/tau**1.5):>11.5f}{float(rep_ok):>10.0e}"
          f"{'  '+mp.nstr(ks,7):>22}{float(abs(F2)):>9.4f}{float(ratio):>13.5f}")
print("\nLegend: rep ok ~1e-35 confirms Y3=sum d_k rep (Q1). F2!=0 => nondegenerate saddle (Q2).")
print("|lead SP|/|E|->1 would mean E IS the leading saddle term => R=P12-E is the clean SUBLEADING SP (Q3,case II).")
print("If !=1, leading SP and E differ => need to understand what E captures (phase/Poisson n=+-1 mixing).")
