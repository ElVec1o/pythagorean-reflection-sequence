import mpmath as mp
mp.mp.dps=50

# ---------- exact q-series Se, So ----------
def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So

# ---------- cocycle P12 (=Y), P22(=y=Se) ----------
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  #P12,P22,P11,P21

# ---------- raw resolvent (b0,t1) ----------
def raw(q,N):
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]

# ---------- lem:cos travel blocks Sigma_0, Sigma_1 ----------
def A_(k,q): return 2*q/(1-q**(k+1))
def C_(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_(k+2*j,q)*prod; prod*=C_(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-130) and j>60: break
    return tot
# ---------- lem:cos bulk blocks S_0, S_1 ----------
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-130) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt')]

print("="*120)
print("DICTIONARY PROBE: Se, So, P12 vs lem:cos blocks Sigma_0,Sigma_1,S_0,S_1 and leading forms cos w, sin w/w")
print("="*120)
print("GENERIC q (off-pole):")
hdr=f"{'q':>7}{'w':>9}{'Se':>13}{'cos w':>11}{'So':>13}{'sinw/w':>11}{'P12':>13}{'Sig1':>11}{'Sig0':>11}{'S1blk':>11}{'S0blk':>11}"
print(hdr)
for qf in ['0.85','0.9','0.95','0.97','0.99']:
    q=mp.mpf(qf); N=int(45/(1-q)); J=int(70/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    s1=Sig(1,q); s0=Sig(0,q); sb1=Sb(1,q); sb0=Sb(0,q)
    print(f"{qf:>7}{float(w):>9.3f}{float(Se):>13.6f}{float(mp.cos(w)):>11.5f}{float(So):>13.6f}{float(mp.sin(w)/w):>11.5f}{float(P12):>13.6f}{float(s1):>11.5f}{float(s0):>11.5f}{float(sb1):>11.5f}{float(sb0):>11.5f}")

print()
print("AT TRAVEL POLES (Sigma_1=1):  [dps bumped for SeSo cancellation]")
print(f"{'m':>3}{'w':>9}{'Se':>13}{'So':>13}{'So/Se':>11}{'P12':>13}{'Sig0':>12}{'S1blk':>11}{'S0blk':>11}{'sinw':>9}{'cosw':>11}")
import sys
for i in [1,2,4,8,12,16,20,24]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps = 50 + int(2.2*float(w))   # SeSo terms ~ exp(w); need extra guard digits
    N=int(45/(1-q)); J=int(70/(1-q))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    s0=Sig(0,q); sb1=Sb(1,q); sb0=Sb(0,q)
    sw=mp.sin(w); cw=mp.cos(w)
    print(f"{i:>3}{float(w):>9.3f}{float(Se):>13.7f}{float(So):>13.7f}{float(So/Se):>11.7f}{float(P12):>13.6f}{float(s0):>12.5f}{float(sb1):>11.6f}{float(sb0):>11.5f}{float(sw):>9.4f}{float(cw):>11.4f}")
    sys.stdout.flush()
    mp.mp.dps=50
