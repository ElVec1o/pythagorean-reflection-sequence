"""
Fully independent adversarial verification of R2 claims.
- raw() reimplemented per prompt spec.
- Bulk blocks S0b,S1b from the ALPHA/GAMMA definition in the prompt (NOT colleague's Pochhammer form).
- Cocycle product M_n=[[1+2q^{2n},-2q^n],[2q^{3n},1-2q^{2n}]].
- Verify EVERY claimed exact identity and the asymptotics.
"""
import mpmath as mp

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
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
    return l0,l1,u0[0],u1[0]   # b0,b1,t0,t1

# Bulk lem:cos blocks from PROMPT definition (alpha/gamma), NOT colleague's Pochhammer form.
def bulk_blocks(q,J):
    q=mp.mpf(q)
    def alpha(k): return 2*q**(k+1)/(1-q**(k+1))
    def gamma(k): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
    # S1b = sum_j alpha(1+2j) prod_{i<j} gamma(1+2i)
    # S0b same with k start 0
    def Sb(kstart):
        tot=mp.mpf(0); prod=mp.mpf(1)
        for j in range(J):
            tot += alpha(kstart+2*j)*prod
            prod *= gamma(kstart+2*j)
        return tot
    return Sb(0), Sb(1)   # S0b, S1b

def cocycle_full(q,N):
    # columns: col A = (X,Y) starting (1,0); col B = (x,y) starting (0,1)
    # M_n=[[1+2q^{2n},-2q^n],[2q^{3n},1-2q^{2n}]] applied to column vectors
    q=mp.mpf(q)
    X=mp.mpf(1);Y=mp.mpf(0); x=mp.mpf(0);y=mp.mpf(1)
    qn=mp.mpf(1)
    # also record partial Se_k (=y after k steps) and P12 partials for Casoratian
    y_list=[y]; Y_list=[Y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        Xn=X*(1+2*q2n)-Y*2*qn;   Yn=X*2*q3n+Y*(1-2*q2n)
        xn=x*(1+2*q2n)-y*2*qn;   yn=x*2*q3n+y*(1-2*q2n)
        X,Y,x,y=Xn,Yn,xn,yn
        y_list.append(y); Y_list.append(Y)
    # P = [[P11,P12],[P21,P22]] with columns (X,Y) and (x,y):
    # P11=X (col A top), P21=Y (col A bot), P12=x (col B top), P22=y (col B bot)
    return X,Y,x,y,y_list,Y_list  # P11=X,P21=Y,P12=x,P22=y

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*100)
print("PART 1: EXACT IDENTITY CHECKS at generic q (off-pole), high precision")
print("="*100)
mp.mp.dps=60
for q in [mp.mpf('0.70'),mp.mpf('0.80'),mp.mpf('0.88'),mp.mpf('0.92'),mp.mpf('0.96')]:
    N=int(80/(1-q)); J=N+50
    b0,b1,t0,t1=raw(q,N)
    S0b,S1b=bulk_blocks(q,J)
    Xa,Ya,xb,yb,_,_=cocycle_full(q,N)
    # colleague convention: P12 = Ya (bottom of col that started (1,0)); P22 = yb (Se)
    #                       P21 = xb (top of col that started (0,1)) -> claim P21=-S0b
    #                       P11 = Xa
    P11=Xa; P12=Ya; P21=xb; P22=yb
    p=1-q
    Se=1-S1b
    So=(p/(2*q))*S0b
    det = P11*P22 - P12*P21
    e_P22  = abs(P22 - Se)
    e_P21  = abs(P21 - (-S0b))
    e_det  = abs(det - 1)
    # dictionary: t1 = P12/Se
    e_t1   = abs(t1 - P12/Se)
    e_b0   = abs(b0 - S0b/(1-S1b))
    e_b1   = abs(b1 - S1b/(1-S1b))
    e_t0   = abs(t0 - S1b/(1-S1b))
    print(f"q={float(q):.3f}: P22-Se={float(e_P22):.2e} P21+S0b={float(e_P21):.2e} det-1={float(e_det):.2e}")
    print(f"         t1-P12/Se={float(e_t1):.2e} b0-S0b/(1-S1b)={float(e_b0):.2e} b1-S1b/Se={float(e_b1):.2e} t0-S1b/Se={float(e_t0):.2e}")

print("="*100)
print("PART 2: Casoratian telescoping closed form t1 = sum_n 2 q^{3n}/(y_n y_{n-1})")
print("="*100)
mp.mp.dps=60
for q in [mp.mpf('0.80'),mp.mpf('0.92')]:
    N=int(80/(1-q))
    b0,b1,t0,t1=raw(q,N)
    Xa,Ya,xb,yb,y_list,Y_list=cocycle_full(q,N)
    # y_list[k]=Se after k steps (y_0=1). Casoratian sum t1=sum_{n>=1} 2 q^{3n}/(y_n y_{n-1})
    tot=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q; q3n=qn*qn*qn
        tot += 2*q3n/(y_list[n]*y_list[n-1])
    print(f"q={float(q):.3f}: t1_raw={mp.nstr(t1,15)}  t1_casoratian={mp.nstr(tot,15)}  diff={float(abs(t1-tot)):.2e}")

print("="*100)
print("PART 3: ASYMPTOTICS at travel poles")
print(" check: t1/tau->1/4 ; S0b*Se->1 ; P12/(tau^1.5 sin w)->sqrt2/8 ; Se/(sqrt(tau/2) sinw)->1")
print("="*100)
sqrt2_8=mp.sqrt(2)/8
print(f"{'m':>3} {'tau':>10} {'t1/tau':>11} {'S0b*Se':>10} {'P12/(t^1.5 sinw)':>16} {'Se/(sqrt(t/2)sinw)':>18} {'P12_amp/(sqrt2/8)':>17}")
for m in [1,2,4,8,16,24,32,40,56,72]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.5*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q)); J=N+60
    b0,b1,t0,t1=raw(q,N)
    S0b,S1b=bulk_blocks(q,J)
    Xa,Ya,xb,yb,_,_=cocycle_full(q,N)
    P12=Ya; Se=1-S1b
    sinw=mp.sin(w)
    p12amp = P12/(tau**mp.mpf('1.5')*sinw)
    seamp  = Se/(mp.sqrt(tau/2)*sinw)
    s0bse  = S0b*Se
    print(f"{m:>3} {float(tau):>10.3e} {float(t1/tau):>11.7f} {float(s0bse):>10.6f} {float(p12amp):>16.9f} {float(seamp):>18.9f} {float(p12amp/sqrt2_8):>17.9f}")
    mp.mp.dps=60
print(f"\nsqrt2/8 = {mp.nstr(sqrt2_8,12)}")
