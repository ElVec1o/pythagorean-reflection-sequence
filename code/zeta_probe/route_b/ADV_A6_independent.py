"""
INDEPENDENT adversarial verification of the A6 attack.

Claims under test:
 (C1) P11 = S0_bulk  (EXACT, all q)
 (C2) Se = P22 = 1 - S1_bulk (EXACT, all q)
 (C3) At a travel pole Sig_t(q_m)=1:  P12 = 1/P11 - Se   (EXACT scalar identity)
 (C4) |P12|/tau^{3/2} -> (1/sqrt2)(2 c1 + c0^2),  c0=sqrt2/36, c1=0.12423
 (C5) GATE:  |P12| < (1/sqrt2) tau^{3/2}  at every travel pole, asymptote 1/(4sqrt2)=0.17678
 (C6) sup_m |P12|/tau^{3/2} = 0.18043, margin 3.92x to 1/sqrt2=0.70711.
 (C7) c1 = 1/3 - kappa, kappa->0.2091; gate <=> c1 < (1-c0^2)/2 = 0.49923.

I build the cocycle from scratch (matrix product), independently define S0_bulk,
S1_bulk from the bulk recursion, refine poles independently, and test each claim.
"""
import mpmath as mp

# ---- cocycle as an explicit 2x2 matrix product (independent of attack's inlined form) ----
# The transfer matrix per the attack:
#   [x,y; X,Y] columns: state vectors. We reconstruct from the update rule given in prompt:
#     x,y,X,Y = x*(1+2q2n)-2y qn,  2x q3n + y(1-2q2n),  X*(1+2q2n)-2Y qn,  2X q3n + Y(1-2q2n)
# This is M_n applied to TWO vectors (x,y) and (X,Y). M_n = [[1+2q2n, -2qn],[2q3n, 1-2q2n]].
# Initial: (x,y)=(0,1), (X,Y)=(1,0). So the product matrix P = M_N...M_1 has
#   P @ (0,1)^T = (x,y)^T ,  P @ (1,0)^T = (X,Y)^T.
# i.e. column 0 of P = (X,Y) [the (1,0) image], column 1 of P = (x,y) [the (0,1) image].
# So P = [[X, x],[Y, y]].  Entries: P11=X, P12=x, P21=Y, P22=y.
# That means: P11=X, P22=y=Se, P12=x, P21=Y.
# NOTE: prompt comment says cocycle returns (P12,Se,P11,P21)=(Y,y,X,x) -> P12=Y,P11=X,Se=y,P21=x.
# Attack's A6 script returns (P11,P12,P21,Se)=(X,Y,x,y) -> P12=Y, Se=y.
# There is an AMBIGUITY: is P12 the entry x or the entry Y? Test BOTH against the matrix.

def Mn(q, n):
    qn = q**n; q2n = qn*qn; q3n = q2n*qn
    return mp.matrix([[1+2*q2n, -2*qn],[2*q3n, 1-2*q2n]])

def cocycle_matrix(q, N):
    P = mp.matrix([[1,0],[0,1]])
    for n in range(N,0,-1):   # M_N ... M_1 (leftmost is M_N)
        P = P * Mn(q,n)
    return P

def cocycle_inline(q,N):
    # the prompt's inline version
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return x,y,X,Y

# ---- bulk blocks S0_bulk, S1_bulk (continued-fraction-style sum) independently ----
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J=200000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod
        prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-6) and j>80: break
    return tot

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(260/(1-q))+80
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-12): break
    return S

def refine_pole(q0, iters=14):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
c0=mp.sqrt(2)/36
gate=1/mp.sqrt(2)

print("="*110)
print("INDEPENDENT A6 verification.  gate=1/sqrt2=%.7f  c0=sqrt2/36=%.7f  1/(4sqrt2)=%.7f  (1-c0^2)/2=%.7f"
      % (float(gate),float(c0),float(1/(4*mp.sqrt(2))),float((1-c0**2)/2)))
print("="*110)
print(("{:>3} {:>11} {:>11} {:>11} {:>11} {:>13} {:>11} {:>11}").format(
    "m","tau","P11/S0b","Se/(1-S1b)","P12=x?","P12=Y?","|P12x|/t1.5","|P12Y|/t1.5"))

sup_gate_x=mp.mpf(0); sup_gate_Y=mp.mpf(0)
rows=[]
for m in [2,4,8,16,24,32,48,64,79]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=60+int(2.4*float(w0))
    q=refine_pole(poles[m-1])
    tau=-mp.log(q); w=mp.sqrt(2/tau); s=mp.sin(w); cw=mp.cos(w)
    N=int(90/(1-q))
    P = cocycle_matrix(q,N)
    P11m,P12m_x,P21m,P22m = P[0,0],P[0,1],P[1,0],P[1,1]
    xi,yi,Xi,Yi = cocycle_inline(q,N)
    # cross-check inline vs matrix
    assert abs(P11m-Xi)<mp.mpf(10)**(-30), (m,"P11 mismatch")
    assert abs(P12m_x-xi)<mp.mpf(10)**(-30), (m,"x mismatch")
    assert abs(P21m-Yi)<mp.mpf(10)**(-30), (m,"Y mismatch")
    assert abs(P22m-yi)<mp.mpf(10)**(-30), (m,"y mismatch")
    P11=P11m; Se=P22m; cand_x=P12m_x; cand_Y=P21m  # the off-diag entries
    S0b=Sbulk(0,q); S1b=Sbulk(1,q)
    id1=P11/S0b; id2=Se/(1-S1b)
    t15=tau**mp.mpf('1.5')
    # which off-diag entry satisfies P12 = 1/P11 - Se ?
    target = 1/P11 - Se
    err_x = abs(cand_x-target); err_Y=abs(cand_Y-target)
    gx=abs(cand_x)/t15; gY=abs(cand_Y)/t15
    sup_gate_x=max(sup_gate_x,gx); sup_gate_Y=max(sup_gate_Y,gY)
    rows.append((m,tau,id1,id2,err_x,err_Y,gx,gY,float(target/t15)))
    print(("{:>3} {:>11.4e} {:>11.7f} {:>11.7f} {:>11.2e} {:>13.2e} {:>11.7f} {:>11.7f}").format(
        m,float(tau),float(id1),float(id2),float(err_x),float(err_Y),float(gx),float(gY)),flush=True)
    mp.mp.dps=50

print("-"*110)
print("sup |x|/t^1.5 = %.7f ;  sup |Y|/t^1.5 = %.7f" % (float(sup_gate_x),float(sup_gate_Y)))
print("which off-diag entry = 1/P11 - Se ?  (err_x vs err_Y above: the small one is the true P12)")
