import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

def homog_Q(q,N):
    q=mp.mpf(q)
    A=lambda b:(1+q)-2*(1-q)*q**(2*b+1)
    Q=[mp.mpf(0),mp.mpf(1)]
    for b in range(1,N):
        Q.append(A(b)*Q[b]-q*Q[b-1])
    return Q

# b0 = L_1 * Q_inf exactly. Want b0*tau->2.
# Strategy: get continuum asymptotics of BOTH L_1 and Q_inf.
# Q_b solves homog with Q_0=0,Q_1=1. In Bessel basis (valid for all b once tau small):
#   psiQ_b = q^{-b/2}Q_b = aQ*J0(w q^b)+cQ*Y0(w q^b).
# Q_0=0 => psiQ_0=0 => aQ J0(w)+cQ Y0(w)=0  (z0=w q^0=w).
# Q_1=1 => psiQ_1=q^{-1/2} => aQ J0(wq)+cQ Y0(wq)=q^{-1/2}.
# Solve aQ,cQ. Then Q_inf = lim q^{b/2}psiQ_b. As z=w q^b->0:
#   psiQ_b ~ aQ*1 + cQ*(2/pi)(ln(z/2)+gamma). q^{b/2}=sqrt(z/w).
#   Q_b ~ sqrt(z/w)[aQ + cQ(2/pi)(ln(z/2)+gamma)] -> 0 ??  but Q_inf is finite nonzero!
# So again const mode missed. The const mode = the DISCRETE correction beyond leading Bessel.
# RESOLUTION: Q_inf is NOT z->0 of the Bessel; it's the amplitude of the lambda=1 mode which
# the leading-order Bessel sends to 0. Need the NEXT order (the "const-mode/subleading piece"
# the prompt warns about). Let's just get Q_inf NUMERICALLY vs tau and L_1 vs tau, find scalings.
print(f"{'q':>8}{'tau':>10}{'w':>9}{'Q_inf':>12}{'L_1':>12}{'b0':>12}{'b0*tau':>10}")
for qf in ['0.9','0.95','0.97','0.99','0.995','0.997','0.999']:
    q=mp.mpf(qf); N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    Q=homog_Q(q,N); Qinf=Q[-1]
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f"{qf:>8}{float(tau):>10.5f}{float(w):>9.3f}{float(Qinf):>12.5f}{float(L[1]):>12.5f}{float(b0):>12.4f}{float(b0*tau):>10.5f}")
