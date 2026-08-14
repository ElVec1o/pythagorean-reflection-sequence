import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# Compare TRUE Sigma=sum q^c L_c(1-q^c) to (1/tau)int_0^1 L(u)(1-u)du with TRUE L (interp),
# AND to closed-form L. Isolate which approximation fails.
for m in [2,4,8]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    Sig_true=sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    # integral with TRUE L sampled: Sigma ~ (1/tau) int_0^1 L(u)(1-u) du
    # discretize using actual L_c at u_c=q^c. The sum IS the Riemann sum with weight tau:
    #   sum_c f(q^c) ~ (1/tau) int_0^1 f(u)/u du? Let's see: c-> u=q^c, dc=-du/(u tau).
    #   sum_{c>=1} G(c) ~ int_{0.5}^inf G(c)dc. G(c)=q^c L_c(1-q^c)=u L(u)(1-u).
    #   = int u L(u)(1-u) * du/(u tau) = (1/tau) int_0^q L(u)(1-u)du.
    Lint=b0/mp.sin(w)
    Sig_cf=(1/tau)*mp.quad(lambda u: (b0*mp.sin(w*(1-u))/mp.sin(w))*(1-u), [0,q])
    print(f'm={m} Sig_true={float(Sig_true):.5f} Sig_closedform_int={float(Sig_cf):.5f} b0={float(b0):.4f}')
    # what b0 would the closed-form-int self consistency give for the FULL eqn:
    # b0 = 2q/(1-q)+2q Sig.  If Sig=Sig_cf(b0)=b0*K, then b0=2q/(1-q)/(1-2qK).
    K=Sig_cf/b0
    b0pred=2*q/(1-q)/(1-2*q*K)
    print(f'    K={float(K):.5f} b0pred={float(b0pred):.4f}')
