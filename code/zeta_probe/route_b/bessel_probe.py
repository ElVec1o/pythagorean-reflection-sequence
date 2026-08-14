import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Continuum: u=q^b in (0,1]. b=0 => u=1, b=inf => u=0.
# psi_b = L_b q^{-b/2} satisfies (claimed) Bessel order 0 in variable w*u? Let's test.
# The recursion L_{b+1}-(1+q)L_b+qL_{b-1} = 2(1-q)q^{2b+1}L_b.
# Substitute tau=-ln q small. q^b=e^{-tau b}=u. Let L_b=f(u).
# L_{b+1}=f(qu)=f(e^{-tau}u), L_{b-1}=f(e^{tau}u).
# Expand: f(qu)-(1+q)f(u)+q f(e^{tau}u) ... leading -> tau^2 d/d.. Let me instead test the
# VERIFIED closed form L_b ~ b0 sin(w(1-q^b))/sin(w) and measure quality vs b.

for q in [mp.mpf('0.9'),mp.mpf('0.97'),mp.mpf('0.99')]:
    N=int(50/(1-q)); b0,b1,t0,t1,L0,L1=raw(q,N)
    L=[mp.mpf(0)]+L0
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f'\nq={float(q)} w={float(w):.4f} sin(w)={float(mp.sin(w)):.4f} b0={float(b0):.4f}')
    for b in [1,2,4,8,16,N//2,N-1]:
        approx=b0*mp.sin(w*(1-q**b))/mp.sin(w)
        print(f'  b={b:>4} L_b={float(L[b]):>10.5f} approx={float(approx):>10.5f} rel={float((approx-L[b])/(abs(L[b])+1e-9)):>9.4f}')
