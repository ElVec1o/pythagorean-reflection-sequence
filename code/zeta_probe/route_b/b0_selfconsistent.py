import mpmath as mp
mp.mp.dps=40
exec(open('struct_probe.py').read().split('# The forward')[0])

# EXACT: b0 = 2q/(1-q) + 2(1-q) sum_{a>=1} q^a sum_{c>=a} q^c L_c.
# Swap order: sum_{a>=1} q^a sum_{c>=a} q^c L_c = sum_{c>=1} q^c L_c sum_{a=1}^c q^a
#   = sum_{c>=1} q^c L_c * q(1-q^c)/(1-q).
# So b0 = 2q/(1-q) + 2 q sum_{c>=1} q^c L_c (1-q^c).
# i.e.  b0 = 2q/(1-q) + 2q [ sum q^c L_c - sum q^{2c} L_c ].
# Verify exact:
for qf in ['0.9','0.97','0.99']:
    q=mp.mpf(qf); N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    rhs=2*q/(1-q)+2*q*sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    print(f'q={qf} b0={float(b0):.6f} rhs={float(rhs):.6f}')
