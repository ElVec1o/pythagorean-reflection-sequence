import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Determine L_1 (source-0) in closed form and Q_inf in closed form.
# Recall the FIRST-order system before elimination:
#   L_b = L_{b-1} + c_b + 2 q^b S_b   (c_b=2q^b for source0)
#   S_{b+1}= S_b - (1-q) q^b L_b
# with L_0=0 and S_? boundary. What's S_1? The cumsum starts. b0=L_inf, S_inf=?
# Actually from raw forward loop, l0 accumulates with dd division -- that's the dressed version.
# Let me instead just measure L_1 and S_1 from the homogeneous structure and fit.
# L_1 = c_1 + 2 q S_1 = 2q + 2q S_1  (with L_0=0). So S_1=(L_1-2q)/(2q).

for qf in ['0.9','0.95','0.99','0.999']:
    q=mp.mpf(qf); N=int(50/(1-q)); b0,b1,t0,t1,L0,L1=raw(q,N)
    L=[mp.mpf(0)]+L0
    L1v=L[1]
    S1=(L1v-2*q)/(2*q)
    print(f'q={qf}: L_1={float(L1v):.6f} S_1={float(S1):.6f} b0={float(b0):.6f}')
