import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# SOURCE 1: c_b=2 q^{2b}. RHS of 2nd-order recursion = c_{b+1}-q c_b = 2q^{2b+2}-2q*q^{2b}
#   = 2q^{2b}(q^2-q)= -2q^{2b+1}(1-q). matches prompt: RHS=-2(1-q)q^{2b+1}.
# t1 = u1[0] is the source-1 'travel' boundary value (analog of L_1? actually u0[0]=t0,u1[0]=t1).
# In raw, u1 is built by the SAME backward recursion as u0 but with c1=2q^{2b}. And the L1
# accumulator (b1) is the source-1 resolvent. The prompt says s=g_V t1, t1=u1[0].
# Let me find an exact summed identity for t1 like we did for b0.
# First understand what u1[0] is. The backward recursion:
#  u1[b-1]=u1[b](1+2q2b)+qb*c1 + vb(c1+2 qb u1[b]),  c1=2 q2b.  u1[N]=0.
# This is the 'travel' dressing. Hard to telescope directly. Let me instead get the
# source-1 analog L^{(1)}_b (the partial cumsum b1 accumulator) and its summed form,
# then relate t1. Let me reconstruct L^{(1)}_b and S^{(1)}_b.
# Actually the cleanest: mirror the source-0 derivation. For source1, define M_b (=L^{(1)}_b)
# solving: M_{b+1}-[(1+q)-2(1-q)q^{2b+1}]M_b+qM_{b-1} = -2(1-q)q^{2b+1}, M_0=0.
# Then check t1 relation. Build M_b from this recursion (need M_1). Get M_1 from raw's l1?
# l1 is the dressed accumulator. Let me just reconstruct via the 1st-order system for source1:
#  M_b=M_{b-1}+c_b+2q^b S^{(1)}_b, c_b=2q^{2b}; S^{(1)}_{b+1}=S^{(1)}_b-(1-q)q^b M_b.
# with M_0=0, S^{(1)}_inf=0. Solve by shooting on S^{(1)}_1 to enforce S^{(1)}_inf=0.
for m in [2,4,8]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N);
    tau=-mp.log(q); w=mp.sqrt(2/tau); gV=q/(1-q)
    print(f'm={m}: t1={float(t1):.6f} s=gV*t1={float(gV*t1):.6f} b1(dressed l1)={float(b1):.5f}')
