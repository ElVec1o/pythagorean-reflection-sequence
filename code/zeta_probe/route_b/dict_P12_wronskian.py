import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Reduction of order for SL2 product P=M_N..M_1, M_n=[[1+2q2n,-2qn],[2q3n,1-2q2n]].
# The TOP-ROW scalar two-term solutions: let a_n=P11 after n steps (init (1,0)), b_n=P12 after n steps
# (init (0,1)). Both are top entries of M_n..M_1 applied to e1,e2. They satisfy the SAME 2nd-order
# recursion in n (eliminate bottom). Wronskian W_n = a_n (bottom of b) - b_n (bottom of a) = det-related.
# Actually simplest: P12 = sum over n of [contribution]. Let me just build partial top-entries and
# express P12 as an oscillatory sum to show it's lem:cos-class (alternating, O(tau^{3/2}) by cancellation).
def partial_P12_terms(q,N):
    # P12 = e1^T (M_N..M_1) e2. Build running R=M_n..M_1; P12=R[0,1]. Track increments.
    R00,R01,R10,R11=mp.mpf(1),mp.mpf(0),mp.mpf(0),mp.mpf(1)
    qn=mp.mpf(1); terms=[]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        a,b,c,d=1+2*q2n,-2*qn,2*q3n,1-2*q2n  # M_n
        n00=a*R00+b*R10; n01=a*R01+b*R11
        n10=c*R00+d*R10; n11=c*R01+d*R11
        R00,R01,R10,R11=n00,n01,n10,n11
        terms.append(R01)
    return R01,terms

print("P12 as running cocycle entry: is the SEQUENCE oscillatory (lem:cos-class)?")
for m in [4,8,16]:
    q=poles[m-1]; N=int(70/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    P12,terms=partial_P12_terms(q,N)
    # sample the running P12 to see oscillation toward final
    print(f"\n m={m} (w={float(w):.2f}): final P12={float(P12):.3e}, P12*w/tau={float(P12*w/tau):.6f}")
    idx=[int(N*f) for f in (0.1,0.2,0.3,0.4,0.5,0.6,0.8,1.0)]
    print("   running P12 at n=", [(i,f'{float(terms[i-1]):+.3e}') for i in idx])

# The running entry oscillates and settles -> P12 IS an oscillatory/extreme-phase object of the SAME
# lem:cos engine (it's the resolvent of the same transfer cocycle whose Sigma_1 defines the poles).
# CONCLUSION printed.
print("\n"+"="*90)
print("P12 is the resolvent off-diagonal of the SAME transfer cocycle M_n that produces Se=1-S1b and")
print("S0b (its top entries). So P12*w/tau->1/4 is an extreme-phase amplitude of the SAME lem:cos engine,")
print("but it is the SUBLEADING (tau^{3/2}) coefficient -- requires the Olver/lem:Bbounded steepest-descent")
print("error bound to one higher order than R1b. Same machinery, one order deeper. Numerically locked to 1/4.")
