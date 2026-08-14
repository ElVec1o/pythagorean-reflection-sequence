import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
# P11 vs k-shifted blocks. S1b uses alpha,gamma start k=1. Try S1b shifts and combos.
print("P11 vs block combos:")
print(f"{'q':>7} {'P11':>12} {'S1b':>11} {'S2b':>11} {'1-S1b':>11} {'S0b':>11}")
for qf in ['0.70','0.80','0.88','0.96','0.985']:
    q=mp.mpf(qf);N=int(70/(1-q))
    P12,P22,P11,P21=cocyc(q,N)
    print(f"{qf:>7} {float(P11):>12.6f} {float(Sbulk(1,q)):>11.6f} {float(Sbulk(2,q)):>11.6f} {float(1-Sbulk(1,q)):>11.6f} {float(Sbulk(0,q)):>11.6f}")
# P12 vs blocks one more time with shifts - maybe P12 is a SHIFTED Se/So.
# The cocycle started at n=1. A SHIFTED cocycle (start n=2) would give the "tail" structure.
# Test: is P12 = q-shift of Se? i.e. Se computed with q->? No. 
# Direct: P12 satisfies its own recursion. Let me get P12 as a Lambert-type series numerically (q-expansion).
print()
print("P12 q-series (low order) to identify:")
q=mp.mpf('0.001')  # tiny q to read off series coeffs
N=80
P12,P22,P11,P21=cocyc(q,N)
print(f" q=0.001: P12={mp.nstr(P12,12)}  (P12/q^?)")
for qf in ['0.0001','0.001','0.01']:
    q=mp.mpf(qf);N=200
    P12,P22,P11,P21=cocyc(q,N)
    print(f"  q={qf}: P12={mp.nstr(P12,10)} P12/(2q^3)={mp.nstr(P12/(2*q**3),8)}")
