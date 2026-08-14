import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# y-sequence and Y-sequence both solve the 2nd-order recursion from the cocycle.
# Both (x,y) and (X,Y) evolve by SAME 2x2 matrix M_n. (x,y) starts (0,1), (X,Y) starts (1,0).
# So (X_n,Y_n) and (x_n,y_n) are the two columns of the product matrix M_n...M_1 = P_n.
# P_n = [[X_n, x_n],[Y_n, y_n]]  with det=1.
# t1 = Y_N/y_N = P12/P22 (ratio of bottom row).
#
# Standard SL2 fact: for product of matrices, the ratio Y_n/y_n telescopes.
# d(Y_n/y_n) = (Y_n y_{n-1} - Y_{n-1} y_n)/(y_n y_{n-1}).
# Since columns evolve by same M: [X_n,Y_n]^T=M_n[X_{n-1},Y_{n-1}]^T etc.
# Y_n y_{n-1} - Y_{n-1} y_n : use M_n=[[a,b],[c,d]], det=1 (ad-bc=1).
#   Y_n = c X_{n-1}+d Y_{n-1},  y_n = c x_{n-1}+d y_{n-1}
#   Y_n y_{n-1} - Y_{n-1} y_n = (cX+dY)y' - Y(cx'+dy')  [primes=n-1]
#       = c(X_{n-1}y_{n-1} - Y_{n-1}x_{n-1}) = c * det(P_{n-1}) = c_n * 1
#   where c_n = 2 q^{3n} (the lower-left of M_n).
# So Y_n/y_n - Y_{n-1}/y_{n-1} = c_n/(y_n y_{n-1}) = 2 q^{3n}/(y_n y_{n-1}).
# Telescoping from n=0 (Y_0/y_0=0/1=0):
#   t1 = Y_N/y_N = sum_{n=1}^{N} 2 q^{3n}/(y_n y_{n-1}).
# where y_n = P22 partial = Se partial sequence!

def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf);N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    yh=cocyc_y(q,N)
    qn=mp.mpf(1); S=mp.mpf(0)
    for n in range(1,N+1):
        qn=qn*q
        S+=2*qn**3/(yh[n]*yh[n-1])
    print(f"q={qf}: t1={float(t1):.9f}  VOP-sum={float(S):.9f}  diff={float(t1-S):.2e}")
