import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# cocycle convA: x'=x(1+2q2n)-2y qn, y'=2x q3n+y(1-2q2n). 
# P22=y=Se, P12=Y (the y-component of the basis vector started at (X,Y)=(1,0)).
# t1=P12/Se = Y/y... wait, P22=y, P12=Y. t1=P12/P22? Let's check: t1=P12/Se=P12/P22.
# Actually the prompt cocycle returns (P12,P22,P11,P21)=(Y,y,X,x) and t1=P12/Se=Y/y.
# Let's verify and also build So-cocycle analog.

def cocyc(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    Yhist=[Y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn; Yhist.append(Y)
    return Y,y,X,x,Yhist

for qf in ['0.80','0.92']:
    q=mp.mpf(qf);N=int(70/(1-q))
    Y,yy,X,xx,Yh=cocyc(q,N)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    print(f"q={qf}: P12=Y={float(Y):.7f} P22=y={float(yy):.7f} Se={float(Se):.7f} t1={float(t1):.7f} P12/Se={float(Y/Se):.7f} P12/yy={float(Y/yy):.7f}")
    # The y-recursion: y_n = 2 x_{n-1} q3n + y_{n-1}(1-2q2n). 
    # P22=y is the "Se" block. P12=Y uses (X,Y)=(1,0) start: a DIFFERENT solution.
    # Wronskian: P11 P22 - P12 P21 = det of transfer = prod det. det of step = (1+2q2n)(1-2q2n)-(-2qn)(2q3n)=1-4q4n+4q4n=1.
    # So determinant is 1! X y - Y x =1.
    print(f"   det check X*y-Y*x = {float(X*yy-Y*xx):.10f}  (should be 1)")
