import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Can P12 be a proven bulk block (k-shift / derivative)?  
# P12=Y solves same recursion as P22=y=Se=1-S1b but with init (1,0) instead of (0,1).
# Se=1-S1b. The companion P11=X, P21=x. Recall P21=x with (0,1) start.
# Maybe P12 relates to a y-derivative of Se w.r.t. a parameter, or to So-block.
# Test P12 vs So-related blocks: So=(p/2q)S0b.
print("P12 vs candidate blocks (generic q, EXACT test):")
print(f"{'q':>7} {'P12':>12} {'So':>11} {'S0b':>11} {'(p/2)S0b':>11} {'q So':>11}")
for qf in ['0.70','0.80','0.88','0.96','0.985']:
    q=mp.mpf(qf);p=1-q;N=int(70/(1-q))
    def cocyc(q,N):
        x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
        for n in range(1,N+1):
            qn=qn*q;q2n=qn*qn;q3n=q2n*qn
            xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
            Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
            x,y,X,Y=xn,yn,Xn,Yn
        return Y,y,X,x
    P12,P22,P11,P21=cocyc(q,N)
    Se,So=Se_So(q); S0b=Sbulk(0,q)
    print(f"{qf:>7} {float(P12):>12.6f} {float(So):>11.6f} {float(S0b):>11.6f} {float((p/2)*S0b):>11.6f} {float(q*So):>11.6f}")
