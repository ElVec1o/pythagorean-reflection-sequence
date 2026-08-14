import mpmath as mp
mp.mp.dps=80
exec(open('dict_compare.py').read().split('poles=')[0])
exec(open('dict_P12.py').read().split('def block')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Cocycle step:  [x;y] -> [x(1+2q2n)-2y qn ; 2x q3n + y(1-2q2n)].
# Columns: (P11,P21) from init (X=1,x=0); (P12,P22) from init (Y=0,y=1).
# So the matrix M_n = [[1+2q2n, -2qn],[2q3n, 1-2q2n]], P = M_N...M_1.
# P22=Se, P21=-S0b proven. Now: is P11 a bulk-type Lambert block? P12?
# Build them as their OWN telescoping sums. Define via the SECOND column already = (P12,P22)=(?,Se).
# Note P12 column starts (0,1): so P12 = sum over the -2qn coupling injecting from y into x.
# Let me just get accurate P11,P12 at poles and test P11~w, P11*Se->1, P12~(So)/(something).

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

print("R2 mechanism. P11*Se=1-P12*S0b; P11~? , P12~? at travel poles.")
print(f"{'m':>3} {'tau':>10} {'w':>9} {'P11':>12} {'P11*Se':>11} {'P11/w':>10} {'P12':>13} {'P12*w':>11} {'P12*w/tau':>11}")
for m in [1,2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    P12,P22,P11,P21=cocycle_full(q,N)
    print(f"{m:>3} {float(tau):>10.6f} {float(w):>9.4f} {float(P11):>12.5f} {float(P11*P22):>11.7f} {float(P11/w):>10.6f} {float(P12):>13.8f} {float(P12*w):>11.7f} {float(P12*w/tau):>11.6f}")

# t1=P12/Se. s=(q/p)t1->1/4. (q/p)tau->1 so t1~tau/4. P12=t1*Se~ (tau/4)*(1/w) [Se~1/w].
# => P12*w/tau -> 1/4 ? check above. And t1/tau=P12/(Se*tau). Se~1/w => P12/(Se tau)=P12*w/tau (approx).
print("\nKey R2 reduction: t1/tau = P12/(Se*tau).  Se*w->1 (R1 fact2).  So t1/tau ~ (P12*w)/tau.")
print(f"{'m':>3} {'t1/tau':>11} {'P12*w/tau':>11} {'(P12*w/tau)/(Se*w)':>18}")
for m in [2,4,8,16,32]:
    if m>len(poles): break
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    P12,P22,P11,P21=cocycle_full(q,N)
    Se=P22
    print(f"{m:>3} {float(t1/tau):>11.7f} {float(P12*w/tau):>11.7f} {float((P12*w/tau)/(Se*w)):>18.7f}")
