import mpmath as mp
mp.mp.dps=90
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Goal: express P12 via lem:cos blocks so R2's P12*w/tau->1/4 reduces to proven extreme-phase asymptotics.
# The cocycle M_n=[[1+2q2n,-2qn],[2q3n,1-2q2n]], P=M_N..M_1. SL2. P22=Se, P21=-S0b PROVEN.
# REDUCTION OF ORDER: track partial products P^{(n)}=M_n..M_1. Define columns at each n.
# The top-row second entry P12^{(N)} can be built from a Wronskian sum:
#   For SL2 transfer matrices, second-solution = first-solution * sum (det-step)/(prod of first sol).
# Easier: just numerically FIT P12 to a lem:cos block. Candidates with the right size (~tau/w ~ tau^{3/2}):
# So ~ (p/2q)S0b ~ (tau/2) sin w  (since S0b~w sin w, p~tau => So ~ (tau/2) sin w). Check So*w/tau:
print("P12 leading-form hunt. P12*w/tau->1/4. Compare to bulk-block-built candidates.")
print(f"{'m':>3} {'P12*w/tau':>11} {'So*w/tau':>11} {'(p/2q)S0b*w/tau':>16}")
for m in [2,4,8,16,32]:
    q=poles[m-1]; N=int(70/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    # cocycle
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n); x,y=xn,yn
    P12=x  # second column top = Y actually; recompute properly
    X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1); x2=mp.mpf(0);y2=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n); X,Y=Xn,Yn
        x2n=x2*(1+2*q2n)-2*y2*qn;y2n=2*x2*q3n+y2*(1-2*q2n); x2,y2=x2n,y2n
    P12=Y  # (0,1)-init top entry
    So=So_clf(q); S0b=Sblk(0,q)
    print(f"{m:>3} {float(P12*w/tau):>11.7f} {float(So*w/tau):>11.7f} {float((p/(2*q))*S0b*w/tau):>16.9f}")

# So*w/tau -> 1/2 (So~(tau/2)sin w, *w/tau= (1/2)*w*sin w/... wait So*w/tau, So~? let me just read).
# Then P12*w/tau->1/4 = (1/2)*(So*w/tau)?  i.e. P12 = So/2 ? Test directly:
print("\nP12 ?= So/2 :")
for m in [2,4,8,16,32]:
    q=poles[m-1]; N=int(70/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n); X,Y=Xn,Yn
    P12=Y; So=So_clf(q)
    print(f"  m={m:>2}: P12={float(P12):+.9f}  So/2={float(So/2):+.9f}  diff={float(abs(P12-So/2)):.1e}")
