import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

print("AT TRAVEL POLES: t1/tau -> 1/4 ?")
print(f"{'m':>3} {'tau':>10} {'w':>9} {'t1':>13} {'t1/tau':>11} {'s=g_V t1':>11}")
for i in [1,2,4,8,16,24,32,40,56,72]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.0*float(w)); 
    N=int(60/(1-q))
    yh=cocyc_y(q,N)
    qn=mp.mpf(1); S=mp.mpf(0)
    for n in range(1,N+1):
        qn=qn*q; S+=2*qn**3/(yh[n]*yh[n-1])
    t1=S; gV=q/(1-q); s=gV*t1
    print(f"{i:>3} {float(tau):>10.6f} {float(w):>9.3f} {float(t1):>13.6f} {float(t1/tau):>11.7f} {float(s):>11.7f}")
    mp.mp.dps=50
