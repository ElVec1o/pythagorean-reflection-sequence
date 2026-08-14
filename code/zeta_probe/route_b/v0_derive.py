import mpmath as mp
mp.mp.dps=30
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# v Riccati: v_{b-1}=(v_b(1+2q^{2b})+2q^{3b})/(1-2q^{2b}-2q^b v_b), v_N=0 (top), want v_0.
# s=q/(1-q) v_0 -> 1/4 => v_0 ~ (1-q)/(4q) ~ tau/4.
# Check the SCALE of v_0 vs tau:
print(f"{'m':>3}{'tau':>11}{'v0':>14}{'v0/tau':>10}{'s':>10}")
for m in [1,2,4,8,16,32]:
    q=poles[m-1]; N=int(50/(1-q))
    v=mp.mpf(0)
    qp=q
    # iterate backward from b=N..1
    for b in range(N,0,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        v=(v*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*v)
    v0=v
    tau=-mp.log(q); gV=q/(1-q)
    print(f"{m:>3}{float(tau):>11.6f}{float(v0):>14.8f}{float(v0/tau):>10.5f}{float(gV*v0):>10.6f}")
