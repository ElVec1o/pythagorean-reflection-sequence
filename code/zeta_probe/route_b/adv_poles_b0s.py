import mpmath as mp
mp.mp.dps = 40

def raw(q, N):
    qp = [mp.mpf(1)]*(N+1)
    for b in range(1, N+1): qp[b] = qp[b-1]*q
    v = [mp.mpf(0)]*(N+1); u0 = [mp.mpf(0)]*(N+1); u1 = [mp.mpf(0)]*(N+1)
    for b in range(N, 0, -1):
        qb = qp[b]; q2b = qb*qb; q3b = q2b*qb
        dd = 1 - 2*q2b - 2*qb*v[b]
        vb = (v[b]*(1+2*q2b) + 2*q3b)/dd
        c0 = 2*qb; c1 = 2*q2b
        u0[b-1] = u0[b]*(1+2*q2b) + qb*c0 + vb*(c0 + 2*qb*u0[b])
        u1[b-1] = u1[b]*(1+2*q2b) + qb*c1 + vb*(c1 + 2*qb*u1[b])
        v[b-1] = vb
    l0 = mp.mpf(0); l1 = mp.mpf(0)
    for b in range(1, N+1):
        qb = qp[b]; q2b = qb*qb
        dd = 1 - 2*q2b - 2*qb*v[b]
        l0 = (l0 + 2*qb + 2*qb*u0[b])/dd
        l1 = (l1 + 2*q2b + 2*qb*u1[b])/dd
    return l0, l1, u0[0], u1[0]

def Nfor(q): return int(50/(1-q)) + 5

poles = []
with open("poles.txt") as f:
    for line in f:
        line=line.strip()
        if line: poles.append(mp.mpf(line))

print("=== travel poles: b0*tau and s ===")
print(f"{'m':>3} {'q':>10} {'b0*tau':>16} {'s=gV*t1':>16} {'(b0tau-2)/tau^2':>16} {'(s-1/4)/tau':>14}")
for m,q in enumerate(poles):
    if m>22: break
    tau = -mp.log(q)
    N = Nfor(q)
    l0,l1,t0,t1 = raw(q,N)
    gV = q/(1-q)
    s = gV*t1
    b0tau = l0*tau
    r1 = (b0tau-2)/tau**2
    r2 = (s - mp.mpf(1)/4)/tau
    print(f"{m:>3} {float(q):>10.6f} {mp.nstr(b0tau,12):>16} {mp.nstr(s,12):>16} {mp.nstr(r1,6):>16} {mp.nstr(r2,6):>14}")
