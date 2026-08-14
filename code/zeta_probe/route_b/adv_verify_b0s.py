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

def Nfor(q):
    return int(50/(1-q)) + 5

# ----- colleague's b0 closed form -----
def b0_closed(q):
    # Sigma_even = sum_j (-2(1-q))^j q^{j(j+1)} / (q;q)_{2j}
    # Sigma_odd  = sum_j (-2(1-q))^j q^{j(j+2)} (1-q) / (q;q)_{2j+1}
    onem = 1-q
    def qpoch(n):  # (q;q)_n
        p = mp.mpf(1)
        for i in range(1, n+1): p *= (1-q**i)
        return p
    Se = mp.mpf(0); So = mp.mpf(0)
    for j in range(0, 200):
        term_e = (-2*onem)**j * q**(j*(j+1)) / qpoch(2*j)
        term_o = (-2*onem)**j * q**(j*(j+2)) * onem / qpoch(2*j+1)
        Se += term_e; So += term_o
        if j>5 and abs(term_e)+abs(term_o) < mp.mpf(10)**(-50): break
    return (2*q/onem)*So/Se, So, Se

print("=== b0 closed form vs raw, off-pole ===")
for q in [mp.mpf('0.8'), mp.mpf('0.9'), mp.mpf('0.95'), mp.mpf('0.97')]:
    l0,l1,t0,t1 = raw(q, Nfor(q))
    b0c, So, Se = b0_closed(q)
    print(f"q={float(q):.3f}  raw b0={mp.nstr(l0,12)}  closed={mp.nstr(b0c,12)}  diff={mp.nstr(abs(l0-b0c),3)}")
