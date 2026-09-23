import cmath, math
def series(q, shift, tol=1e-18, kmax=400):
    # sum_k (-2(1-q))^k q^{k^2+shift*k} / (q;q)_{2k}
    s = 1+0j; t = 1+0j; a = -2*(1-q); poch = 1+0j; big = 1.0
    qk2 = 1+0j
    for k in range(1, kmax):
        poch *= (1-q**(2*k-1))*(1-q**(2*k))
        term = a**k * q**(k*k+shift*k) / poch
        s += term
        big = max(big, abs(term))
        if abs(term) < tol*big and k > 5: break
    return s, big
B  = lambda q: series(q,0)
Se = lambda q: series(q,1)
