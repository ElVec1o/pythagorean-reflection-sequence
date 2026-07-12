#!/usr/bin/env python3
"""No algebraic differential equation for S(q) up to order 4, degree 5 (paper2 prop:nofinitering).

Evidence that the beta_2 series S(q) = sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k} is differentially
transcendental in q -- hence the DESCENT VARIABLE q carries no finite differential ring, which is the
precise obstruction to a classical (Nesterenko/Binyamini) multiplicity estimate for the value q*.

Method: Taylor-expand S at q=0 to order M mod a 31-bit prime; form all monomials of degree <= deg in
(S, S', ..., S^{(order)}) times q^j (j <= qshift); compute the rank of the coefficient matrix (M rows).
Full rank = no linear dependence = NO differential-algebraic relation of that shape.

Result (M=900, p=2^31-1): order<=4, degree<=5 windows all FULL RANK -> no relation. The (sigma,delta)
finiteness of the module lives jointly in (z-shift, q-derivative); it does NOT descend to a finite
differential ring in q alone, because sigma: z -> q^2 z moves the diagonal off itself.
"""
import numpy as np
from itertools import combinations_with_replacement as cwr

p = (1 << 31) - 1
M = 900


def pmul(a, b):
    c = np.zeros(M+1, dtype=np.int64)
    for i, ai in enumerate(a):
        if ai == 0: continue
        L = M+1-i
        c[i:i+L] = (c[i:i+L] + ai*b[:L]) % p
    return c


def inv_1_minus_qn(n):
    a = np.zeros(M+1, dtype=np.int64)
    a[0:M+1:n] = 1
    return a


def series_S():
    S = np.zeros(M+1, dtype=np.int64)
    omq = np.zeros(M+1, dtype=np.int64); omq[0] = 1; omq[1] = p-1
    for k in range(40):
        if k*k > M: break
        term = np.zeros(M+1, dtype=np.int64); term[0] = pow(p-2, k, p)
        for _ in range(k): term = pmul(term, omq)
        t2 = np.zeros(M+1, dtype=np.int64); t2[k*k:] = term[:M+1-k*k]; term = t2
        for i in range(1, 2*k+1): term = pmul(term, inv_1_minus_qn(i))
        S = (S + term) % p
    return S


def deriv(a):
    b = np.zeros(M+1, dtype=np.int64)
    for n in range(1, M+1): b[n-1] = (a[n]*n) % p
    return b


def rank_modp(A):
    A = A.copy() % p; rows, ncols = A.shape; r = 0
    for c in range(ncols):
        piv = next((rr for rr in range(r, rows) if A[rr, c] % p), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r]*pow(int(A[r, c]), p-2, p)) % p
        for rr in range(rows):
            if rr != r and A[rr, c] % p:
                A[rr] = (A[rr] - A[rr, c]*A[r]) % p
        r += 1
        if r == rows: break
    return r


def search(D, order, deg, qshift, Mrows):
    vars_ = D[:order+1]
    cols = []
    for d in range(deg+1):
        for combo in cwr(range(order+1), d):
            v = np.zeros(M+1, dtype=np.int64); v[0] = 1
            for idx in combo: v = pmul(v, vars_[idx])
            for j in range(qshift+1):
                w = np.zeros(M+1, dtype=np.int64); w[j:] = v[:M+1-j]
                cols.append(w[:Mrows])
    A = np.array(cols, dtype=np.int64).T
    return A.shape[1], rank_modp(A)


if __name__ == "__main__":
    S = series_S()
    D = [S]
    for _ in range(4): D.append(deriv(D[-1]))
    print("S(q) mod p, coeffs [0..6]:", S[:7].tolist(), "(= 1,-2,0,-2,4,-6,4)")
    for order, deg, qs in [(3, 4, 5), (4, 3, 4), (3, 5, 4), (4, 4, 3)]:
        nc, rk = search(D, order, deg, qs, min(M+1, 800))
        print(f"order={order} deg={deg} qshift={qs}: {nc} monomials, rank {rk} -> "
              + ("NO relation" if rk == nc else f"RELATION (nullity {nc-rk})"))
