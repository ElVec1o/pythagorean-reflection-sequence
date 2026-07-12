#!/usr/bin/env python3
"""The rank-6 deformation module is a FIRST-JET sigma-module, NOT a finite differential ring
(paper2 prop:deformation, corrected). Soundness check that corrected an overclaim.

CLAIM (verified): theta^2 G and delta^2 G both ESCAPE
   span_{Q(q,z)} {G, sigma G, theta G, sigma theta G, delta G, sigma delta G}.
So the rank-<=6 module (finite as a sigma-difference module of the FIRST jet) is not closed under a
second theta or delta; there is no finite differential ring in q (consistent with prop:nofinitering).
An earlier paper draft claimed "differentiating the pinned relation yields a closed quasi-linear
system -- the precondition for Nesterenko"; that is FALSE and is now removed.

Also records the exact identity  delta G = (theta^2 - theta) G + C = z^2 G_zz + C, with
   C = sum_k (-1)^k [sum_{i=1}^{2k} i q^i/(1-q^i)] q^{k(k-1)} z^k / (q;q)_{2k}
(immediate: delta g_k = g_k [k(k-1) + sum_{i<=2k} i q^i/(1-q^i)], (theta^2-theta) picks the k(k-1)).

METHOD NOTE (a trap this project hit twice): fast z-coefficient decay + truncating g_k at k^2>=Nz
manufactures FALSE closure (too few nonzero coefficients -> everything low-rank). g_k contributes to
z^k, so ALL g_k up to Nz-1 must be kept, and nrow must exceed ncol. Perfect-square q (e.g. 1/4) also
fakes closure. Use generic non-square q and rank(A) vs rank([A|target]).
"""
p = 2147483647
Nz = 70


def inv(a): return pow(a % p, p-2, p)


def build(qnum, qden):
    q = inv(qden) * (qnum % p) % p
    Q = q*q % p

    def poch(n):
        r = 1
        for i in range(1, n+1): r = r*((1-pow(q, i, p)) % p) % p
        return r
    g = [(pow(p-1, k, p)*pow(q, k*(k-1), p) % p)*inv(poch(2*k)) % p for k in range(Nz)]
    W = []
    for k in range(Nz):
        s = k*(k-1) % p
        for i in range(1, 2*k+1): s = (s + i*pow(q, i, p) % p*inv((1-pow(q, i, p)) % p)) % p
        W.append(s)
    DW = []
    for k in range(Nz):
        s = 0
        for i in range(1, 2*k+1):
            d = inv((1-pow(q, i, p)) % p); s = (s + i*i % p*pow(q, i, p) % p*d % p*d) % p
        DW.append(s)
    dg = [g[k]*W[k] % p for k in range(Nz)]
    d2g = [g[k]*((W[k]*W[k]+DW[k]) % p) % p for k in range(Nz)]
    sh = lambda c, s: [c[k]*pow(Q, s*k, p) % p for k in range(Nz)]
    th = lambda c: [k*c[k] % p for k in range(Nz)]
    return dict(g=g, dg=dg, d2g=d2g, sh=sh, th=th)


def in_module(basis, target, D=6):
    cols = []
    for b in basis:
        for j in range(D+1):
            c = [0]*Nz
            for k in range(Nz-j): c[k+j] = b[k]
            cols.append(c)
    ncol = len(cols)

    def rank(aug):
        M = [[cols[cc][rw] for cc in range(ncol)] + ([target[rw]] if aug else []) for rw in range(Nz)]
        R = len(M); C = len(M[0]); r = 0
        for cc in range(C):
            piv = next((rr for rr in range(r, R) if M[rr][cc] % p), None)
            if piv is None: continue
            M[r], M[piv] = M[piv], M[r]; iv = inv(M[r][cc]); M[r] = [x*iv % p for x in M[r]]
            for rr in range(R):
                if rr != r and M[rr][cc] % p:
                    f = M[rr][cc]; M[rr] = [(M[rr][t]-f*M[r][t]) % p for t in range(C)]
            r += 1
            if r == R: break
        return r
    return rank(False), rank(True), ncol


if __name__ == "__main__":
    for (n, d) in [(1, 3), (2, 5)]:                 # q = 1/3, 2/5 (generic, non-square)
        B = build(n, d)
        basis = [B['g'], B['sh'](B['g'], 1), B['th'](B['g']),
                 B['sh'](B['th'](B['g']), 1), B['dg'], B['sh'](B['dg'], 1)]
        for name, tgt in [("theta^2 G", B['th'](B['th'](B['g']))), ("delta^2 G", B['d2g'])]:
            rA, rAug, nc = in_module(basis, tgt)
            print(f"q={n}/{d}  {name}: rank(A)={rA} rank([A|t])={rAug} -> "
                  + ("IN module" if rA == rAug else "ESCAPES module"))
