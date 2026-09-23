"""Room C seat C1: verify travel poles = zeros of classical Hahn-Exton / KS q-cosine,
pencil identification, index match, Fredholm determinant identity. Scalar mpmath only."""
import mpmath as mp, sys

def G(q, z):  # 1phi1(0;q;q^2,z) = sum (-1)^k q^{k(k-1)} z^k/(q;q)_{2k}
    s = mp.mpf(0); t = mp.mpf(1); k = 0; poch = mp.mpf(1)
    while True:
        term = (-1)**k * q**(k*(k-1)) * z**k / poch
        s += term
        if k > 5 and abs(term) < mp.mpf(10)**(-mp.mp.dps-5) * (1+abs(s)): break
        poch *= (1-q**(2*k+1))*(1-q**(2*k+2)); k += 1
    return s

def F(lam, q):  # pencil: sum (-2 lam (1-q))^k q^{k^2}/(q;q)_{2k} = G(q, 2 lam q (1-q))
    return G(q, 2*lam*q*(1-q))

def B(q): return F(1, q)

def qpoch_inf(a, q):
    p = mp.mpf(1); k = 0
    while True:
        f = a*q**k
        if abs(f) < mp.mpf(10)**(-mp.mp.dps-5): break
        p *= (1-f); k += 1
    return p

def J3(nu, x, Q):  # Koelink-Swarttouw normalisation, base Q
    # J_nu^(3)(x;Q) = x^nu (Q^{nu+1};Q)_inf/(Q;Q)_inf * 1phi1(0;Q^{nu+1};Q;Q x^2)
    b = Q**(nu+1)
    s = mp.mpf(0); k = 0; num = mp.mpf(1)  # (Q;Q)_k (b;Q)_k
    while True:
        term = (-1)**k * Q**(k*(k-1)/2) * (Q*x*x)**k / num
        s += term
        if k > 5 and abs(term) < mp.mpf(10)**(-mp.mp.dps-5)*(1+abs(s)): break
        num *= (1-Q**(k+1))*(1-b*Q**k); k += 1
    return x**nu * qpoch_inf(b, Q)/qpoch_inf(Q, Q) * s

def main():
    mp.mp.dps = 90
    # locate q_1..q_10 : w = sqrt(2/tau), guess tau ~ 8/(pi^2 (2m-1)^2) corrected
    guesses = [mp.mpf('0.44945363'), mp.mpf('0.91348664'), mp.mpf('0.96804175'), mp.mpf('0.98357902'),
               mp.mpf('0.99003740'), mp.mpf('0.99332100'), mp.mpf('0.99521395'), mp.mpf('0.99640323'),
               mp.mpf('0.99719876'), mp.mpf('0.99775693')]
    qs = []
    for g in guesses:
        qm = mp.findroot(B, g, tol=mp.mpf(10)**(-80))
        qs.append(qm)
    print("== travel poles (45 digits) and checks ==")
    for m, qm in enumerate(qs, 1):
        Z = mp.sqrt(2*(1-qm)/qm)
        Q = qm**2
        j = J3(mp.mpf(-1)/2, Z, Q)          # classical Hahn-Exton J_{-1/2}^{(3)}(Z;q^2)
        # scale for relative size: compare with |J3| at nearby generic point
        jref = abs(J3(mp.mpf(-1)/2, Z*mp.mpf('1.01'), Q))
        # KS q-cosine cos(z;q^2)= sum (-1)^j q^{j^2+j} z^{2j}/(q;q)_{2j} = G(q, q^2 z^2)
        cosZ = G(qm, qm**2*Z**2)
        # index: zeros of G(q_m, .) below/at z* = 2q(1-q); lambda_k = z_k/(2q(1-q))
        zstar = 2*qm*(1-qm)
        # count sign changes of G(q_m,z) on (0, 1.0000001 z*) with fine grid
        N = 400*m
        cnt = 0; prev = G(qm, zstar*mp.mpf(1e-6))
        for i in range(1, N+1):
            z = zstar*(mp.mpf(i)/N)*(1-mp.mpf(10)**-30) if i == N else zstar*mp.mpf(i)/N
            v = G(qm, z)
            if v*prev < 0: cnt += 1
            prev = v
        # next zero above z*: lambda_{m+1}
        # derivative of B at q_m (simplicity of pole as a zero in q)
        dB = mp.diff(B, qm)
        dFl = mp.diff(lambda l: F(l, qm), 1)
        dlam_dq = -dB/dFl  # d lambda_m/dq at the crossing
        eps = 1-qm
        print(f"m={m} q_m={mp.nstr(qm,45)}")
        print(f"   |B|={mp.nstr(abs(B(qm)),3)} |J3_(-1/2)(Z;q^2)|={mp.nstr(abs(j),3)} (ref {mp.nstr(jref,3)}) |cos(Z;q^2)|={mp.nstr(abs(cosZ),3)}")
        print(f"   zeros of G(q_m,.) in (0,z*) [strictly below z*]: {cnt} (expect m-1={m-1});"
              f"  B'(q_m)={mp.nstr(dB,8)}  dlambda_m/dq={mp.nstr(dlam_dq,8)}")
        print(f"   eps*pi^2(2m-1)^2/8 = {mp.nstr(eps*mp.pi**2*(2*m-1)**2/8,12)}")
    return qs

if __name__ == '__main__':
    main()
