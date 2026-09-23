import mpmath as mp, numpy as np
from c1_verify import G, F, B, J3
mp.mp.dps = 90
# q_10 by bracketing
q10 = mp.findroot(B, (mp.mpf('0.99775'), mp.mpf('0.99776')), solver='anderson', tol=mp.mpf(10)**-80)
m = 10; qm = q10
Z = mp.sqrt(2*(1-qm)/qm)
print("q_10 =", mp.nstr(qm, 45), " |B|=", mp.nstr(abs(B(qm)), 3),
      " |J3_{-1/2}(Z;q^2)|=", mp.nstr(abs(J3(mp.mpf(-1)/2, Z, qm**2)), 3),
      " ref", mp.nstr(abs(J3(mp.mpf(-1)/2, Z*mp.mpf('1.01'), qm**2)), 3))
zs = 2*qm*(1-qm); N = 4000; cnt = 0; prev = G(qm, zs*mp.mpf(1e-6))
for i in range(1, N):
    v = G(qm, zs*mp.mpf(i)/N)
    if v*prev < 0: cnt += 1
    prev = v
print("  zeros of G(q_10,.) strictly below z*:", cnt, "(expect 9);  eps*pi^2*19^2/8 =",
      mp.nstr((1-qm)*mp.pi**2*361/8, 12))
dB = mp.diff(B, qm); dFl = mp.diff(lambda l: F(l, qm), 1)
print("  B'(q_10)=", mp.nstr(dB, 8), " dlambda/dq=", mp.nstr(-dB/dFl, 8))

# Fredholm determinant identity det(I - lam S(q)) = F(lam,q), S = D^{1/2} K D^{1/2}
print("\n== Fredholm determinant / spectrum checks (double precision, numpy) ==")
for q in [0.3, 0.6, 0.8]:
    n = int(np.ceil(np.log(1e-18)/np.log(q))) + 10
    s = np.arange(n)
    D = 2*q**(1+s)
    K = q**np.maximum.outer(s, s)
    S = np.sqrt(D)[:, None]*K*np.sqrt(D)[None, :]
    mu = np.sort(np.linalg.eigvalsh(S))[::-1]
    for lam in [0.5, 2.7, 1.0, complex(1.5, 2.0)]:
        det = np.linalg.det(np.eye(n) - lam*S)
        Fv = complex(F(mp.mpc(lam), mp.mpf(q)))
        print(f"  q={q} lam={lam}: det(I-lam S)={det:.15g}  F={Fv:.15g}  |diff|={abs(det-Fv):.2e}")
    # eigenvalues vs pencil zeros lambda_k = z_k/(2q(1-q))
    lams = []
    qq = mp.mpf(q)
    f = lambda l: F(l, qq)
    # scan for sign changes
    grid = [mp.mpf(1/mu[0])*mp.mpf(0.5)*(1.02)**i for i in range(0, 700)]
    prev = f(grid[0])
    for a, b in zip(grid, grid[1:]):
        v = f(b)
        if v*prev < 0:
            lams.append(mp.findroot(f, (a, b), solver='anderson'))
            if len(lams) == 4: break
        prev = v
    print(f"  q={q}: 1/mu_k (numpy) =", [f"{1/x:.12g}" for x in mu[:4]])
    print(f"        pencil zeros    =", [mp.nstr(x, 12) for x in lams])
    # bulk: det(I - q S) = S_e = F(q,q)
    Se = mp.nsum(lambda j: (-2*(1-qq))**j*qq**(j*(j+1))/mp.qp(qq, qq, 2*j), [0, mp.inf])
    print(f"  q={q}: det(I-qS)={np.linalg.det(np.eye(n)-q*S):.15g}  S_e={mp.nstr(Se,15)}  F(q,q)={mp.nstr(F(qq,qq),15)}")
    # trace = 2q/(1-q^2)
    print(f"  trace S={np.trace(S):.15g} vs 2q/(1-q^2)={2*q/(1-q*q):.15g}; sum 1/lambda_k over found = {sum(1/float(x) for x in lams):.6g}")

# sine side: H(q,z)=sum (-1)^k q^{k^2}(1-q) z^k/(q;q)_{2k+1}; zeros vs q*j_{k,1/2}(q^2)^2
print("\n== normalisation of the sine side ==")
q = mp.mpf('0.6')
H = lambda z: mp.nsum(lambda k: (-1)**k*q**(k*k)*(1-q)*z**k/mp.qp(q, q, 2*k+1), [0, mp.inf])
Gz = lambda z: G(q, z)
j_half = [mp.findroot(lambda x: J3(mp.mpf(1)/2, x, q**2), g) for g in [2.0, 3.6]]
j_mhalf = [mp.findroot(lambda x: J3(mp.mpf(-1)/2, x, q**2), g) for g in [1.0, 2.5]]
print("  j_{k,-1/2}(q^2):", [mp.nstr(x, 15) for x in j_mhalf], " G(q, q^2 j^2):", [mp.nstr(Gz(q**2*x**2), 3) for x in j_mhalf])
print("  j_{k,+1/2}(q^2):", [mp.nstr(x, 15) for x in j_half], " H(q, q j^2):", [mp.nstr(H(q*x**2), 3) for x in j_half])
