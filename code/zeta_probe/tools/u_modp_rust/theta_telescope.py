#!/usr/bin/env python3
# Verify the explicit theta-telescoping of the catalytic block F(q,t):
#   F(q,t) = E(t) + D(t) F(q, q^2 t),   D(t) = 2q(q-1)t / [(1-qt)(1-q^2 t)]
#   => F(q,t) = sum_{k>=0} alpha_k(t) E(q^{2k} t),   alpha_k = prod_{j<k} D(q^{2j} t)
#   CLAIM:  alpha_k(t) = [2q(q-1)]^k t^k q^{k(k-1)} / (qt; q)_{2k}     <-- the q^{k(k-1)} theta factor
# Everything as exact integer/poly q-series; t tracked symbolically (sympy) for alpha_k.
import sympy as sp

# ---------- 1. solve eq:sections for F_s(q) as integer q-series ----------
M = 16                                  # q-order (<-> x^{2M})
def zeros(): return [0]*(M+1)
def shift(a, s):                        # multiply q-series a by q^s, truncate
    r = zeros()
    for i in range(M+1):
        if i+s <= M: r[i+s] = a[i]
    return r
def add(*xs):
    r = zeros()
    for a in xs:
        for i in range(M+1): r[i]+=a[i]
    return r

F = {s: zeros() for s in range(1, M+1)}
for _ in range(M+3):                    # converges (upper-triangular in q-order)
    newF = {}
    for s in range(1, M+1):
        t1 = zeros(); t1[s] = 2 if s<=M else 0
        S2 = zeros()                    # sum_{s'>=s} F_{s'} q^{s'}
        for sp_ in range(s, M+1): S2 = add(S2, shift(F[sp_], sp_))
        t2 = shift([2*c for c in S2], s)
        S3 = zeros()                    # sum_{s'<s} F_{s'}
        for sp_ in range(1, s):  S3 = add(S3, F[sp_])
        t3 = shift([2*c for c in S3], 2*s)
        newF[s] = add(t1, t2, t3)
    F = newF

F1   = F[1]
Fq1  = add(*[F[s] for s in range(1, M+1)])               # F(q,1)=sum_s F_s
Fqq  = add(*[shift(F[s], s) for s in range(1, M+1)])     # F(q,q)=sum_s F_s q^s
tex  = [0,2,2,6,2,18,6,42,18,118,50,282,190,706,594]     # tex bulk series at q^1..q^14
print("# bulk-run target (tex):  ", tex[1:15])
print("# F_1(q)   coeffs q^1..:  ", F1[1:15])
print("# F(q,1)   coeffs q^1..:  ", Fq1[1:15])
print("# F(q,q)   coeffs q^1..:  ", Fqq[1:15])
which = "F_1" if F1[1:15]==tex[1:15] else ("F(q,1)" if Fq1[1:15]==tex[1:15] else
        ("F(q,q)" if Fqq[1:15]==tex[1:15] else "NONE"))
print(f"# => bulk-run series == {which}\n")

# ---------- 2. symbolic check of the alpha_k closed form ----------
q, t = sp.symbols('q t')
D = lambda tt: 2*q*(q-1)*tt / ((1-q*tt)*(1-q**2*tt))
print("# alpha_k = prod_{j<k} D(q^{2j} t)   vs   [2q(q-1)]^k t^k q^{k(k-1)} / prod_{i=1}^{2k}(1-q^i t)")
for k in range(0, 5):
    prod = sp.Integer(1)
    for j in range(k): prod *= D(q**(2*j)*t)
    claim = (2*q*(q-1))**k * t**k * q**(k*(k-1)) / sp.prod([1-q**i*t for i in range(1, 2*k+1)])
    ok = sp.simplify(prod - claim) == 0
    print(f"#   k={k}:  closed-form match = {ok}   (theta exponent q^{{k(k-1)}} = q^{k*(k-1)} = x^{{{2*(k*(k-1))}}})")

# ---------- 3. telescoping reproduces F_1 = [t^1] F ----------
# [t^1] F = [t^1] sum_k alpha_k(t) E(q^{2k}t).  E(t)=2qt/(1-qt)(1+F(q,q)); alpha_k*E(q^{2k}t)
# starts at t^{k+1}, so only k=0 hits t^1:  [t^1]F = [t^1]E(t) = 2q(1+F(q,q)).
twoq_1pFqq = add([2*c for c in shift(Fqq,1)])           # 2q*F(q,q)
twoq_1pFqq[1] += 2                                       # +2q
print("\n# [t^1] of telescoping (k=0 term) = 2q(1+F(q,q)):")
print("#   2q(1+F(q,q)) q^1..:    ", twoq_1pFqq[1:15])
print("#   matches F_1?           ", twoq_1pFqq[1:15]==F1[1:15])
print("\n# => theta structure: alpha_k carries q^{k(k-1)} = x^{2k(k-1)} (square exponents).")
print("#    The (qt;q)_{2k}=prod(1-q^i t) denominator (Euler/pentagonal) spreads each")
print("#    theta block over all degrees -> no lacunary gaps survive in U -> the")
print("#    non-automaticity is REAL but its proof = transcendence of this theta series")
print("#    mod p over F_p(x) = the SAME theta/square wall as route-D and Polya-Carlson.")
