"""
INDEPENDENT adversarial verification of the D5 assembly skeleton.
Everything built from scratch. No reuse of the script under test.

Claims under test:
 (B/C) pref := 2 q^3 / (3 (1-q^3)) = 2/(9 tau) (1 + O(tau)).
 (D)   Y3(1/q)_lead = (3/sqrt2) tau^{3/2} sin w   [ Y3(1/q)/(tau^{3/2} sin w) -> 3/sqrt2 ].
       cos W = (19/18) sqrt(tau/2) sin w + O(tau^{3/2}).
 (E)   (Y3(1/q) - (3/sqrt2) tau^{3/2} sin w)/tau^{5/2}  BOUNDED.
 (F)   E = (1/2)(w-W)^2 sin w sin(w-W),  E_lead = tau^{3/2}/(4 sqrt2) sin w,
       P12/E -> 1,  |P12|/tau^{3/2} -> 1/(4 sqrt2) = 0.176777.
 (G)   fact-9 cross check Y3(1/q)/[N0 (1/q)^{3/2} J_{3/2}(W/q)] -> 36/35.
 GATE: |P12| <= C tau^{3/2}, C < 1/sqrt2.
"""
import mpmath as mp

def setdps(tau):
    mp.mp.dps = 40 + int(2.5 * float(mp.sqrt(2/tau)))

# ----- INDEPENDENT cocycle (matches the stated recursion in fact 1) -----
def cocycle(q, N):
    x = mp.mpf(0); y = mp.mpf(1); X = mp.mpf(1); Y = mp.mpf(0); qn = mp.mpf(1)
    for n in range(1, N + 1):
        qn *= q; q2n = qn*qn; q3n = q2n*qn
        nx = x*(1 + 2*q2n) - 2*y*qn
        ny = 2*x*q3n + y*(1 - 2*q2n)
        nX = X*(1 + 2*q2n) - 2*Y*qn
        nY = 2*X*q3n + Y*(1 - 2*q2n)
        x, y, X, Y = nx, ny, nX, nY
    return Y, y   # P12, Se

# ----- INDEPENDENT Hahn-Exton d_k via the stated ratio recursion (fact 2) -----
def d_list(q, K):
    d = [mp.mpf(1)]
    for k in range(K):
        # d_{k+1}/d_k = -2(1-q) q^{2k+4} / [(1-q^{2k+2})(1-q^{2k+5})]
        num = -2*(1-q)*q**(2*k+4)
        den = (1 - q**(2*k+2))*(1 - q**(2*k+5))
        d.append(d[-1]*num/den)
    return d

def Y3_at(q, K, x):
    # Y3(x) = sum_k d_k x^{2k+3}
    d = d_list(q, K)
    return mp.fsum(d[k]*x**(2*k+3) for k in range(K+1))

def Kfor(tau):
    return int(16/float(mp.sqrt(tau))) + 100

with open('poles.txt') as f:
    POLES = [mp.mpf(l.strip()) for l in f if l.strip()]

print("Loaded %d poles. POLES[0]=%.6f" % (len(POLES), float(POLES[0])))

# First, verify the pole condition Sig_t(q_m)=1 to make sure poles.txt is indexed as I think.
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(q, J):
    s = mp.mpf(0); prod = mp.mpf(1)
    for j in range(J):
        s += Aq(1+2*j, q)*prod
        prod *= Cq(1+2*j, q)
    return s

print("\n[pole check] Sig_t(q_m) should = 1")
for m in [0,1,2,5]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau)
    J = int(60/float(mp.sqrt(tau)))+200
    print("  m=%d tau=%.4e Sig_t-1=%.3e" % (m, float(tau), float(Sig_t(q,J)-1)))

print("\n" + "="*120)
print(" m    tau         P12_cocycle      P12_closed       relerr   |Y3dir-Y3stab|rel  identity_resid")
print("="*120)
for m in [1,3,6,12,25,40]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau); K = Kfor(tau)
    N = int(95/(1-q))
    Pk, Se = cocycle(q, N)
    # closed form P12 = (2 q^3/(1-q^3)) Y3(1)
    Y3_1 = Y3_at(q, K, mp.mpf(1))
    P12_closed = 2*q**3/(1-q**3)*Y3_1
    # Y3(1/q): direct power series vs stable route 3 Y3(1) - (1-q^-3) Se
    Y3invq_dir = Y3_at(q, K, 1/q)
    Y3_1_fromP = (1-q**3)*Pk/(2*q**3)
    Y3invq_stab = 3*Y3_1_fromP - (1 - q**(-3))*Se
    ident = 2*q**3/(3*(1-q**3))*Y3invq_stab - mp.mpf(2)/3*Se - Pk
    print(" %2d  %.4e  %+.10e  %+.10e  %.1e  %.2e            %.2e"
          % (m, float(tau), float(Pk), float(P12_closed),
             float(abs((Pk-P12_closed)/Pk)),
             float(abs((Y3invq_dir-Y3invq_stab)/Y3invq_stab)),
             float(abs(ident))))

print("\n" + "="*120)
print("CONSTANT EXTRACTION (independent). Ratios should converge to the claimed constants.")
print("="*120)
print(" m    tau        pref*9tau/2   (1-q^3)/3tau   Y3inv/((3/sqrt2)t^1.5 sw)  cosW/(sqrt(t/2)sw)  P12/E   |P12|/t^1.5  Y3inv/[N0 q^-1.5 J32(W/q)]")
sup = mp.mpf(0)
data = []
for m in [1,2,3,5,6,8,10,12,16,20,25,30,40,50,60,79]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau); K = Kfor(tau)
    N = int(95/(1-q))
    Pk, Se = cocycle(q, N)
    w = mp.sqrt(2/tau); W = w*mp.exp(-tau/2); sinw = mp.sin(w); cosW = mp.cos(W)
    Y3invq = 3*((1-q**3)*Pk/(2*q**3)) - (1-q**(-3))*Se
    pref = 2*q**3/(3*(1-q**3))
    r_pref = pref*9*tau/2
    r_q3 = (1-q**3)/(3*tau)
    r_Y3 = Y3invq/((3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw)
    r_cosW = cosW/(mp.sqrt(tau/2)*sinw)
    E = mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    r_E = Pk/E
    r_gate = abs(Pk)/tau**mp.mpf('1.5')
    if r_gate > sup: sup = r_gate
    # fact 9 cross check
    N0 = 3*2**mp.mpf('1.5')*mp.sqrt(mp.pi)/(4*W**mp.mpf('1.5'))
    J32 = mp.besselj(mp.mpf(3)/2, W/q)
    r_fact9 = Y3invq/(N0*(1/q)**mp.mpf('1.5')*J32)
    data.append((m, float(tau), float(r_Y3), float(r_cosW), float(r_E), float(r_gate)))
    print(" %2d  %.3e  %.8f    %.8f     %.8f                 %.8f          %.6f  %.7f    %.7f"
          % (m, float(tau), float(r_pref), float(r_q3), float(r_Y3), float(r_cosW),
             float(r_E), float(r_gate), float(r_fact9)))

print("\nTARGET CONSTANTS:")
print("  3/sqrt2        = %.8f" % float(3/mp.sqrt(2)))
print("  19/18          = %.8f" % (19/18))
print("  36/35          = %.8f" % (36/35))
print("  1/(4 sqrt2)    = %.8f" % float(1/(4*mp.sqrt(2))))
print("  1/sqrt2 (gate) = %.8f" % float(1/mp.sqrt(2)))
print("  sup_m |P12|/tau^{3/2} = %.7f" % float(sup))
