"""
Verify the moment-bound claims underlying the J <= exp((W^2/2)(I0(2rho)-1)) proof.

G(psi)=Im(e^{rho e^{i psi}})=sum_{n>=1}(rho^n/n!) sin(n psi), psi~Unif(-pi,pi).
sigma^2 = E[G^2] = (1/2) sum_n (rho^n/n!)^2 = (1/2)(I0(2rho)-1).

(6) SUB-GAUSSIAN PROXY 2 sigma^2 (colleague's PROVED route):
     E[G^{2k}] <= (2k)!/(2^k k!) (2 sigma^2)^k    (claim: worst ratio EXACTLY 0.5)
(1b) PURE-VARIANCE (colleague says FALSE at rho=2,k=2):
     E[G^{2k}] <= (2k)!/(2^k k!) sigma^{2k}
(1a) FALSE GENERAL FACTORIZATION counterexample c=(1.37,1.94,1.45,1.06,1.53):
     E[e^{sum c_n sin n psi}] / prod I0(c_n) = 1.47 > 1
"""
import mpmath as mp
mp.mp.dps = 30

def Emoment(rho, k, M=6000):
    # E[G^{2k}], G=sum (rho^n/n!) sin(n psi)
    cn = [mp.mpf(0)] + [rho**n/mp.factorial(n) for n in range(1, 60)]
    s = mp.mpf(0)
    for q in range(M):
        psi = -mp.pi + 2*mp.pi*mp.mpf(q)/M
        G = sum(cn[n]*mp.sin(n*psi) for n in range(1, 60))
        s += G**(2*k)
    return s/M

print("="*68)
print("(6) sub-Gaussian: E[G^{2k}] vs (2k)!/(2^k k!)(2 sigma^2)^k  [ratio<=1?]")
print("    sigma^2=(1/2)(I0(2rho)-1)")
print("="*68)
worst = mp.mpf(0)
for rho in [mp.mpf(x) for x in ['0.3', '1', '2', '3']]:
    sig2 = (mp.besseli(0, 2*rho)-1)/2
    line = []
    for k in range(1, 8):
        E = Emoment(rho, k)
        rhs = mp.factorial(2*k)/(mp.mpf(2)**k*mp.factorial(k)) * (2*sig2)**k
        r = E/rhs
        worst = max(worst, r)
        line.append(f"k={k}:{float(r):.3f}")
    print(f"  rho={float(rho):.1f}: " + " ".join(line))
print(f"  => worst ratio = {float(worst):.4f}  (claim: <=1, approx 0.5)")

print()
print("="*68)
print("(1b) pure-variance proxy: E[G^{2k}] vs (2k)!/(2^k k!) sigma^{2k} [claim FAILS rho=2,k=2]")
print("="*68)
anyfail = False
for rho in [mp.mpf('1'), mp.mpf('2'), mp.mpf('3')]:
    sig2 = (mp.besseli(0, 2*rho)-1)/2
    for k in [2, 3]:
        E = Emoment(rho, k)
        rhs = mp.factorial(2*k)/(mp.mpf(2)**k*mp.factorial(k)) * sig2**k
        r = E/rhs
        flag = " <-- FAILS (>1)" if r > 1 else ""
        if r > 1: anyfail = True
        print(f"  rho={float(rho):.0f} k={k}: E/[(2k)!/(2^k k!) sigma^2k] = {float(r):.4f}{flag}")
print(f"  => pure-variance proxy fails somewhere: {anyfail}")

print()
print("="*68)
print("(1a) false general factorization counterexample")
print("    E[e^{sum c_n sin n psi}] / prod I0(c_n),  c=(1.37,1.94,1.45,1.06,1.53)")
print("="*68)
c = [mp.mpf(x) for x in ['1.37', '1.94', '1.45', '1.06', '1.53']]
M = 20000; s = mp.mpf(0)
for q in range(M):
    psi = -mp.pi + 2*mp.pi*mp.mpf(q)/M
    val = sum(c[n]*mp.sin((n+1)*psi) for n in range(len(c)))
    s += mp.e**val
E = s/M
prodI0 = mp.mpf(1)
for cn in c: prodI0 *= mp.besseli(0, cn)
print(f"  E[e^...] = {float(E):.5f}   prod I0(c_n) = {float(prodI0):.5f}   ratio = {float(E/prodI0):.4f}")
print(f"  => factorization {'FAILS (>1, confirms counterexample)' if E/prodI0 > 1 else 'holds'}")
