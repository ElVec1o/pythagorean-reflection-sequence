#!/usr/bin/env python3
"""
DECISIVE: is the form factor rho_j = t_j/that_j completely monotone (a Hausdorff moment
sequence rho_j = int_0^1 x^j dmu(x), mu>=0)?  If YES, then
   S_1(q) = sum_i (-1)^{i-1} w^{2i}/(2i)! rho_{i-1} = int_0^1 (1-cos(w sqrt x))/x dmu(x),
a RIGOROUS integral rep (oscillation INSIDE the integral) => lem:cos by Laplace at x=1,
with NO divergent majorant. This would CLOSE lem:cos (hence V/G_0 transcendence).

Tests for complete monotonicity of (rho_j):
 (1) finite differences: (-1)^k (Delta^k rho)_j >= 0 for all k,j  (Hausdorff CM criterion).
 (2) Hankel PSD: H_n=(rho_{i+k})_{i,k<=n} and shifted H'_n=(rho_{i+k+1}) both PSD (moment on [0,1]).
 (3) VERIFY the integral rep numerically: reconstruct S_1 from int(1-cos(w sqrt x))/x dmu and compare.
"""
import mpmath as mp
mp.mp.dps=60

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))

def rho_seq(tau, J=40):
    q=mp.e**(-tau)
    # S_1 = sum_j (-1)^j t_j,  t_j = alpha_{1+2j} prod_{i<j}|gamma_{1+2i}|
    t=[]; prod=mp.mpf(1)
    for j in range(J):
        tj=alpha(1+2*j,q)*prod
        t.append(tj)
        prod*=abs(gamma(1+2*j,q))
    that=[(2/tau)**(j+1)/mp.factorial(2*j+2) for j in range(J)]
    rho=[t[j]/that[j] for j in range(J)]
    return rho, q

for tau in [mp.mpf('0.1'), mp.mpf('0.05')]:
    rho,q=rho_seq(tau, J=36)
    w=mp.sqrt(2/tau)
    print(f"\n=== tau={float(tau)}, w={float(w):.3f} ===")
    print("rho_j (j=0..10):", [mp.nstr(r,6) for r in rho[:11]])
    print("rho in (0,1], decreasing:", all(0<r<=1+mp.mpf('1e-9') for r in rho), all(rho[i]>=rho[i+1]-mp.mpf('1e-12') for i in range(len(rho)-1)))
    # (1) complete monotonicity via finite differences (-1)^k Delta^k rho_j >= 0
    def diffs(seq,k):
        s=list(seq)
        for _ in range(k):
            s=[s[i]-s[i+1] for i in range(len(s)-1)]   # forward (-Delta): (-Delta)^k = (-1)^k Delta^k
        return s
    cm_ok=True; firstbad=None
    for k in range(0,9):
        dk=diffs(rho,k)   # this is (-1)^k Delta^k rho (since we use s[i]-s[i+1])
        m=min(dk[:len(dk)-2]) if len(dk)>2 else min(dk)
        if m< -mp.mpf('1e-25'):
            cm_ok=False
            if firstbad is None: firstbad=(k,mp.nstr(m,4))
    print(f"(1) completely monotone ((-1)^k Delta^k rho >=0 for k<=8): {cm_ok}" + (f"  firstbad k={firstbad}" if firstbad else ""))
    # (2) Hankel PSD (Hausdorff moment) -- leading minors of H and H'
    def hankel_psd(seq,n,shift=0):
        import mpmath
        ok=True
        for sz in range(1,n+1):
            M=mp.matrix(sz,sz)
            for i in range(sz):
                for j in range(sz):
                    M[i,j]=seq[i+j+shift]
            if mp.det(M) < -mp.mpf('1e-30'): ok=False
        return ok
    print(f"(2) Hankel H PSD (size<=8): {hankel_psd(rho,8,0)};  shifted H' PSD: {hankel_psd(rho,8,1)}")
    # (3) reconstruct S_1 via integral rep IF CM: get mu from rho as a measure on [0,1].
    #     Quick proxy: S_1 = sum_i (-1)^{i-1} w^{2i}/(2i)! rho_{i-1}; vs direct S_1.
    S1_direct=sum((-1)**j * (sum_t) for j,sum_t in [(0,0)])  # placeholder
    S1=sum((-1)**(i-1)*w**(2*i)/mp.factorial(2*i)*rho[i-1] for i in range(1,len(rho)))
    # compare to actual S_1 from telescoping
    def Sb1(q,J=4000):
        tot=mp.mpf(0); prod=mp.mpf(1)
        for j in range(J):
            tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
            if abs(prod)<mp.mpf(10)**(-90) and j>40: break
        return tot
    print(f"(3) S_1 via rho-sum={mp.nstr(S1,10)}  vs telescoped S_1={mp.nstr(Sb1(q),10)}  (1-cos w={mp.nstr(1-mp.cos(w),8)})")
