"""
D4 step 3: Fit log rho^T_j (travel block) as a polynomial in j with tau-scaled coeffs.
We posit  log rho^T_j = b1*tau*(j+1) + b2*tau^2*(j+1)^2 + b3*tau^2*(j+1)^3 + ...
Actually let's be agnostic: fit log rho_j = sum_p e_p * j^p for small j at fixed tau,
then read tau-scaling of each e_p.

Compare to the BULK S_1 form factor (alpha_k, gamma_k) which the tex says has
  log rho^bulk_j = -(j+1)tau - (1/9)tau^2 j^3 + O(...).

Goal: confirm travel has NO O(tau) linear term, and pin its cubic coefficient,
then map to c_T.
"""
import mpmath as mp

KSTART = 1
def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))
# bulk
def alpha(k, q): return 2 / (q**(-(k+1)) - 1)   # = 2/(e^{(k+1)tau}-1)
def gamma(k, q): return alpha(k+1, q) - alpha(k, q)

def travel_terms(q, J):
    ts = []; prod = mp.mpf(1)
    for j in range(J):
        kk = KSTART + 2 * j
        ts.append(Aq(kk, q) * prod); prod *= -Cq(kk, q)
    return ts

def bulk_terms(q, J):
    ts = []; prod = mp.mpf(1)
    for j in range(J):
        kk = 1 + 2 * j
        ts.append(alpha(kk, q) * prod); prod *= -gamma(kk, q)
    return ts

def hat_t(j, tau): return (2 / tau) ** (j + 1) / mp.factorial(2 * j + 2)

def fit_logrho(terms_fn, label):
    print(f"\n###### {label} ######")
    # Use small tau; fit log rho_j in j with a polynomial, examine tau-scaling of coeffs.
    res = {}
    for tau in [mp.mpf('0.004'), mp.mpf('0.001'), mp.mpf('0.00025')]:
        q = mp.e ** (-tau)
        J = 30
        ts = terms_fn(q, J)
        lr = [mp.log(ts[j] / hat_t(j, tau)) for j in range(J)]
        # fit lr[j] ~ c1*j + c2*j^2 + c3*j^3 + c4*j^4 + c5*j^5 using j=1..12 (window where lr is small)
        npt = 12
        A = mp.matrix(npt, 5)
        b = mp.matrix(npt, 1)
        for r in range(npt):
            j = r + 1
            for p in range(5):
                A[r, p] = mp.mpf(j) ** (p + 1)
            b[r, 0] = lr[j]
        # least squares: solve A^T A x = A^T b
        AT = A.T
        coef = mp.lu_solve(AT * A, AT * b)
        c1, c2, c3, c4, c5 = [coef[i, 0] for i in range(5)]
        res[tau] = (c1, c2, c3)
        print(f"tau={mp.nstr(tau,5)}: c1={mp.nstr(c1,6)} c2={mp.nstr(c2,6)} c3={mp.nstr(c3,6)}")
        print(f"          c1/tau={mp.nstr(c1/tau,6)}  c2/tau^2={mp.nstr(c2/tau**2,6)}  c3/tau^2={mp.nstr(c3/tau**2,6)}")
    return res

if __name__ == "__main__":
    mp.mp.dps = 90
    fit_logrho(bulk_terms,   "BULK S_1   (expect c1/tau->-1, c3/tau^2->-1/9=-0.1111)")
    fit_logrho(travel_terms, "TRAVEL Sig_1")
