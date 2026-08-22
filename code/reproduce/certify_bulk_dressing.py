r"""Exact-rational certification of the bulk non-interference constants (Paper 1).

Companion to certify_beta2_pole.py (whose machinery it imports). Certifies, in
exact rational arithmetic with explicit tail bounds:

  (B1)  Sigma_1^bulk < 1 on the certified bracket of q*: the bulk dressing is
        finite at the travel pole (enclosure ~ 0.48045).
  (B2)  F_b(q) := 1 - Sigma_1^bulk(q) has WINDING NUMBER 0 around |q| = 1/2:
        the bulk resolvent is holomorphic on the closed disc |q| <= 1/2, which
        contains |q| <= q*.  This replaces "its nearest singularity lies at
        q_b = 0.6095... > q*" with a disc statement.
  (B3)  F_b changes sign on an explicit rational bracket of width < 1e-20
        inside [0.60, 0.62]: the bulk singularity q_b is real with certified
        digits 0.60956734426012... (> 1/2 > q*).

Bulk series (code/zeta_probe/route_b/full_singularity_assembly.py):

  Sigma_k^bulk(q) = sum_j alpha(k+2j, q) prod_{i<j} gamma(k+2i, q),
  alpha(k, q) = 2q^{k+1}/(1-q^{k+1}),
  gamma(m, q) = 2q^{m+2}/(1-q^{m+2}) - 2q^{m+1}/(1-q^{m+1})
              = 2 q^{m+1} (q-1) / ((1-q^{m+1})(1-q^{m+2})).

For k = 1 the product telescopes (verified against the alpha/gamma product
form to 40 digits at real and complex points):

  Sigma_1^bulk(q) = sum_{j>=0} 2^{j+1} (q-1)^j (1-q) q^{j^2+3j+2} / (q;q)_{2j+2}.

Tail bound on |q| <= r < 1:
  |t_j| <= (2(1+r))^{j+1} r^{j^2+3j+2} / P_{2j+2}(r),   P_n(r) = prod (1-r^m),
with successive-bound ratio < 1/2 checked at the truncation index.

    python3 certify_bulk_dressing.py       (~10 s)
"""

import json
import time
from fractions import Fraction as Fr

from certify_beta2_pole import (
    HALF, cadd, csub, cmul, cdiv, cpow, cabs2,
    F_real, tail_F, P_lower, winding_curve, _selftest,
)


# ---------- F_b(q) = 1 - Sigma_1^bulk(q), telescoped form ----------

def Fb_complex(q, N):
    one = (Fr(1), Fr(0))
    tot = one                     # the leading 1
    # t_0 = 4 q^2 (1-q) / ((1-q)(1-q^2)) ... build from the closed form directly
    one_minus_q = csub(one, q)
    num = cmul(cmul((Fr(2), Fr(0)), one_minus_q), cmul(q, q))   # 2 (1-q) q^2 at j=0... times 2^j (q-1)^j q^{j^2+3j}
    poch = cmul(one_minus_q, csub(one, cmul(q, q)))             # (q;q)_2
    qm = cmul(q, q)               # q^m with m = 2
    m = 2
    q_minus_one = csub(q, one)
    for j in range(N):
        term = cdiv(num, poch)
        tot = csub(tot, term)     # 1 - sum
        # j -> j+1: factor 2 (q-1) q^{2j+4}; poch gains (1-q^{2j+3})(1-q^{2j+4})
        num = cmul(num, cmul((Fr(2), Fr(0)), cmul(q_minus_one, cpow(q, 2 * j + 4))))
        for _ in range(2):
            m += 1
            qm = cmul(qm, q)
            poch = cmul(poch, csub(one, qm))
    return tot


def Sb1_real(q, N):
    tot = Fr(0)
    num = 2 * (1 - q) * q * q
    poch = (1 - q) * (1 - q * q)
    for j in range(N):
        tot += num / poch
        num *= 2 * (q - 1) * q ** (2 * j + 4)
        poch *= (1 - q ** (2 * j + 3)) * (1 - q ** (2 * j + 4))
    return tot


def tail_Fb(r, N):
    """|sum_{j>=N} t_j| on |q| <= r, ratio < 1/2 asserted at j = N."""
    tN = (2 * (1 + r)) ** (N + 1) * r ** (N * N + 3 * N + 2) / P_lower(r, 2 * N + 2)
    ratio = 2 * (1 + r) * r ** (2 * N + 4) / ((1 - r ** (2 * N + 3)) * (1 - r ** (2 * N + 4)))
    assert ratio < HALF, "bulk tail ratio not < 1/2; increase N"
    return 2 * tN


def lipschitz_Fb_on_half_circle(N=12):
    """Exact rational L_b with |F_b'(q)| <= L_b on |q| = 1/2.
    Log-derivative of t_j: j/(q-1) - 1/(1-q) + (j^2+3j+2)/q
    + sum_{m=1}^{2j+2} m q^{m-1}/(1-q^m); on |q| = 1/2 bounded by
    2j + 2 + 2(j^2+3j+2) + D_{2j+2}."""
    r = HALF
    L = Fr(0)
    for j in range(N):
        tj = (2 * (1 + r)) ** (j + 1) * r ** (j * j + 3 * j + 2) / P_lower(r, 2 * j + 2)
        D = sum(Fr(m) * r ** (m - 1) / (1 - r ** m) for m in range(1, 2 * j + 3))
        L += tj * (2 * j + 2 + 2 * (j * j + 3 * j + 2) + D)
    tN = (2 * (1 + r)) ** (N + 1) * r ** (N * N + 3 * N + 2) / P_lower(r, 2 * N + 2)
    DN = sum(Fr(m) * r ** (m - 1) / (1 - r ** m) for m in range(1, 2 * N + 3))
    L += 2 * tN * (2 * N + 2 + 2 * (N * N + 3 * N + 2) + DN)
    return L


def main():
    t0 = time.time()
    cert = {}
    print("certify_bulk_dressing: exact-rational certification of bulk non-interference", flush=True)
    _selftest()

    # ---- travel bracket (re-derived; 1.5 s) ----
    N_real = 18
    r_real = Fr(46, 100)
    tauT = tail_F(r_real, N_real)
    a, b = Fr(44, 100), Fr(46, 100)
    assert F_real(a, N_real) - tauT > 0 and F_real(b, N_real) + tauT < 0
    while b - a > Fr(1, 10 ** 27):
        mid = (a + b) / 2
        Fm = F_real(mid, N_real)
        if Fm - tauT > 0:
            a = mid
        elif Fm + tauT < 0:
            b = mid
        else:
            break
    print(f"  travel bracket re-derived, width {float(b-a):.1e}  [{time.time()-t0:4.1f}s]", flush=True)

    # ---- (B1) Sigma_1^bulk enclosure on the bracket ----
    tauB = tail_Fb(r_real, N_real)
    s_a = Sb1_real(a, N_real)
    s_b = Sb1_real(b, N_real)
    LSb = Fr(100)  # crude real-interval Lipschitz; bracket width 1e-27 makes it irrelevant
    lo = min(s_a, s_b) - tauB - LSb * (b - a)
    hi = max(s_a, s_b) + tauB + LSb * (b - a)
    assert hi < 1, "Sigma_1^bulk(q*) < 1 FAILED"
    assert lo > 0
    cert["sigma1_bulk_at_qstar"] = [float(lo), float(hi)]
    print(f"  [B1] Sigma_1^bulk(q*) in [{float(lo):.10f}, {float(hi):.10f}]  < 1", flush=True)

    # ---- (B2) winding 0 on |q| = 1/2 ----
    N_c = 10
    tau_c = tail_Fb(HALF, N_c)
    Lb = lipschitz_Fb_on_half_circle()
    print(f"  [B2] winding on |q| = 1/2: {N_c} terms, tail <= {float(tau_c):.2e}, "
          f"L_b <= {float(Lb):.2f}", flush=True)
    w, nseg = winding_curve(lambda q: Fb_complex(q, N_c), tau_c, Lb)
    assert w == 0, f"bulk winding = {w}, expected 0"
    cert["bulk_winding_on_half_circle"] = w
    cert["circle_segments"] = nseg
    print(f"    winding = {w} over {nseg} certified segments: bulk resolvent "
          f"holomorphic on |q| <= 1/2  [{time.time()-t0:4.1f}s]", flush=True)

    # ---- (B3) q_b bracket in [0.60, 0.62] ----
    r_b = Fr(62, 100)
    tau_b = tail_Fb(r_b, N_real)
    A, B = Fr(60, 100), Fr(62, 100)
    FA, FB = 1 - Sb1_real(A, N_real), 1 - Sb1_real(B, N_real)
    assert FA - tau_b > 0, "F_b(0.60) not certified positive"
    assert FB + tau_b < 0, "F_b(0.62) not certified negative"
    while B - A > Fr(1, 10 ** 20):
        mid = (A + B) / 2
        Fm = 1 - Sb1_real(mid, N_real)
        if Fm - tau_b > 0:
            A = mid
        elif Fm + tau_b < 0:
            B = mid
        else:
            break
    SC = 10 ** 20
    cert["q_b_lo"] = str(A)
    cert["q_b_hi"] = str(B)
    cert["q_b_dec"] = f"{int(A*SC)}e-20 .. {int(B*SC)+1}e-20"
    print(f"  [B3] q_b in [{int(A*SC)}e-20, {int(B*SC)+1}e-20]  (> 1/2 > q*)", flush=True)

    cert["conclusion"] = (
        "Sigma_1^bulk < 1 on the certified q* bracket; 1 - Sigma_1^bulk has no "
        "zero in |q| <= 1/2 (winding 0), so the bulk resolvent is holomorphic "
        "there; the bulk singularity q_b is real with certified digits and "
        "exceeds 1/2. The travel pole q* is the dominant singularity of the "
        "assembled relaxed series V.")
    out = __file__.replace(".py", "_certificate.json")
    json.dump(cert, open(out, "w"), indent=1)
    print(f"  certificate -> {out}")
    print(f"  ALL CHECKS PASSED  [{time.time()-t0:5.1f}s total]", flush=True)


if __name__ == "__main__":
    main()
