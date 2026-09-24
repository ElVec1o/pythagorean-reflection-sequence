# P1a: the level-q saddle asymptotic of Sigma near p/q (research programme P1, first atom)

Date: 2026-09-24. Scope: N odd (eps = 1). Nothing in the papers was edited and nothing was committed.
Every run used `perl -e 'alarm 290; exec @ARGV'`, and each run needed well under 100 MB.

**Outcome in one line.** Near a/N = p/q + theta/(qN), Sigma_N (equivalently S0 or Psi) has a leading
term that is a nonzero explicit factor, times a **quadratic Gauss sum of length 2|theta|**, times
**the same sum at level q, Sigma_q(p/q)**. So the problem renormalises exactly from level N to level q.
The leading amplitude is nonzero whenever S0(e^{2 pi i p/q}) != 0, and that is certified for q <= 150.
A full proof still needs a uniform, rigorous error bound (listed in section 5).

## 0. Reduction used
We work with Sigma of S0_lemma Lemma 1: S0 = K * Sigma, where K is an exponential and so never 0.
Also Psi = Sigma * K (1-w)^{1/2N} / G(a,N). Hence Psi != 0 <=> Sigma != 0 <=> S0 != 0 (PROVED; N not 2 mod 4 for the Psi form).
Here
  Sigma_N(a/N) = sum_{r<N} zeta^{r^2} lam^{2r} / (zeta u; zeta)_{2r},   zeta = e^{2 pi i a/N},  u = lam^2/c,  c = -2(1-zeta).

## 1. The asymptotic formula
Write zeta = zeta0 e^{i tau}, with zeta0 = e^{2 pi i p/q} and tau = 2 pi theta/(qN).
Set U = u^q and V(phi) = u e^{2 i phi}. Define
  g_m(phi) = i phi^2 - (i/q^2)[Li2(U e^{2iq phi}) - Li2(U)] - 2 pi i m phi/q,
  C(phi)   = sqrt((1-V^q)/(1-U)) * prod_{i=1}^q ((1-zeta0^i u)/(1-zeta0^i V))^{i/q},
  A(phi)   = sum_{rho<q} zeta0^{rho^2} e^{2 i rho phi} / (zeta0 V; zeta0)_{2 rho}.
Let phi_0 solve g_0' = 0, that is, 2i phi = (2/q) Log(1 - U e^{2iq phi}), and put phi_m = phi_0 + pi m/q.
g'' = 2i(1+V^q)/(1-V^q) does not depend on m. Then

  Sigma_N = (1/(q tau)) sqrt(2 pi tau / (-g'')) e^{g_0(phi_0)/tau} * sum_{m in M_theta} e^{-i pi m^2 N/(2 q theta)} C(phi_m) A(phi_m) * (1 + O(1/N)),

where M_theta = {0,...,2theta-1} for theta > 0 and {0,-1,...,2theta+1} for theta < 0.

- Derivation (HEURISTIC; a sketch, not written with error bounds):
  1. Split r = rho + qk.
  2. Factor (zeta u; zeta)_{2r} into 2k full q-blocks (each equal to 1 - U e^{iq psi} + O(tau)) and a partial block.
  3. Apply Euler–Maclaurin in k. The O(tau) block correction and the boundary term give exactly C.
  4. Apply Poisson in k. The index m labels the 2|theta| saddles in phi in [0, 2 pi theta/q].
  5. Use steepest descent.
- PROVED (algebra): g_m(phi + pi m/q) = g_0(phi) - i pi^2 m^2/q^2. So all saddles are translates of phi_0, they share |e^{g/tau}|, and their relative phase is exactly e^{-i pi m^2 N/(2 q theta)}.
- VERIFIED (exact Sigma at 30 + 0.6N/q + 30 digits against the formula; `P1a_saddle.py`). |S/pred| - 1 = O(1/N) in every family tested (moduli only; for theta < 0 the principal sqrt gives an overall sign -1):

| p/q, theta | N | S/pred |
|---|---|---|
| 1/3, 1 | 101 / 401 / 1601 | 1.00029 / 1.000072 / 1.000018 |
| 1/3, 2 | 403 / 1603 | 1.00015 / 1.000036 |
| 1/2, ±1 | 401 / 1601 | ±1.000004 / ±1.0000002 |
| 2/5, 1 and 2/5, -3 | ~1600 | 0.99995, -1.00014 |
| 3/7, 1; 1/9, 1; 3/8, 1; 1/4, 3 | ~1600–3200 | 0.99996; 0.9968; 0.99999; 0.999996 |
| 7/19, 11; 13/31, -7; 2/5, 25 | ~3200 | 0.99997; -1.00003; 0.99939 |

  With only the m = 0 saddle the ratio is 1 ± i. That is how the multi-saddle structure was detected.
- Side fact (VERIFIED): in every family tested, |Sigma_N|/sqrt N stays in [1.2, 1.3], and so does |Sigma_q|/sqrt q at level q. Sigma behaves like sqrt N times a quantum-modular phase. It does not decay: the e^{-kappa N/theta} decay in S0_lemma sits entirely in the prefactor K.

## 2. The leading amplitude is the same problem at level q
- **PROVED.** Let w_q be the small root of c0^q w = (1-w)^2, with c0 = -2(1-zeta0). Let lam_q = (1-w_q)^{1/q} and u_q = lam_q^2/c0. Then e^{i phi} = lam_q solves the saddle equation, because V = u0 lam_q^2 = u_q and V^q = w_q. At this saddle, A(phi_0) = Sigma_q(p/q), which is **exactly the S0_lemma sum at N = q, a = p**.
- VERIFIED: that this is the saddle the numerics use. A(phi_0) = Sigma_q to 1e-40 for all odd q <= 41 (`P1a_renorm.py`).
- Even q (`P1a_renorm_even.py`, VERIFIED to 1e-39 for q <= 14):
  - If 4 | q, the saddles with odd m have amplitude 0, and A(phi_0) = Sigma_q.
  - If q = 2 mod 4, the saddles with even m have amplitude 0, and A(phi_1) = Sigma_q with twist eps = e^{+2 pi i/q}. That twisted sum is conj(Sigma_q^{(n0=+1)}((q-p)/q)), so it is nonzero iff S0(e^{2 pi i p/q}) != 0 (PROVED via S0(zeta-bar) = conj S0(zeta)).
  - This is how the q = 2 case (1/2) has a single surviving saddle and no oscillation, which matches the old "16/15" plateau.
- C(phi_m) != 0 and g'' != 0 because |V^q| = |w_q| < 1 (PROVED).

## 3. The saddle sum is a Gauss sum and never vanishes
- VERIFIED (`P1a_amp.py`, 30 digits) for odd q: W_m := C(phi_m) A(phi_m) = W_0 * e^{-2 pi i inv(4p) m^2 / q}. So
  sum_m e^{-i pi m^2 N/(2q theta)} W_m = W_0 * sum_{m mod 2|theta|} e^{-i pi Y m^2/(2 theta)},  Y = (N + theta*4*inv(4p))/q in Z.
  Y is an integer because pN + theta = 0 mod q. The summand is 2|theta|-periodic.
- PROVED (classical generalized quadratic Gauss sum, Landsberg–Schaar reciprocity; e.g. Berndt–Evans–Williams ch. 1): for integers a, c with ac even and a != 0, the sum over n mod c of e^{pi i a n^2/c} has modulus sqrt(c * gcd(a,c)), so it is never 0. Combined with the verified phase law, the saddle sum has modulus |W_0| sqrt(2|theta| d) with d >= 1. This part is **conditional on the phase law**, which is VERIFIED, not PROVED.
- VERIFIED independently of the phase law, directly from the numerical weights (`P1a_gauss.py`). The scan covers q <= 20, 1 <= |theta| <= 10, and all admissible N mod 4q|theta|, with 11,700 cases.
  - The ratio |Gcal| / (max|W| sqrt(2|theta|)) takes only the values sqrt(d) for d in {1, 3, 5, 7, 9} when q is odd, and sqrt(d/2) for d in {1, 3, 5, 7, 9} when q is even.
  - Its minimum is 1/sqrt2. **The limiting amplitude never vanishes.**

**Consequence (target of step 2).** Fix p/q on the good arc and fix theta (theta = 1 in particular). Then for N -> infinity (N odd), |Sigma_N| ~ R * |Sigma_q(p/q)| * sqrt(N), with R > 0 explicit:
  R = |C| |e^{g0/tau}| sqrt(d |1-w_q| / (q |1+w_q|)).
This holds with the asymptotic HEURISTIC but VERIFIED to O(1/N), and the nonvanishing PROVED given the level-q certificate.
So S0 != 0 for all large N in every such family, since q <= 150 is certified by `certify_S0.py`.
For theta = 1 and q odd no Gauss-sum input is needed: the sum is |1 + e^{-i pi Y/2}| = sqrt2 with Y odd (PROVED, given the phase law).

## 4. Does iterating along the continued fraction close the argument?
Structurally, yes. Sigma at level N maps to Sigma at level q, times a nonzero Gauss sum and explicit factors.
By Dirichlet, choose p/q with q <= sqrt N and |theta| <= sqrt N. Then the level drops from N to at most sqrt N, and after O(log log N) steps it lands in the certified range q <= 150.
The observed relative errors are small in this regime; for example, theta = 25 gives 6e-4 at N = 3205.
The induction needs only the non-quantitative input S0(level q) != 0 at each step, provided the error is small relative to the leading term. The leading term's size is set by |Sigma_q|, which is itself of size about sqrt q by the same law.

## 5. What remains (OPEN), stated precisely
1. **Rigorous uniform error bound.** Prove |Sigma_N - Main| <= eps(q, theta, N, delta) * |Main| with eps -> 0 uniformly in the regime q, |theta| <= sqrt N, and p/q on the arc ell >= delta/2. The required pieces are:
   - explicit Euler–Maclaurin remainders for the block products;
   - Poisson plus contour deformation for 2|theta| saddles; the analyticity strip is Im phi > -ell/2, which is uniform in q, a good sign;
   - control of the partial-block O(q tau) corrections when q grows with N.
   The observed error constant grows roughly like |theta|/N. At the edge ell -> delta, the constants degrade as |w_q| -> 1.
2. **Quantitative induction.** The level-q input must be a lower bound. The natural form is |Sigma_q| >= c(delta) sqrt q, which is what the numerics show (ratio in [1.2, 1.3]). Otherwise the errors cannot be absorbed along the chain. The step multipliers R must be bounded below uniformly; R contains |e^{g0/tau}| = e^{Re g0 * qN/(2 pi theta)}, which can be exponentially small or large when theta is small.
3. **The phase law** W_m/W_0 = e^{-2 pi i inv(4p) m^2/q} (odd q) and the even-q masks: VERIFIED, not PROVED. A proof should follow from the shift phi -> phi + pi/q (V -> zeta0 V) acting on A and C; this was not written.
4. **Even N** (N = 0, 2 mod 4, with the eps twist) was not run. The same machinery should apply.
5. The arc edge: p/q must itself satisfy ell(p/q) >= delta' with delta' slightly below delta; this was not quantified.

## Files (all in this folder)
- `P1a_saddle.py`: exact Sigma_N against the multi-saddle prediction. Usage: `p q theta N...`
- `P1a_amp.py`: limiting weights W_m and the minimum of |Gcal| over residue classes.
- `P1a_gauss.py`: distribution of |Gcal| / (|W| sqrt(2|theta|)), showing it is Gauss-sum valued.
- `P1a_renorm.py`, `P1a_renorm_even.py`: the renormalisation identity A(phi_0 or phi_1) = Sigma_q.

## Claim census
- PROVED:
  - the equivalence Psi, Sigma, S0;
  - the saddle translation law;
  - the saddle identity A(phi_0) = Sigma_q (and the twisted even-q version);
  - C, g'' != 0;
  - Gauss-sum nonvanishing (classical);
  - the theta = 1, odd-q amplitude being nonzero, given the phase law.
- VERIFIED:
  - the full asymptotic to O(1/N) in 13 families, q up to 31 and |theta| up to 25;
  - the phase law;
  - the Gauss-sum moduli in 11,700 cases;
  - A = Sigma_q to 1e-40.
- HEURISTIC: the derivation of the asymptotic (no error bounds).
- OPEN: items 1–5 of section 5, and hence P1 itself.
