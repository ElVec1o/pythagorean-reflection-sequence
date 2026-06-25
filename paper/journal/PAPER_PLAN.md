# Publication plan — Pythagorean reflection-sequence corpus

_Generated from the publication-prep workflow (survey -> architect -> draft -> review). Honest status; conditional results flagged in place._

## Paper split

### paper1  *(drafted)* — The Universal Right-Triangle Reflection Sequence: a word-length metric, effective universality, and the lamplighter structure of A396406
- **Venue:** Journal of Integer Sequences (primary, realistic) or Journal of Combinatorial Theory Series A / Annals of Combinatorics (stretch). JIS is the honest fit: OEIS-anchored, exact-enumeration + closed-form, machine-verified certificates.
- **Readiness:** ready-to-draft
- **Thesis:** For right triangles with unequal rational legs the side-reflection group is virtually the lamplighter Z wr Z; its geodesic word length has a closed form ell_T = ell_R + 2c; the orbit-growth sequence (OEIS A396406) is shape-independent through depth 32 (sharp) with an effective all-depths universality theorem, and has exact growth rate beta_2 = 1.4916177871..., excluding 3/2.
- **Sections:** 10

### paper1b — A dimension-independent collision-depth invariant for right-corner orthoscheme reflection groups
- **Venue:** Journal of Integer Sequences or Geometriae Dedicata / a Coxeter-groups venue (e.g. Journal of Group Theory). The OEIS-sequence family + closed-form rate + elliptic-curve descent fits a solid specialist journal; not top-tier.
- **Readiness:** ready-to-draft
- **Thesis:** For the n-dimensional right-corner orthoscheme reflection group: closed-form Coxeter-Steinberg growth rate r_n = 1+2cos(2pi/(n+3)); unconditional faithfulness for pairwise-distinct rational legs (Class C) via a uniform Gram determinant identity and rank-0 Mordell descent; and a tri-valued collision-depth invariant cd_n in {inf,4,3} determined by two positional statistics (e,t).
- **Sections:** 6

### paper2 — Transcendence of a planar reflection-group growth series and its relaxed companion
- **Venue:** After V's lemma is fully typeset: a specialist analysis/combinatorics journal (e.g. Journal de Theorie des Nombres de Bordeaux, Ramanujan Journal, or Aequationes Mathematicae). Until then it is a preprint/arXiv reduction note, NOT submittable as an unconditional theorem.
- **Readiness:** blocked-on-open-item
- **Thesis:** The catalytic q-difference building-block series Sigma_0,Sigma_1,S_0,S_1 are transcendental over Q(q) unconditionally (Polya-Carlson natural boundary); the relaxed series V is transcendental over Q(x) modulo one closed-form contour lemma plus Stirling; and the true series U is transcendental over Q(x) CONDITIONAL on one named Hahn-Exton q-Bessel turning-point bound R = P12 - E = O(tau^{5/2}), corroborated by an orthogonal Christol-route evidence line.
- **Sections:** 8

## Closed ledger (publishable now)

- **Coxeter presentation W=<R_0,R_1,R_2 | R_i^2,(R_0R_1)^2> with Steinberg series (1+t)^2/(1-t-t^2), coefficients F_{d+3}** — Standard Steinberg/Niven; unconditional; paper.tex lines 121-140. Load-bearing baseline.
- **The eight length-10 relations hold for every right triangle (equality of affine matrices over Q(a,b))** — Polynomial identity over Q(a,b) (denominators divide a power of a^2+b^2) AND Lean-4 ring-tactic kernel-checked. paper.tex lines 142-207.
- **Depth-10 completeness: exactly 225 distinct length-10 images (217 singletons + 8 collision pairs), u_10=225** — Finite enumeration over (3,4,5) + symbolic Q(a,b) backing guaranteeing the eight are the only collisions. paper.tex lines 209-231.
- **Symbolic normal form rho_T(w):z|->eps zeta^k sigma^delta(z)+P_w(zeta), P_w bounded-height integer Laurent poly, P_w(1)=0** — Elementary induction on word length; triangle-independent; complete. paper.tex lines 397-426.
- **Effective universality: deviation at depth d forces c_T | extreme coefficients, so c_T>2d => universal at depth d** — Gauss's lemma on mu_T = c_T t^2 - e_T t + c_T, fully elementary, unconditional. paper.tex lines 443-502.
- **Sharp uniform universality through depth 32; (1,2) deviates at depth 33 (u_33-30=3848354)** — effective-universality (c_T>72) + finite one-sided-exact two-prime modular certificate; sharpness an exact BFS for (1,2). Trust base modular not Lean kernel (stated honestly). paper.tex lines 524-542.
- **T-independence of orbit growth through depth 22, Lean-certified (universal_layers_through_22)** — Single symbolic BFS deduplicating over (a^2+b^2)^22; native_decide trust base stated precisely. paper.tex lines 245-272.
- **All-depths universality is FALSE: explicit kernel witness 2(t-1)mu_T; deviation depth n_T in [max(31,c_T/2), 24c_T+8]** — Glide-square lemma (R_xR_yR_h)^2=translation; Phi_T never injective for algebraic shapes; first deviation depth 33. Refutation is a theorem, not an open question. paper.tex lines 274-578.
- **Translation module T_rho^ab = I_A cap I_B = Z[Q].h, h=(c-1)(Y-1), unconditional** — Bass-Serre tree exactness, 3-step descent, no torsion; finite-quotient cross-check. paper.tex lines 1506-1603.
- **Generic side-reflection group is virtually Z wr Z (lamplighter): amenable, exponential growth, not finitely presentable** — H index 4 = T rtimes <r> = Z wr Z; not-f.p. by Baumslag + commensurability invariance. paper.tex lines 894-946.
- **Metric theorem ell_T = ell_R + 2c with explicit finite-state closed form for c (correct kernel q/(1-qy))** — Splice +2 upper bound complete; lower bound via Part-B finite-state covering verification (depth 24, 275823 elements held out, 0 exceptions); reproduces u_0..u_22 with no BFS. Corrects the naive qy/(1-qy) overcount. metric_theorem.tex lines 40-228.
- **Strand-bound: single-Eulerian-trail interface profiles are multisets over a fixed 8-letter alphabet with one catalytic variable** — Self-contained half-line sub-walk argument; DP cross-check corroborates. paper.tex lines 1099-1125.
- **beta_2 = 1.4916177871143742268... exactly (root of Sigma_1(q)=1); 3/2 excluded** — Squeeze t_d<=u_d<=v_d with connectivity-invariant travel block (Euler trail argument), independent of lem:cos. Growth-rate statement only; number's transcendence open. paper.tex lines 1166-1204.
- **n-dim closed-form rate r_n = 1+2cos(2pi/(n+3))** — Steinberg series collapse to Pell-Fibonacci P_{n+3}; verified 50 digits to n=500. paper_ndim.tex lines 131-176.
- **Uniform Gram determinant det Q_n = -prod a_i^2 for all n>=3, all positive legs** — Single n-independent polynomial identity D_k=(prod a_i^2)(1-sum a_i^2), tridiagonal cofactor induction, SymPy-verified. paper_ndim.tex lines 232-292.
- **Three Diophantine quartics empty over distinct positive rationals (Cremona 24a1, 72a2, y^2=x^3-x, all rank 0)** — Classical rank-0 Mordell descent; Sage/LMFDB-verified. paper_ndim.tex lines 313-349.
- **Class C faithfulness: for pairwise-distinct rational legs, rho_n faithful and u_d^n=[t^d]W_n(t) in every n>=3** — det-Q non-degeneracy + extended Niven + boundary elementary + interior rank-0 descent + Tits. Restricted to Class C (does NOT extend to equal legs). paper_ndim.tex lines 353-395.
- **Collision-depth invariant cd_n in {inf,4,3} determined by (e,t) statistics** — Complete elementary classification; the (e,t) refinement corrects the naive run-length rule at n>=4. paper_ndim.tex lines 425-510.
- **OEIS Class C family 3D-7D with proven closed-form g.f.s and rates (A397439, A397437, A396927 published, A397438, 7D pending)** — n-case of ndim-rate + master-C-uncond; BFS-confirmed; leg-independence a Class C theorem. paper/OEIS/submit/*.txt.
- **Sigma_0,Sigma_1,S_0,S_1 transcendental over Q(q) unconditionally (Polya-Carlson natural boundary)** — Integer power series, radius exactly 1, super-polynomial diagonal |c_{(j+1)^2}|>=2^{j+1}, non-rational => |q|=1 natural boundary. No analytic gate, no lem:cos. Does NOT transfer to V. transcendence.tex lines 1057-1104.
- **P12 closed form = Hahn-Exton q-Bessel J^{(3)}_{3/2}, determinant q^3-1 (Abel), reductions eq:p12iden/eq:p12pole** — Exact, machine-verified to 10^-60. The BOUND on this object is the conditional part; the closed form itself is unconditional. lifting_U.tex lines 549-622.
- **Two amplitude lemmas unconditional: kappa modular Poisson estimate, conserved-Casoratian bulk envelope (4-B_n^2)^{-1/4}** — Proved from scratch (Poisson summation; Abel summation against Dirichlet kernel); verified to 25-35 digits. They reduce the U-gate to ONE turning-point normalization but do NOT prove it. amplitude_bound.tex lines 63-188.
- **No-Mahler theorem (parts 1+2 unconditional): no validated Mahler fit to 500 terms; Hankel determinants nonzero** — Non-rationality via nonzero Hankel is unconditional; the finite search excludes the searched classes. (Pole-law part 3 is conditional on lem:cos.) transcendence.tex lines 1324-1344.

## Open ledger (route-to-finish)

### lem:cos uniform oscillatory-average bound (Sigma_1, S_1 ~ 1-cos w + O(sqrt tau) uniformly in phase)  `[research-level]` → paper2
- Status: Numerically certain (sup_w|S_1-(1-cos w)|<=0.67 sqrt tau on tau in (0,1e-3]); exact Abel reduction S_1=(1-cos w)+sum mu_j R_j proved; leading constant -17sqrt2/36 derived term-by-term to 15 digits. The uniform bound itself is unproved.
- Why not closed: The naive absolute Touchard tail majorant is INFINITE (E[exp(c N^5)] diverges for Poisson; partial sums ~10^975). Closing needs an oscillation-preserving (saddle / van der Corput / Poisson) uniform estimate not available.
- Done when: A written proof of sup_w |S_1-(1-cos w)|/sqrt tau <= C uniformly, OR the strictly weaker |E(m pi)|<1 for all large m, with no numerical hypothesis remaining.
- Route:
  1. State lem:cos explicitly as a Hypothesis in Paper 2, never as a Lemma
  2. For the WEAKER pole-accumulation need, prove only |E(m pi)|<1 along extreme phases via the lem:extremephase / lem:T2abs absolute-contour route
  3. If a full uniform bound is wanted, carry out the Olver steepest-descent error estimate on the curved contour through s*=iW/2 (the genuine unwritten step)

### lem:T2abs absolute-contour bound |T2|=O(tau^{1/4}) (the V-transcendence keystone)  `[high]` → paper2
- Status: Stated with proof sketch: e^{piW/2} cancellation on horizontal sides kills the cosh W majorant; numerics A_left=0.00746 tau^{1/4}, fitted exponent 0.257. Rests on lem:Bbounded.
- Why not closed: Internal contradiction in transcendence.tex: the same file states the absolute-value route meets a divergent majorant. The hinge |g_s|<=2 on the FULL horizontal sides of dR (including Re s up to where the cubic rises) is asserted but not verified; the absolute integral's convergence must be confirmed.
- Done when: A referee-checkable proof that the absolute contour integral over dR converges to O(tau^{1/4})->0, making V transcendental modulo only lem:Bbounded (closed form) + textbook Stirling.
- Route:
  1. Resolve the internal contradiction: delete the refuted lem:tail and the lem:cos-conditional language for V, OR demote V to conditional-on-lem:cos
  2. Verify lem:Bbounded's lower bound holds along the entire dR horizontal sides
  3. Confirm the absolute contour integral converges and equals O(tau^{1/4})
  4. Typeset the Stirling O(sqrt tau) decay rate fully (currently numeric 0.078 sqrt tau; qualitative ->0 rigorous)

### lem:Bbounded uniform lower bound across the full contour (the true keystone under 'V unconditional')  `[high]` → paper2
- Status: Closed form Re B_{iy}=-(1/2)log(y tau/sin y tau) proved; inf = -(sqrt2/18)sqrt tau + O(tau) on the strip, minimizer the diagonal node. Numerically confirmed dps>=45.
- Why not closed: The Stirling Re log Gamma asymptotic is used 'uniformly for x in compacta' over a tau-dependent range up to Re s ~ sqrt3/2 W; the tail control O(tau^{3/2}) across the whole contour is the load-bearing analytic step, not fully bounded.
- Done when: Re B_s >= -(sqrt2/18)sqrt tau + O(tau) proved on all of dR with explicit constants, no 'verified against truncation' hedge.
- Route:
  1. Make the Stirling uniformity precise over the tau-dependent range
  2. Bound the O(tau^{3/2}) tail of the cubic series across the whole contour rigorously
  3. Confirm the lower bound holds on the entire horizontal sides of dR (the part lem:T2abs needs)

### U-gate turning-point bound R = P12 - E = O(tau^{5/2}) (the lone input keeping U conditional)  `[research-level]` → paper2
- Status: Reduced (amplitude_bound.tex thm:R) to a SINGLE turning-point amplitude normalization gamma/gamma_cl=1+O(tau); two harder pieces (kappa modulus, Casoratian envelope) proved unconditionally. Numerically certain: R/(tau^{5/2}sin w)->1891 sqrt2/10368 to 21 digits, ~4x margin over 80 poles.
- Why not closed: The O(tau) confluent correction to the x->0 Hahn-Exton q-Bessel nu=3/2 connection coefficient (q-Airy / uniform-Bessel matching across the turning point) is not carried out. Six independent routes all reduce to this same coefficient and confirm it is not reachable by elementary/resummation means (Gevrey-1, Borel singularity |rho|~4.16, no holonomic/PSLQ shortcut).
- Done when: A proof of |R|<=K tau^{5/2} (K<1/sqrt2) uniform in m; then U transcendental over Q(x) stated as a Theorem conditional only on lem:cos (or unconditional if lem:cos also closes). U must NEVER be stated unconditionally before this.
- Route:
  1. Match Morita 2011 (arXiv:1105.1998) normalization for the q-Borel/q-Laplace connection formula (correct kernel is Jacobi theta theta_p(t/tau), matches q-series 36 digits)
  2. Push Morita's p->1 confluent limit to SUBLEADING via modular theta expansion to obtain the O(tau) correction
  3. Conclude gamma/gamma_cl=1+O(tau), hence R=O(tau^{5/2}), hence U transcendental

### Christol mod-p route: K_p(u) infinite for one prime p  `[research-level]` → paper2
- Status: Validated O(N^4) engine reproduces u_n mod p to n=42; p-kernel near-maximal at two primes (p=3: 1,4,13,39 vs 1,4,13,40; p=5: 1,6,30 vs 1,6,31). Theta-telescoping closed form derived (verified k<=4).
- Why not closed: Finite data establishes the kernel is LARGE, not provably INFINITE; Christol needs an infinite kernel. The square-support handle is unavailable (u_n mod p is dense / base-p pseudorandom; Kedlaya and Adamczewski-Bell 2012 gap/zero-set theorems do not apply directly). Reduces to the same theta/square obstruction as the analytic route.
- Done when: A proof that K_p(u) is infinite for at least one prime p, yielding U transcendental over Q(x) unconditionally via Christol. Until then it is EVIDENCE only.
- Route:
  1. Prove K_p infinite via the theta-telescoping q^{k(k-1)}/(qt;q)_{2k} structure surviving the Euler-product denominator mod p
  2. Complete the one-line general-k Pochhammer induction for theta-telescoping
  3. Tie the kernel growth rigorously to the square-gap structure

### Metric theorem Part B: explicit transition-list write-up of the <=24-state transducer  `[low]` → paper1
- Status: Mathematics settled (finite-state covering verification, depth 24, 275823 elements held out, 0 exceptions). The c closed form is realization-independent (cor:rigid discharges the lower bound).
- Why not closed: The explicit transition list of the finite-state function is verified in code (c_close.py) but not typeset on paper, so the covering verification is not yet checkable without the script.
- Done when: The transducer transition table appears in the paper and the covering argument is checkable without running code. (Expositional, not a math gap.)
- Route:
  1. Write out the <=24 transition list explicitly in an appendix
  2. State the finite-state lemma (lem:fsm) with the transition-covering-window argument made airtight

### Theta-telescoping general-k Pochhammer identity  `[low]` → paper2
- Status: Verified symbolically for 0<=k<=4 plus an elementary general-k argument (sum_{j<k}(2j+1)=k^2 numerator power; prod(1-q^{2j+1}t)(1-q^{2j+2}t)=(qt;q)_{2k}). Reproduces the bulk record exactly to [q^14].
- Why not closed: The general-k step is a finite symbolic check, not yet a one-line induction.
- Done when: A typeset induction proving F(q,t)=sum_k alpha_k(t)E(q^{2k}t) for all k. (Expositional.)
- Route:
  1. Write the general-k Pochhammer telescoping as an induction

### Sharp sqrt(tau) constants (-17sqrt2/36 bulk, +sqrt2/36 travel) as symbolic theorems  `[medium]` → paper2
- Status: Derived rigorously term-by-term EXCEPT the resummation of the O(tau) remainder; confirmed to 15-21 digits by Richardson. The phase constant sqrt2/36 also follows from the elementary McMahon addendum c1=1/18 (effectively unconditional for the leading order).
- Why not closed: The single O(tau)-remainder resummation step is the lem:cos gap; the constants are not fully proven beyond the leading-order law plus numerics.
- Done when: Either a symbolic proof of the sharp constants, or an explicit statement that only the leading-order law is a theorem and the coefficient is numerically certain.
- Route:
  1. Close lem:cos (above), OR present the constants as 'leading-order law proved, sharp coefficient numerically certain'
  2. Use the elementary McMahon c1=1/18 derivation to make the LEADING phase constant unconditional

### All-orders McMahon rationality of travel-pole expansion (thm:mcmahon)  `[research-level]` → paper2
- Status: c1=1/18, c2=-41/600, c3=-1915/7056 unconditional (elementary from the q-series); all-orders algorithm + lemmas A,B,C elementary and complete.
- Why not closed: All-orders VALIDITY rests on one Borel bound (G2): |B(t)|<=K e^{|t|/R} on R_+ for the Borel transform. NS-a (analyticity) proved; G2 is the standing-open nu=1/2 q-Bessel confluence-with-remainder, not citable.
- Done when: A proof of the Borel bound G2, making the all-orders rational McMahon expansion a Theorem; the low orders c1,c2,c3 are already unconditional.
- Route:
  1. Prove the single Borel growth bound G2 on R_+ (same difficulty tier as lem:cos)
  2. Until then, state only c1,c2,c3 as unconditional and the all-orders theorem as conditional on G2

### Conjecture: true series U transcendental over Q(x) (and beta_2 transcendental as a number)  `[research-level]` → paper2
- Status: Reduced to U transcendental iff N_U avoids vanishing at infinitely many travel poles q_m; ONE confirmed U pole (the dominant q*=0.4495, unconditional via positivity on (0,q_bulk)). Three independent transcendence-of-beta_2 routes (Christol, D-finite exclusion, Mahler) are all conditional/open.
- Why not closed: Needs (a) lem:cos for the poles to be genuine, (b) propagation of the cycle-amplitude sign to secondary poles, AND (c) the R=O(tau^{5/2}) gate. A validated closed form for individual B_c (c>=1) is missing (naive +2-per-cycle weighting miscounts u_9=142 vs 144). beta_2-as-a-number transcendence has no proven route.
- Done when: U transcendental over Q(x) as a Theorem conditional only on the named turning-point bound; the conjecture stays a conjecture until all three inputs close. NEVER upgrade to unconditional.
- Route:
  1. Close the R=O(tau^{5/2}) gate (above)
  2. Close lem:cos (above)
  3. Establish a validated closed form for B_c and propagate its sign to secondary poles
  4. For beta_2 the number: prove one of the Christol / all-(k,m) D-finite-exclusion / Mahler-class routes

### Class B (two equal legs, e.g. (1,1,2)) growth: closed form / rate / leg-independence  `[high]` → paper1b
- Status: BFS to depth 18 (1,4,9,18,...,336544); ratio ~1.92 empirical; no order<=9 linear recurrence; tetranacci coincidence disclosed (diverges at a(14): 24591 vs 24615).
- Why not closed: No closed form, no rational g.f., no proven rate; the Class C faithfulness proof provably does NOT transfer (needs all dihedral angles irrational multiples of pi, which fails with two equal legs). Leg-independence within Class B is empirical (5 triples).
- Done when: A closed-form or proven growth rate for Class B; until then file as OEIS hard/more with the caveats. Do NOT state leg-independence for Class B.
- Route:
  1. Prove leg-independence within Class B (new method, not the Class C descent)
  2. Find a generating function / growth-rate minimal polynomial
  3. Extend BFS beyond depth 18 (no recurrence, each term a deeper exact-rational BFS)

### V-relaxed and bulk-block as standalone OEIS entries; transcendence framing  `[low]` → paper2
- Status: V-relaxed (1,3,5,8,13,21,34,55,91,148,...) and bulk-block (2,2,6,2,18,6,42,18,118,50,...) entries drafted hard/more. Bulk-block transcendental over Q(q) unconditional (Polya-Carlson); V transcendence conditional on one analytic bound.
- Why not closed: V transcendence is conditional (lem:cos / lem:T2abs); leg-independence for the relaxed metric is conjectural; standalone OEIS interest of the bulk block is borderline (editor pushback risk).
- Done when: OEIS acceptance with honest hard/more flags and the two transcendence tiers kept distinct.
- Route:
  1. Confirm no duplicate (search the bulk-block prefix) and justify standalone interest, or file as a comment on A396406
  2. Carry the unconditional (Q(q)) vs conditional (Q(x)/V) tiers distinctly
  3. Submit after the Class C family per the OEIS handoff note

## Notes

SPLIT RATIONALE. The corpus splits cleanly into THREE papers, one bankable (draft_now=true). I deviated from the recommended two-paper split by separating the n-dim orthoscheme family (paper1b) from the 2D right-triangle paper (paper1), because (a) paper_ndim.tex already exists as a self-contained, fully-unconditional manuscript with its own abstract and title, and (b) the 2D metric/universality/lamplighter material is itself a full paper. Forcing both into one would bloat it and mix two distinct audiences (geometric group theory / word metrics for 2D vs Coxeter growth + elliptic-curve descent for n-dim). Both paper1 and paper1b are ready-to-draft and unconditional; paper1 is the designated bankable draft_now=true paper because it is the headline OEIS sequence A396406 with the strongest single narrative (lamplighter + metric + universality + exact beta_2).

HONESTY GUARDRAILS for the drafters (mandatory):
1. NEVER state U transcendental unconditionally. U is conditional on the named Hahn-Exton q-Bessel nu=3/2 turning-point bound R=O(tau^{5/2}) (and on lem:cos). This appears ONLY in paper2, NEVER in paper1/paper1b.
2. paper1 must NOT contain any transcendence claim beyond the unconditional beta_2 growth-rate value and the honest finite-horizon exclusions. The Polya-Carlson BLOCK transcendence and the V/U ratio transcendence belong to paper2.
3. The lem:cos / lem:T2abs INTERNAL CONTRADICTION in transcendence.tex MUST be resolved before paper2 is drafted: pick ONE framing (V conditional on lem:cos, OR V unconditional modulo lem:Bbounded+Stirling via lem:T2abs) and delete the other. The author's honesty constraint forbids presenting V as unconditional while the same document still contains the lem:tail refutation. Until resolved, paper2 is blocked-on-open-item.
4. Lean trust base must be stated precisely everywhere: ring-tactic kernel-checked (length-10 relations, Schur steps) vs native_decide / modular two-prime certificate (depths 22-36, det Q_n n=2..10). Do not present depth 32 or general-n det as Lean-kernel-verified.
5. Class C faithfulness/leg-independence is ONLY for pairwise-distinct rational legs; Class B is empirical and the proof provably does not transfer.
6. Purge ALL research-log narration ('we first tried', 'it turns out', 'BREAKTHROUGH', 'adversarial re-check', 'now superseded', 'the optimism was misplaced', code-script citations inline). The main paper.tex abstract is currently ~80% lem:cos saga narration and MUST be rewritten to state results only; the unconditional geometry/arithmetic results in that abstract are fine but are buried under the transcendence hedging.

VENUE HONESTY: None of this is top-tier (no Annals/Inventiones/JAMS). paper1 and paper1b fit Journal of Integer Sequences best (OEIS-anchored, exact enumeration, machine-verified, closed forms) with a possible stretch to a mid-tier combinatorics/group-theory journal. paper2, once V's lemma is typeset, fits a specialist analysis/number-theory journal (Ramanujan Journal, JTNB, Aequationes Math); as currently standing (U conditional, V contradiction unresolved) it is an arXiv reduction note, not a submittable unconditional theorem.

READINESS: paper1 = ready-to-draft NOW (all results closed or honest-finite; only the metric Part-B transition list and abstract rewrite remain, both expositional). paper1b = ready-to-draft (paper_ndim.tex is near-final; needs the R-rule hedge converted to a corollary and the Class B caveats kept). paper2 = blocked-on-open-item (resolve the lem:cos/lem:T2abs contradiction; decide V's honest status; keep U conditional).

KEY SOURCE FILES (absolute paths): /Users/vico/Documents/elvec1o/XXXXX MATH PROOF/paper/paper.tex (2D, mixed — extract bankable parts for paper1); /Users/vico/Documents/elvec1o/XXXXX MATH PROOF/paper/paper_ndim.tex (paper1b, near-final); /Users/vico/Documents/elvec1o/XXXXX MATH PROOF/paper/paper_extra.tex (Class A/B, supplement material); /Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b/{metric_theorem,transcendence,lifting_U,amplitude_bound,route_b_funceq,route_modp,transcendence_paper}.tex (paper2). OEIS drafts in /Users/vico/Documents/elvec1o/XXXXX MATH PROOF/paper/OEIS/submit/.