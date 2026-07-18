# Route B — catalytic kernel: assembled results

All claims below are validated numerically (0 counterexamples in the stated range).

## Lemma C (unified local site cost) — VERIFIED 0/209
For any two adjacent edges with deposits `a_{j-1}, a_j` (any `f`, any crossing
counts `m`), the **minimal** site cost is
```
        SiteCost(a_{j-1}, a_j) = max(|a_{j-1}|, |a_j|),
```
unique given the deposits and **independent of the crossing counts `m`** and of
`f`.  (Derived from the matching closed form `SiteCost = 2·rem − c1`, which for
bulk reduces to `2·max(|pu_L−pd_L|, |pu_R−pd_R|)` with `|pu−pd| = |a|/2`.)

## Lemma D (closed-form relaxed length) — VERIFIED vs BFS 0/229 (depth 8), 0 over-counts (depth 11)
The relaxed length of `(eps, delta, k; a)` is
```
   relaxed_len = Σ_{j in span} m_j  +  Σ_{sites in span} sitecost,
   span  = [lo, hi),  lo = min, hi = max of visited sites
                      {0, k} ∪ {j, j+1 : a_j ≠ 0 or f_j ≠ 0},
   m_j   = max(|a_j|, |f_j|),   forced to 2 when that is 0 (reachability gap edge),
   interior sitecost = max(|a_{j-1}|, |a_j|),
   virtual sites 0 and k use the explicit matching cost (the only non-local sites).
```
Implementation: `catalytic_funceq.relaxed_len_local`.

## Catalytic functional equation (bulk block) — VERIFIED to order x^28
Bulk edges have **even** deposit `a = 2s`, `s ≥ 1`; weight `2` per edge (signs ±),
edge length `|a| = 2s`, site length `max(|a_{j-1}|, |a_j|) = 2·max(s_{j-1}, s_j)`.
Put `q = x²`.  The catalytic GF `F(q,t) = Σ_{s≥1} F_s(q) t^s` (t marks `s = |a|/2`
of the last edge) satisfies the **closed catalytic equation**
```
  F(q,t) = 2qt/(1−qt)                                   [a single edge]
         + 2qt/(1−qt) · [ F(q,q) − F(q, q²t) ]          [append smaller/equal s']
         + 2q²t/(1−q²t) · F(q, q²t).                    [append larger s']
```
Equivalently, the s-sections satisfy
```
  F_s(q) = 2q^s + 2q^s Σ_{s'≥s} F_{s'}(q) q^{s'} + 2q^{2s} Σ_{s'<s} F_{s'}(q).
```
Both forms reproduce the series `[t¹]…: 2,2,6,2,18,6,42,18,118,50,282,190,706,594`
(coeff of `q^n` = coeff of `x^{2n}`) **exactly**.

## CRITICAL STRUCTURAL FINDING (revises the README expectation)
The catalytic argument enters as the **dilation `t ↦ q²t`**, NOT as a polynomial
kernel `K(x,t)`.  Hence the equation is a **linear q-difference (dilation)
equation**, and **Bousquet-Mélou–Jehanne Theorem 3 does NOT apply** in this form:
the `max(s,s')` site coupling is responsible (it splits the append-sum at
`s' = s`, producing the dilated section `F(q,q²t)` rather than `F(x,1)` plus a
polynomial kernel).  The solution class is q-holonomic, generically **transcen-
dental over ℚ(x)** — consistent with:
  * no low-order holonomic/algebraic recurrence for `v_n` in 33 terms;
  * `β₂` having no established low-order algebraic relation (project record).

## Sub-rates (numerical)
* bulk-run block growth `r_bulk = √(q-growth) ≈ √1.6405 ≈ 1.281`
  (series radius from 120-term series; clean period-2 q-ratio ≈ 1.6405).
* README determinized bulk scaffold `r ≈ 1.378` counts a different ensemble
  (full profile determinization incl. m>|a| ladder); reproduced here as
  `funceq_build.bulk_rho` (mmax=12 → rho 0.7214, r 1.386).
* full relaxed `v_n` growth `r ≈ 1.50–1.52` (project record), `r ≥ β₂ = 1.4995`.

## Files
* `catalytic_funceq.py`  — Lemmas C, D; `relaxed_len_local`, `boundary_site_cost`.
* `catalytic_kernel.py`  — boundary-class catalytic DP, reproduces v_n through n=16.
* `funceq_build.py`      — determinized bulk transfer, reproduces README rho_bulk.
* `state_census.py`      — shows RAW determinized state count is unbounded (the
                           obstruction the catalytic variable resolves).
* `catalytic_state_census.py` — cost-equivalence-class census.
