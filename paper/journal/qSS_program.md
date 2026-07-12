# The q-Siegel–Shidlovskii program for β₂ (the Hahn–Exton q-cosine zeros)

Status: research program, committed 2026-07-12. β₂ irrationality is OPEN; this document states the
precise target, the established theory it must extend, our position relative to that theory, the
milestones, and an honest assessment of scale. Grounded in Amou–Matala-aho–Väänänen, *On Siegel–
Shidlovskii's theory for q-difference equations*, Acta Arith. 127 (2007) 309–335 (AMV07), and the
Matala-aho-school Baker-type method (arXiv:1312.3819).

## 1. Target

**Conjecture Z.** For algebraic q ∈ (0,1), every positive zero z_k(q) of the Hahn–Exton q-cosine
G(q,·) is transcendental. (The weaker *irrational* form suffices for β₂.)

Equivalence: q* is by definition the least positive root of S(q) = G(q, 2q(1−q)); so z* = 2q*(1−q*)
= z₁(q*) is a positive zero of G(q*,·). Hence q* algebraic ⟹ z* is a nonzero *algebraic* zero of the
Hahn–Exton q-cosine at algebraic base, contradicting Conjecture Z. And β₂ = 1/√q*. So

    Conjecture Z (irrational form)  ⟹  β₂ irrational.

No result on the arithmetic of q-Bessel zeros exists in the literature (the zeros literature —
Koelink–Swarttouw and successors — is entirely analytic). Conjecture Z is unclaimed territory.

## 2. The established theory and our exact position

AMV07 / Matala-aho operate on Poincaré-type q-difference equations and prove linear independence /
non-vanishing of values at algebraic points, via a Thue–Siegel (Padé-of-the-second-kind)
construction. Two hypotheses gate the method:

- **(Geometry) Poincaré-type / regularity.** The system Y(qz) = A(z)Y(z) must be Poincaré-type at 0
  (A(0) invertible) and controlled at ∞.
- **(Arithmetic) Siegel margin.** A height ratio γ = log|b|/log|a| must lie below a threshold
  Γ(m,s) (AMV07 / arXiv:1312.3819, condition (4)).

Our equation q·G(z) − (q+1−qz)G(q²z) + G(q⁴z) = 0, companion A(z) = [[0,1],[−q,q+1−qz]]:

| hypothesis | our status |
|---|---|
| Poincaré-type at 0 | **MET.** A(0) = [[0,1],[−q,q+1]], det = q ≠ 0, invertible. |
| order | second-order (AMV07 covers higher order; the school's cleanest results are first-order). |
| regular at ∞ | **FAILS.** Irregular at ∞, Newton slopes {0,1}. |
| Siegel margin γ < Γ | **FAILS.** γ is our ρ = log(t/s)/(2 log t) ≤ 1/2 (prop:nogo); the factor 2 is the double Pochhammer (q;q)_{2k}. The AMV threshold is a condition on exactly this ratio. |

So the "ρ = 1/2 wall" of this project **is** the AMV Siegel-margin failure, now identified inside the
established theory. The double Pochhammer is the arithmetic obstruction; the irregularity at ∞ is the
geometric one.

## 3. Milestones

**M1 (geometry — hard but tractable).** Extend the q-SS Padé construction to a second-order equation
*irregular at ∞*. Our asset: the connection problem is **solved** (paper2) — C₁ = 1/(q;q)∞ (modular),
zero product = (q;q²)∞, the q-Stokes cocycle C₂ explicit, f₁/f₂ pinned by q-Borel/q-Laplace. The
irregularity is fully described, so the approximants can be written down; this is adaptation, not new
theory. Estimated scale: months of expert work.

**M2 (Siegel margin — MAJOR OPEN, ≡ the wall).** Prove a q-SS non-vanishing *past* the margin
γ ≥ Γ, i.e. for the ρ = 1/2 double-Pochhammer class. Every explicit approximation this project has
built (Taylor/Padé, backward-orbit normal form, truncation roots, power sums, ~30 constructions)
conserves ρ ≤ 1/2 — none beats the margin, and the conservation is proven for all natural-lattice
objects (prop:nogo). Closing M2 needs input from **outside** the module's ℚ(q)-lattice.

  The natural candidate is the modularity of the connection constant: Nesterenko's method controls
  modular values with **no** Siegel-margin condition (it uses the differential-ring + multiplicity
  structure, not Siegel's lemma). But the modularity enters the zero condition **only through the
  connection formula** G(z*) = C₁f₁(z*) + C₂(z*)f₂(z*) = 0, which reduces M2 to a theta non-resonance
  (Lemma Θ / rem:sharpest) — proven equal in strength to β₂ itself. So the modularity is **not** a
  bypass; it re-expresses M2 as the joint (σ,δ)-difference-differential multiplicity estimate
  (rem:valuedescent), which is absent from the literature. Estimated scale: a genuine new theory —
  years, or a breakthrough.

**M3 (self-referential specialization — minor).** AMV give non-vanishing at *fixed* algebraic q; our
q* is tied to z* by the diagonal z = 2q(1−q). Once M1+M2 give non-vanishing uniform in a neighborhood
of q*, specialize to the diagonal crossing. Straightforward once M1+M2 hold.

## 4. Secret-sauce assets, honestly costed

| asset (all PROVEN) | contributes to | does it break the wall? |
|---|---|---|
| C₁ = 1/(q;q)∞ modular; zero product (q;q²)∞ | M2 (Nesterenko hope) | **No** — reduces to theta non-resonance (equal strength). |
| connection theory solved (C₂ explicit, f₁/f₂ pinned) | M1 | Yes for M1 (makes irregular-∞ tractable). |
| SL₂ Galois + non-integrability + differential transcendence (function level) | prerequisite | Necessary (the q-analog of "not an E-function"); not sufficient. |
| backward-orbit / truncation-root explicit approximants | M2 (approximation hope) | **No** — conserve ρ = 1/2 (proven). |
| adelic-units lemma (finite places = units) | M2 (any criterion is archimedean) | Sharpens, does not break. |

## 5. Honest scale

- M1: tractable, ~months, no new theory (leverages the solved connection problem).
- M2: the real barrier. Equal in strength to β₂ (Collapse Lemma). Needs a Nesterenko-type multiplicity
  theory for finite (σ,δ)-modules at a non-fixed point, OR a q-Siegel method valid past the margin —
  neither exists. Years, or a genuinely new idea.
- M3: minor.

## 6. Concrete first deliverables (executable now, independent of the breakthrough)

1. **[done, paper2]** State the obstruction as the AMV Siegel-margin inequality γ = ρ ≤ 1/2 < Γ.
2. Write the second-order irregular-∞ Padé-of-the-second-kind construction explicitly (M1), using the
   pinned f₁/f₂. Even without closing M2, this is a publishable extension of the q-SS construction to
   the Hahn–Exton class and isolates M2 as a single quantitative estimate.
3. A companion paper: *Differential transcendence of the Hahn–Exton q-cosine and the arithmetic of
   its zeros* — the function-level theorem (thm:sl2 + non-integrability, already proven) is publishable
   independently of β₂, and frames Conjecture Z for the transcendence community.

The last item is the highest-value near-term move: it banks the proven function-level result and
poses Conjecture Z where a specialist could pick up M2.

---

# M1 — the second-kind Padé construction (begun 2026-07-12)

M1 asks for the explicit q-Siegel Padé-of-the-second-kind approximants for the irregular-at-∞
Hahn–Exton system, their degree/order/arithmetic properties, and the reduction of irrationality to a
single quantitative inequality (M2). Progress:

## M1a — the diagonal second-kind form (DONE)
The cleared truncation P_N(q) = (q;q)_{2N}·S_N(q) ∈ ℤ[q], S_N = Σ_{k≤N}(-2)^k q^{k²}(1-q)^k/(q;q)_{2k},
is the second-kind approximant along the diagonal z = 2q(1-q). Verified (N ≤ 8):
- **degree** deg P_N = 2N² + N (exact);
- **remainder** |P_N(q*)| = q*^{N²(1+o(1))} (the ratio log|P_N(q*)|/N² → log q* = −0.7997…; measured
  −1.38, −1.22, −1.13, −1.07, −1.03, −1.00 for N = 3..8);
- **height** H(P_N) = e^{O(N)} (linear; log₂H/N → ~1.75 at q = 1/2) — the pentagonal sparsity of the
  q-Pochhammer coefficients keeps the height small;
- **clearing** P_N(s/t)·t^{2N²+N} ∈ ℤ.

## M1b — the general-point / uniform construction (TODO, tractable, ~months)
The Padé denominators of G(q,·) are the modified q-Lommel polynomials (Koelink–Swarttouw); the naive
[n/n] Padé has only a geometric remainder z*^{2n}, so the q-adapted (theta-fast) construction of M1a is
the correct object. What remains: (i) the construction at a general algebraic point z (not only the
diagonal), (ii) uniformity in q over a neighbourhood of q*, (iii) the explicit q-Lommel identification
of the denominators. All are adaptations that the solved connection theory (paper2 §connection:
C₁ = 1/(q;q)∞, C₂ explicit, f₁/f₂ pinned) makes routine; none needs new ideas.

## M1c — the reduction lemma (essentially done; formal statement pending)
From M1a: **q* (hence β₂) is irrational if there is an infinite set of N with P_N(q*) ≠ 0 and
|P_N(q*)| < t^{−(2N²+N)}.** With |P_N(q*)| = q*^{N²(1+o(1))} this is q*^{N²} < t^{−2N²}, i.e.
log(t/s) > 2 log t, i.e. st < 1 — false. The deficit is the factor 2 in the degree 2N² = the double
Pochhammer (q;q)_{2N}. Equivalently, a **single-Pochhammer** second-kind form of degree N²(1+o(1))
with the same remainder would prove q* ≠ s/t for all s < √t (half of irrationality) immediately.

## The margin inequality (the exact face of M2)
M1 reduces irrationality to: *construct integer forms of degree D_N with |form(q*)| < t^{−D_N} for the
Hahn–Exton diagonal.* We have |form| = q*^{N²} at D_N = 2N²; the requirement is D_N ≤ N²(1+o(1)) at the
same remainder, i.e. **halve the effective degree, or double the remainder decay to q*^{2N²}.** Thirty
distinct lattice constructions conserve the factor 2 (paper2 prop:nogo); breaking it is M2, equal in
strength to β₂ itself.
