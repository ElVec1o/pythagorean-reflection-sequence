/-
  GramCasoratian.lean
  ===================
  The Gram–Casoratian identity for the symmetric three-term recurrence
        w (n+2) = B n * w (n+1) − w n
  with unit outer coefficients, which both gate blocks of the U-problem satisfy
  (P12 = Hahn–Exton ν = 3/2, S_e = Hahn–Exton ν = −1/2).

  For the quadratic form attached to the recurrence at step `n`,
  M n = ![![1, −B n/2], ![−B n/2, 1]], and two sequences `u v`, put

     Q n w  = w n ^ 2 − B n * w n * w (n+1) + w (n+1) ^ 2          (= xᵀ M x)
     P n    = 2 u n v n − B n (u n v (n+1) + u (n+1) v n)
                + 2 u (n+1) v (n+1)                                (= 2 · xᵀ M y)
     C n    = u (n+1) * v n − u n * v (n+1)                        (Casoratian)

  Then, pointwise in `n` and for *variable* `B`:

     4 * Q n u * Q n v − P n ^ 2 = (4 − B n ^ 2) * C n ^ 2.

  This is the Gram determinant identity for `M n` (the Gram matrix of two vectors
  with respect to a symmetric form has determinant det(M) · det[x|y]^2), with the
  denominators cleared so that it holds over an arbitrary commutative ring — no
  characteristic or invertibility hypothesis. It needs no property of the
  recurrence beyond the shape of `M`: it is a polynomial identity in the five
  quantities `u n, u (n+1), v n, v (n+1), B n`, closed by `ring`.

  Consequence used downstream: `4 Q u Q v ≥ (4 − B^2) C^2`, with `C` exactly
  constant (`cas_const`), so a *lower* bound on one solution's energy follows from
  an *upper* bound on the partner's. No turning-point analysis enters.
-/

import Mathlib.Tactic

namespace GramCasoratian

variable {R : Type*} [CommRing R]

/-- The energy form of a single sequence at step `n`. -/
def Qform (B : ℤ → R) (w : ℤ → R) (n : ℤ) : R :=
  w n ^ 2 - B n * w n * w (n + 1) + w (n + 1) ^ 2

/-- Twice the polarised (bilinear) form attached to the same quadratic form;
    doubled so that no division by `2` occurs. -/
def Pform (B : ℤ → R) (u v : ℤ → R) (n : ℤ) : R :=
  2 * (u n * v n) - B n * (u n * v (n + 1) + u (n + 1) * v n)
    + 2 * (u (n + 1) * v (n + 1))

/-- The discrete Casoratian of two sequences at step `n`. -/
def Cas (u v : ℤ → R) (n : ℤ) : R :=
  u (n + 1) * v n - u n * v (n + 1)

/-- **The Gram–Casoratian identity.** Pointwise in `n`, for *variable* `B`, over any
    commutative ring, and for arbitrary sequences `u v` — no recurrence hypothesis is
    needed for the identity itself. -/
theorem gram_casoratian (B : ℤ → R) (u v : ℤ → R) (n : ℤ) :
    4 * (Qform B u n * Qform B v n) - Pform B u v n ^ 2
      = (4 - B n ^ 2) * Cas u v n ^ 2 := by
  unfold Qform Pform Cas
  ring

/-- **The inequality used downstream**, over `ℝ`: the product of the two energies
    dominates `(4 − B^2) C^2 / 4`, because the subtracted term is a square. -/
theorem gram_le (B : ℤ → ℝ) (u v : ℤ → ℝ) (n : ℤ) :
    (4 - B n ^ 2) * Cas u v n ^ 2 ≤ 4 * (Qform B u n * Qform B v n) := by
  have h := gram_casoratian B u v n
  nlinarith [sq_nonneg (Pform B u v n)]

/-- **Casoratian conservation** for the unit-outer-coefficient recurrence
    `w (n+2) = B n * w (n+1) - w n`: the Casoratian is constant in `n`.
    Together with `gram_casoratian` this is what makes the right-hand side of the
    identity explicitly known. -/
theorem cas_const (B : ℤ → R) (u v : ℤ → R)
    (hu : ∀ n, u (n + 2) = B n * u (n + 1) - u n)
    (hv : ∀ n, v (n + 2) = B n * v (n + 1) - v n) (n : ℤ) :
    Cas u v (n + 1) = Cas u v n := by
  have e : n + 1 + 1 = n + 2 := by ring
  unfold Cas
  rw [e, hu n, hv n]
  ring

/-! ### The KS q-cosine/q-sine drift identity

For the Koornwinder–Swarttouw pair on the geometric lattice `z_n = z q^n`, the exact
recursions (from their q-derivative rules) are

    c n = c (n+1) − z (n+1) * s (n+1),      s n = s (n+1) + z n * c n.

Writing `z` for `z n` (so `z (n+1) = q z`) and `F n = c n ^2 − z(n+1) c n s n + q s n ^2`,
the substitution collapses the `z^2/q` terms identically and gives `F n` re-expressed at
the `(n+1)` vector, whence the drift. Both are `ring` identities. -/

/-- After substituting the two recursions, `F n` equals the *same* form evaluated at the
    `(n+1)` vector. This is the collapse that makes the drift a single monomial. -/
theorem F_shift (q z c1 s1 : R) :
    (c1 - q*z*s1)^2 - q*z*(c1 - q*z*s1)*(s1 + z*(c1 - q*z*s1))
        + q*(s1 + z*(c1 - q*z*s1))^2
      = c1^2 - q*z*c1*s1 + q*s1^2 := by
  ring

/-- **The drift identity.** `F n - F (n+1) = -(z (n+1)) * (1-q) * c (n+1) * s (n+1)`,
    with `F (n+1) = c1^2 - z(n+2) c1 s1 + q s1^2` and `z (n+2) = q^2 z`. Telescoping this
    over `n` gives `F 0 - F ∞ = ∑ drift` exactly, with `F ∞ = 1`. -/
theorem F_drift (q z c1 s1 : R) :
    ((c1 - q*z*s1)^2 - q*z*(c1 - q*z*s1)*(s1 + z*(c1 - q*z*s1))
        + q*(s1 + z*(c1 - q*z*s1))^2)
      - (c1^2 - q*q*z*c1*s1 + q*s1^2)
      = -(q*z)*(1-q)*c1*s1 := by
  ring

/-! ### The travel-pole equation in q-sine form

The Koornwinder–Swarttouw q-derivative rule `(1-q) D_q sin(z;q²) = cos(z;q²)` reads, after
clearing the difference quotient,

    cos(z;q²) = (sin(z;q²) - sin(qz;q²)) / z.

At a travel pole the gate block satisfies `cos(z₀;q²) = (q z₀/2) · sin(z₀;q²)` with
`z₀² = 2(1-q)`. Eliminating `cos` between the two turns the pole condition into a pure
q-sine relation with no `cos` and no `z₀` left in the coefficients. -/

/-- **Pole condition in q-sine form.** If `z^2 = 2(1-q)`, `z ≠ 0`, the q-derivative rule
    `z * c = sz - sqz` holds, and the pole condition `c = (q*z/2) * sz` holds, then
    `sqz = (1 - q + q^2) * sz`. Pure algebra. -/
theorem pole_qsine (q z c sz sqz : ℝ)
    (hsq : z^2 = 2*(1-q))
    (hrule : z * c = sz - sqz)
    (hpole : 2 * c = q * z * sz) :
    sqz = (1 - q + q^2) * sz := by
  have h : z^2 * q * sz = 2*(sz - sqz) := by linear_combination 2*hrule - z*hpole
  rw [hsq] at h
  linear_combination h/2

/-! ### `1 - Σ₁` is the KS q-cosine at a rescaled argument (U-26)

With `(q²;q²)_j (q;q²)_j = (q;q)_{2j}` one has, from the `₁φ₁` definition,

    cos(z;q²) = ∑_j (-1)^j q^{j²+j} z^{2j} / (q;q)_{2j},

while collapsing `sinh(mτ/2) = q^{-m/2}(1-q^m)/2` in the travel-block formula of the paper gives

    1 - Σ₁ = ∑_j (-1)^j (2(1-q))^j q^{j²} / (q;q)_{2j}.

The two series agree term by term exactly when `z² = 2(1-q)/q`; that per-term identity is the
whole content, and it is what `sigma1_term` states. Consequently the travel poles — the zeros of
`1 - Σ₁` — are precisely the zeros of `cos(·;q²)` at argument `√(2(1-q)/q)`. -/

/-- **U-26, per-term.** With `z² = 2(1-q)/q` and `q ≠ 0`, the `j`-th summand of the q-cosine series
    at argument `z` equals the `j`-th summand of the `1 - Σ₁` series. Summing over `j` (both series
    converge for `|q| < 1`, the `q^{j²}` factor dominating) gives
    `1 - Σ₁ = cos(√(2(1-q)/q); q²)`. -/
theorem sigma1_term (q z : ℝ) (hq : q ≠ 0) (hz : z^2 = 2*(1-q)/q) (j : ℕ) :
    q^(j^2+j) * (z^2)^j = q^(j^2) * (2*(1-q))^j := by
  rw [hz, div_pow, pow_add]
  field_simp

end GramCasoratian

-- Axiom check (Rule 5): all three results use only the standard axioms.
#print axioms GramCasoratian.gram_casoratian
#print axioms GramCasoratian.gram_le
#print axioms GramCasoratian.cas_const
#print axioms GramCasoratian.F_shift
#print axioms GramCasoratian.F_drift
#print axioms GramCasoratian.pole_qsine
#print axioms GramCasoratian.sigma1_term
