/-
  Reciprocity.lean
  ================
  The kernel-symmetry proof of Proposition `prop:recip` of `paper/journal/paper2.tex`,
  section 5.3 (`sec:cocycleid`): `t_0 = b_1`.

  The paper gives two proofs.  The second (the Casoratian) consumes Corollary `cor:cocycle`,
  whose four entries are limits of an infinite product of transfer matrices.  The first (kernel
  symmetry) does not: once the resolvent exists as an operator, it is the push-through identity
  `(I - DK)^{-1}D = D(I - KD)^{-1}` together with the symmetry of `D` and of `K`, and no series,
  no interchange of summation and no analytic continuation is involved.  The paper writes the
  argument through the entrywise symmetry of `X = sum_n (DK)^n D`, which needs the Neumann
  series; the push-through identity replaces that series by an algebraic identity and is what is
  formalised here.

  The setting is the one of \eqref{eq:rankone}, with the two spaces kept apart, as they must be:
  `E` is the space of the solution (`\ell^1` in the paper), `F` the space of the sources and of
  the two test vectors `1` and `v` (`\ell^\infty` in the paper), `D : F \to E` the diagonal
  `diag(2q^b)`, `K : E \to F` the kernel `q^{max(a,b)}`, and `pair : F \times E \to \K` the
  pairing.  So `M_0 = D K` acts on `E`, the two sources are `Evec = D 1` and `u = D v`, and the
  four scalars of Proposition `prop:bulkdress` are the four pairings of `R_0` against `1` and
  `v`.

  Formalised here:

  * `pushThrough`   `R_0 D = D R_1`, where `R_0` inverts `I - DK` on `E` and `R_1` inverts
                    `I - KD` on `F`;
  * `X_symm`        `<f, R_0 D g> = <g, R_0 D f>`: the operator `X = R_0D` of the proof of
                    Proposition `prop:recip` is symmetric;
  * `t0_eq_b1`      **Proposition `prop:recip`, first sentence**, in the operator form the proof
                    uses: `t_0 = v^T(I - M_0)^{-1}Evec` equals `b_1 = 1^T(I - M_0)^{-1}u`.

  NOT formalised here: the two clauses of Proposition `prop:recip` that begin "equivalently".
  Both are read off the dictionary, `T_0S_e + T_1S_0 = S_1` through Proposition
  `prop:bulkdress` and `P_{11}P_{22} - P_{12}P_{21} = 1` through Corollary `cor:cocycle`, and
  neither of those is formalised.  Proposition `prop:recip` therefore keeps its star.

  No `sorry`.
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NormNum

namespace Reciprocity

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

variable (pair : F →ₗ[K] E →ₗ[K] K) (D : F →ₗ[K] E) (Kop : E →ₗ[K] F)

/-! ## The push-through identity -/

/-- `(I - DK)^{-1}D = D(I - KD)^{-1}`.  Only the left-inverse halves of the two resolvents are
used: `R_0` undoes `I - DK` on `E` and `R_1` is undone by `I - KD` on `F`. -/
theorem pushThrough (R0 : E →ₗ[K] E) (R1 : F →ₗ[K] F)
    (hR0 : ∀ x : E, R0 (x - D (Kop x)) = x)
    (hR1 : ∀ f : F, R1 f - Kop (D (R1 f)) = f) (h : F) :
    R0 (D h) = D (R1 h) := by
  have e : D (R1 h) - D (Kop (D (R1 h))) = D h := by
    rw [← map_sub, hR1 h]
  have := hR0 (D (R1 h))
  rwa [e] at this

/-! ## Symmetry of `X = R_0 D` -/

/-- The symmetry computation of the proof of Proposition `prop:recip`, with the two resolvent
arguments already substituted: `<r, D(p - KDp)> = <p, D(r - KDr)>`.  The first term is symmetric
because `D` is, the second because `D` and `K` both are. -/
theorem pair_sub_symm
    (hD : ∀ f g : F, pair f (D g) = pair g (D f))
    (hK : ∀ x y : E, pair (Kop x) y = pair (Kop y) x) (p r : F) :
    pair r (D (p - Kop (D p))) = pair p (D (r - Kop (D r))) := by
  simp only [map_sub]
  rw [hD r p, hD r (Kop (D p)), hD p (Kop (D r)), hK (D p) (D r)]

/-- **The operator `X = R_0D` is symmetric.**  This is the step of Proposition `prop:recip` that
the paper proves by the palindromic Neumann series; the push-through identity gives it without
any series. -/
theorem X_symm (R0 : E →ₗ[K] E) (R1 : F →ₗ[K] F)
    (hR0 : ∀ x : E, R0 (x - D (Kop x)) = x)
    (hR1 : ∀ f : F, R1 f - Kop (D (R1 f)) = f)
    (hD : ∀ f g : F, pair f (D g) = pair g (D f))
    (hK : ∀ x y : E, pair (Kop x) y = pair (Kop y) x) (f g : F) :
    pair f (R0 (D g)) = pair g (R0 (D f)) := by
  rw [pushThrough D Kop R0 R1 hR0 hR1 g, pushThrough D Kop R0 R1 hR0 hR1 f,
    hD f (R1 g), hD g (R1 f)]
  have h1 := pair_sub_symm pair D Kop hD hK (R1 f) (R1 g)
  rwa [hR1 f, hR1 g] at h1

/-- **Proposition `prop:recip`, first sentence.**  With `Evec = D1` and `u = Dv` the two sources
of Proposition `prop:bulkdress`, the two pairings
`t_0 = v^T(I - M_0)^{-1}Evec` and `b_1 = 1^T(I - M_0)^{-1}u` are equal. -/
theorem t0_eq_b1 (R0 : E →ₗ[K] E) (R1 : F →ₗ[K] F)
    (hR0 : ∀ x : E, R0 (x - D (Kop x)) = x)
    (hR1 : ∀ f : F, R1 f - Kop (D (R1 f)) = f)
    (hD : ∀ f g : F, pair f (D g) = pair g (D f))
    (hK : ∀ x y : E, pair (Kop x) y = pair (Kop y) x)
    (one v : F) (Evec u : E) (hE : Evec = D one) (hu : u = D v) :
    pair v (R0 Evec) = pair one (R0 u) := by
  rw [hE, hu]
  exact X_symm pair D Kop R0 R1 hR0 hR1 hD hK v one

/-- The hypothesis `hK` is not vacuous: on `E = F = Q^2` with `pair` the dot product, the map
`(x_0,x_1) |-> (x_1,0)` fails it.  The paper records the same necessity by computation, the
asymmetric kernel `q^{max(a,b)} + q^{a+2b}` giving `t_0 - b_1 = 4q^8 + O(q^9)`. -/
theorem K_symm_needed :
    ¬ ∀ a b : ℚ × ℚ, a.2 * b.1 + 0 * b.2 = b.2 * a.1 + 0 * a.2 := by
  intro h
  have h1 := h (1, 0) (0, 1)
  norm_num at h1

end Reciprocity

#print axioms Reciprocity.pushThrough
#print axioms Reciprocity.pair_sub_symm
#print axioms Reciprocity.X_symm
#print axioms Reciprocity.t0_eq_b1
#print axioms Reciprocity.K_symm_needed
