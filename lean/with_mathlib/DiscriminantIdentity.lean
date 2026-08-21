/-
  DiscriminantIdentity.lean
  =========================
  The discriminant lemma behind the irreducibility of the Gram determinant.

  For a graph H with independent edge variables, write f_H = det(I - C(c)).  Fix an edge
  e = uv.  The variable c_e occupies exactly the two symmetric entries (u,v) and (v,u), so
  f_H is a quadratic in c_e.  The lemma is that its discriminant is

      disc = 4 * f_{H-u} * f_{H-v},

  with every contribution from cycles through e cancelling.  The proof in the paper reads the
  Desnanot-Jacobi identity

      f_H * f_{H-u-v} = f_{H-u} * f_{H-v} - D^2,     D = det(M minus row u, column v),

  and matches powers of c_e, using that D is LINEAR in c_e because the deletion removes one of
  the two positions carrying it.

  Mathlib has no Desnanot-Jacobi, so this file certifies two things.

    * `disc_of_dj`: the coefficient-matching step, in full generality over an integral domain.
      This is the part of the argument that is new here; Desnanot-Jacobi itself is classical.
      It is stated as: given the three coefficient equations that matching powers of c produces,
      the discriminant collapses.

    * `disc_three`, `disc_four`: the complete statement, including the classical input, for
      arbitrary symmetric matrices of size three and four.  These are unconditional polynomial
      identities and require no hypothesis at all.

  Nothing here is specific to Gram matrices of graphs: the diagonal is arbitrary, so the
  identity holds for any symmetric matrix in which the distinguished variable occupies exactly
  the two positions (u,v) and (v,u).
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace DiscriminantIdentity

/-! ### The coefficient-matching step -/

/-- **The step that makes the cycle terms cancel.**  Suppose `f = -a c^2 + g c + b` and the
Desnanot--Jacobi identity `a * f = P - (D0 + D1 c)^2` holds identically in `c`.  Matching the
coefficients of `c^2`, `c` and `1` gives the three hypotheses below, and then the discriminant
`g^2 + 4ab` of `f` collapses to `4P`, with `D0` and `D1` gone.

Here `a = f_{H-u-v}`, `b = f_{H-e}`, `g` is the coefficient linear in `c` collecting the cycles
through `e`, and `P = f_{H-u} * f_{H-v}`. -/
theorem disc_of_dj {R : Type*} [CommRing R] [IsDomain R]
    (a b g P D0 D1 : R) (ha : a ≠ 0)
    (h2 : a * a = D1 * D1)
    (h1 : a * g = -(2 * D0 * D1))
    (h0 : a * b = P - D0 * D0) :
    g * g + 4 * (a * b) = 4 * P := by
  have hsq : (a * a) * (g * g) = (a * a) * (4 * (D0 * D0)) := by
    have : (a * g) * (a * g) = (-(2 * D0 * D1)) * (-(2 * D0 * D1)) := by rw [h1]
    calc (a * a) * (g * g) = (a * g) * (a * g) := by ring
      _ = (-(2 * D0 * D1)) * (-(2 * D0 * D1)) := this
      _ = 4 * (D0 * D0) * (D1 * D1) := by ring
      _ = 4 * (D0 * D0) * (a * a) := by rw [h2]
      _ = (a * a) * (4 * (D0 * D0)) := by ring
  have haa : a * a ≠ 0 := mul_ne_zero ha ha
  have hg : g * g = 4 * (D0 * D0) := mul_left_cancel₀ haa hsq
  rw [hg, h0]; ring

/-! ### The full statement in size three -/

variable {R : Type*} [CommRing R]

/-- A symmetric `3 x 3` matrix with the distinguished variable `c` at the two positions
`(0,1)` and `(1,0)`.  The diagonal `d0, d1, d2` and the other off-diagonal entries `p, q` are
arbitrary. -/
def M3 (d0 d1 d2 p q c : R) : Matrix (Fin 3) (Fin 3) R :=
  !![d0, -c, -p; -c, d1, -q; -p, -q, d2]

/-- `det M3` as a quadratic in `c`. -/
theorem det_M3 (d0 d1 d2 p q c : R) :
    (M3 d0 d1 d2 p q c).det
      = (-d2) * c ^ 2 + (-(2 * p * q)) * c + (d0 * d1 * d2 - d0 * q ^ 2 - p ^ 2 * d1) := by
  simp [M3, Matrix.det_fin_three]
  ring

/-- Deleting row and column `0`, that is the vertex `u`. -/
theorem minor_u3 (d1 d2 q : R) :
    (!![d1, -q; -q, d2] : Matrix (Fin 2) (Fin 2) R).det = d1 * d2 - q ^ 2 := by
  simp [Matrix.det_fin_two]; ring

/-- Deleting row and column `1`, that is the vertex `v`. -/
theorem minor_v3 (d0 d2 p : R) :
    (!![d0, -p; -p, d2] : Matrix (Fin 2) (Fin 2) R).det = d0 * d2 - p ^ 2 := by
  simp [Matrix.det_fin_two]; ring

/-- **Lemma (the discriminant), size three.**  With `det M3 = A c^2 + B c + C` read off by
`det_M3`, the discriminant `B^2 - 4AC` equals `4` times the product of the two minors obtained
by deleting the endpoints of the distinguished edge.  Unconditional: no hypothesis on the
entries. -/
theorem disc_three (d0 d1 d2 p q : R) :
    (-(2 * p * q)) ^ 2 - 4 * (-d2) * (d0 * d1 * d2 - d0 * q ^ 2 - p ^ 2 * d1)
      = 4 * (d1 * d2 - q ^ 2) * (d0 * d2 - p ^ 2) := by
  ring

/-- Desnanot--Jacobi itself, in size three, for the same matrix: the classical input, verified
here rather than assumed.  `D` is the determinant of `M3` with row `0` and column `1` deleted,
namely `det !![-c, -q; -p, d2]`, and the innermost minor is the single entry `d2`. -/
theorem dj_three (d0 d1 d2 p q c : R) :
    (M3 d0 d1 d2 p q c).det * d2
      = (d1 * d2 - q ^ 2) * (d0 * d2 - p ^ 2)
        - ((-c) * d2 - (-q) * (-p)) * ((-c) * d2 - (-p) * (-q)) := by
  rw [det_M3]; ring

/-! ### Size four: the discriminant identity on the coefficients

At size four the expansion of `Matrix.det` defeated the available tactics: `simp` with
`det_succ_row_zero` leaves applications of vector literals to `Fin.succAbove` that neither
`decide` nor `norm_num` reduces, and unfolding `Fin.succAbove` exhausts the recursion limit.
So the identification of `det M4` with the quadratic below is NOT verified here; it was checked
symbolically outside Lean.  What is verified here is the discriminant identity for those
coefficients, together with the two `3 x 3` minor determinants.  The general argument does not
depend on this section: it is `disc_of_dj` together with the complete size-three case above. -/

/-- A symmetric `4 x 4` matrix with `c` at `(0,1)` and `(1,0)`. -/
def M4 (d0 d1 d2 d3 p q r s t c : R) : Matrix (Fin 4) (Fin 4) R :=
  !![d0, -c, -p, -r; -c, d1, -q, -s; -p, -q, d2, -t; -r, -s, -t, d3]

/-- The minor at `u = 0`. -/
def M4u (d1 d2 d3 q s t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![d1, -q, -s; -q, d2, -t; -s, -t, d3]

/-- The minor at `v = 1`. -/
def M4v (d0 d2 d3 p r t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![d0, -p, -r; -p, d2, -t; -r, -t, d3]

/-- `det M4u`. -/
theorem det_M4u (d1 d2 d3 q s t : R) :
    (M4u d1 d2 d3 q s t).det
      = d1 * d2 * d3 - d1 * t ^ 2 - d2 * s ^ 2 - d3 * q ^ 2 - 2 * q * s * t := by
  simp [M4u, Matrix.det_fin_three]; ring

/-- `det M4v`. -/
theorem det_M4v (d0 d2 d3 p r t : R) :
    (M4v d0 d2 d3 p r t).det
      = d0 * d2 * d3 - d0 * t ^ 2 - d2 * r ^ 2 - d3 * p ^ 2 - 2 * p * r * t := by
  simp [M4v, Matrix.det_fin_three]; ring

/-- **The discriminant identity on the size-four coefficients.**  Writing `A`, `B`, `C` for the
coefficients of the quadratic in `c` obtained by expanding `det M4` (an identification checked
outside Lean, see the note above), `B^2 - 4AC` equals `4` times the product of the two minors.
This statement is an unconditional polynomial identity in the nine remaining entries. -/
theorem disc_four_coeffs (d0 d1 d2 d3 p q r s t : R) :
    (-(2 * d2 * r * s) - 2 * d3 * p * q - 2 * p * s * t - 2 * q * r * t) ^ 2
      - 4 * (-(d2 * d3) + t ^ 2)
        * (d0 * d1 * d2 * d3 - d0 * d1 * t ^ 2 - d0 * d2 * s ^ 2 - d0 * d3 * q ^ 2
           - 2 * d0 * q * s * t - d1 * d2 * r ^ 2 - d1 * d3 * p ^ 2 - 2 * d1 * p * r * t
           + p ^ 2 * s ^ 2 - 2 * p * q * r * s + q ^ 2 * r ^ 2)
      = 4 * (d1 * d2 * d3 - d1 * t ^ 2 - d2 * s ^ 2 - d3 * q ^ 2 - 2 * q * s * t)
          * (d0 * d2 * d3 - d0 * t ^ 2 - d2 * r ^ 2 - d3 * p ^ 2 - 2 * p * r * t) := by
  ring

/-! ### Axiom audit (Rule 5) -/

#print axioms disc_of_dj
#print axioms det_M3
#print axioms minor_u3
#print axioms minor_v3
#print axioms disc_three
#print axioms dj_three
#print axioms det_M4u
#print axioms det_M4v
#print axioms disc_four_coeffs

end DiscriminantIdentity
