/-
The bridge between the two models of a word.

`RotationRelations.lean` works with words as lists of letters and classifies
the reduced words of length `2n` whose invariants are `c_2 = 0`, `c_1 = n - 1`:
they are exactly the `markBoth n a j` for admissible `(a, j)`.
`CoxeterTorsion.lean` works with the free product `W_m = D_m * C_2` and decides
which elements of the shape `u₀ x₂ u₁ x₂ u₂` have finite order.

This file connects them. `ev` evaluates a letter list in `W m`, sending the two
apex reflections into the dihedral factor and the third into the other factor;
`ev_markBoth_lt` and `ev_markBoth_gt` compute `ev (markBoth n a j)` as a
`blockWord` with explicit dihedral blocks, and `unique_finite_order` then reads
off Theorem "Rotation relations"(iii): among the `c²` admissible words exactly
one has finite order in `W_m`, namely `a = 0`, `j = n - 1`, which is
`r₂ (r₀ r₁)^c r₂`.
-/
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import RotationRelations
import CoxeterTorsion

namespace CoxeterTorsion

open Monoid RotationRelations

/-- The dihedral factor, as a subgroup of `W m`. -/
def emb (m : ℕ) : DihedralGroup m →* W m := CoprodI.of (M := factor m) (i := 0)

/-- The generators of the triangle group inside `W m`. The two apex
reflections `r₀ = sr 1` and `r₁ = sr 0` go into the dihedral factor, chosen so
that `r₁ r₀ = r 1` is the rotation by one step; `r₂` is the generator of the
other factor. -/
def gen (m : ℕ) (l : Letter) : W m :=
  if l = 0 then emb m (DihedralGroup.sr 1)
  else if l = 1 then emb m (DihedralGroup.sr 0)
  else t m

/-- The element of `W m` represented by a word. -/
def ev (m : ℕ) (w : List Letter) : W m := (w.map (gen m)).prod

@[simp] theorem ev_nil (m : ℕ) : ev m [] = 1 := rfl

@[simp] theorem ev_cons (m : ℕ) (l : Letter) (w : List Letter) :
    ev m (l :: w) = gen m l * ev m w := rfl

theorem ev_append (m : ℕ) (w₁ w₂ : List Letter) :
    ev m (w₁ ++ w₂) = ev m w₁ * ev m w₂ := by
  simp [ev, List.map_append, List.prod_append]

/-- Shorthand for a rotation of the dihedral factor, viewed in `W m`. -/
def R (m : ℕ) (k : ZMod m) : W m := emb m (DihedralGroup.r k)

/-- Shorthand for a reflection of the dihedral factor, viewed in `W m`. -/
def S (m : ℕ) (k : ZMod m) : W m := emb m (DihedralGroup.sr k)

theorem S_mul_S (m : ℕ) (i k : ZMod m) : S m i * S m k = R m (k - i) := by
  rw [S, S, R, ← map_mul, DihedralGroup.sr_mul_sr]

theorem S_mul_R (m : ℕ) (i k : ZMod m) : S m i * R m k = S m (i + k) := by
  rw [S, R, S, ← map_mul, DihedralGroup.sr_mul_r]

theorem R_mul_S (m : ℕ) (i k : ZMod m) : R m i * S m k = S m (k - i) := by
  rw [R, S, S, ← map_mul, DihedralGroup.r_mul_sr]

theorem R_mul_R (m : ℕ) (i k : ZMod m) : R m i * R m k = R m (i + k) := by
  rw [R, R, R, ← map_mul, DihedralGroup.r_mul_r]

theorem gen_zero (m : ℕ) : gen m 0 = S m 1 := rfl

theorem gen_one (m : ℕ) : gen m 1 = S m 0 := rfl

theorem gen_two (m : ℕ) : gen m 2 = t m := rfl

/-- A run of plain blocks is a rotation. -/
theorem ev_plain (m k : ℕ) : ev m (plain k) = R m (k : ZMod m) := by
  induction k with
  | zero =>
      show (1 : W m) = R m ((0 : ℕ) : ZMod m)
      rw [R, Nat.cast_zero, DihedralGroup.r_zero, map_one]
  | succ k ih =>
      rw [plain, ev_cons, ev_cons, ih, gen_one, gen_zero, ← mul_assoc, S_mul_S,
        R_mul_R]
      congr 1
      push_cast
      ring

/-! ### The two marked patterns as explicit concatenations -/

theorem markY_eq : ∀ (n i : ℕ), i < n →
    markY n i = plain i ++ [1, 2] ++ plain (n - i - 1) := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ n ih =>
      intro i h
      match i with
      | 0 => simp [markY, plain]
      | i + 1 =>
          have hi : i < n := by omega
          simp [markY, plain, ih i hi]

theorem markX_eq : ∀ (n i : ℕ), i < n →
    markX n i = plain i ++ [2, 0] ++ plain (n - i - 1) := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ n ih =>
      intro i h
      match i with
      | 0 => simp [markX, plain]
      | i + 1 =>
          have hi : i < n := by omega
          simp [markX, plain, ih i hi]

theorem markBoth_lt : ∀ (n a j : ℕ), a < j → j < n →
    markBoth n a j
      = plain a ++ [2, 0] ++ plain (j - a - 1) ++ [1, 2] ++ plain (n - j - 1) := by
  intro n
  induction n with
  | zero => intro a j _ h; omega
  | succ n ih =>
      intro a j haj hjn
      match a, j with
      | 0, 0 => omega
      | 0, j + 1 =>
          have hj : j < n := by omega
          simp [markBoth, plain, markY_eq n j hj]
      | a + 1, 0 => omega
      | a + 1, j + 1 =>
          have h1 : a < j := by omega
          have h2 : j < n := by omega
          simp [markBoth, plain, ih a j h1 h2]

theorem markBoth_gt : ∀ (n a j : ℕ), j < a → a < n →
    markBoth n a j
      = plain j ++ [1, 2] ++ plain (a - j - 1) ++ [2, 0] ++ plain (n - a - 1) := by
  intro n
  induction n with
  | zero => intro a j _ h; omega
  | succ n ih =>
      intro a j hja han
      match a, j with
      | 0, _ => omega
      | a + 1, 0 =>
          have ha : a < n := by omega
          simp [markBoth, plain, markX_eq n a ha]
      | a + 1, j + 1 =>
          have h1 : j < a := by omega
          have h2 : a < n := by omega
          simp [markBoth, plain, ih a j h1 h2]

/-! ### Evaluating the marked patterns -/

theorem blockWord_eq (m : ℕ) (u₀ u₁ u₂ : DihedralGroup m) :
    blockWord m u₀ u₁ u₂ = emb m u₀ * t m * emb m u₁ * t m * emb m u₂ := rfl

theorem ev_two_zero (m : ℕ) : ev m [2, 0] = t m * S m 1 := by
  simp [ev, gen_zero, gen_two]

theorem ev_one_two (m : ℕ) : ev m [1, 2] = S m 0 * t m := by
  simp [ev, gen_one, gen_two]

/-- Adjacent letters of the dihedral factor fuse. -/
theorem emb_fuse (m : ℕ) (x y : DihedralGroup m) (z : W m) :
    emb m x * (emb m y * z) = emb m (x * y) * z := by
  rw [← mul_assoc, ← map_mul]

theorem ev_markBoth_lt (m n a j : ℕ) (haj : a < j) (hjn : j < n) :
    ev m (markBoth n a j)
      = blockWord m (DihedralGroup.r (a : ZMod m))
          (DihedralGroup.sr 1 *
            (DihedralGroup.r ((j - a - 1 : ℕ) : ZMod m) * DihedralGroup.sr 0))
          (DihedralGroup.r ((n - j - 1 : ℕ) : ZMod m)) := by
  rw [markBoth_lt n a j haj hjn]
  simp only [ev_append, ev_plain, ev_two_zero, ev_one_two, blockWord_eq, R, S,
    mul_assoc, emb_fuse]

theorem ev_markBoth_gt (m n a j : ℕ) (hja : j < a) (han : a < n) :
    ev m (markBoth n a j)
      = blockWord m (DihedralGroup.r (j : ZMod m) * DihedralGroup.sr 0)
          (DihedralGroup.r ((a - j - 1 : ℕ) : ZMod m))
          (DihedralGroup.sr 1 * DihedralGroup.r ((n - a - 1 : ℕ) : ZMod m)) := by
  rw [markBoth_gt n a j hja han]
  simp only [ev_append, ev_plain, ev_two_zero, ev_one_two, blockWord_eq, R, S,
    mul_assoc, emb_fuse, ← map_mul]

/-! ### The dihedral arithmetic -/

theorem mid_lt (m : ℕ) (d : ZMod m) :
    (DihedralGroup.sr 1 * (DihedralGroup.r d * DihedralGroup.sr 0) :
      DihedralGroup m) = DihedralGroup.r (-(d + 1)) := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
  congr 1
  ring

theorem outer_gt (m : ℕ) (x y : ZMod m) :
    ((DihedralGroup.sr 1 * DihedralGroup.r x) *
      (DihedralGroup.r y * DihedralGroup.sr 0) : DihedralGroup m)
      = DihedralGroup.r (-(y + x + 1)) := by
  rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
  congr 1
  ring

/-- A natural number below the modulus is zero in `ZMod m` only if it is zero. -/
theorem cast_eq_zero_iff_of_lt {m k : ℕ} (h : k < m) :
    ((k : ℕ) : ZMod m) = 0 ↔ k = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro hd
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact hk
    · exact absurd (Nat.le_of_dvd hk hd) (by omega)
  · rintro rfl
    exact dvd_zero m

theorem r_eq_one_iff (m k : ℕ) (h : k < m) :
    (DihedralGroup.r ((k : ℕ) : ZMod m) : DihedralGroup m) = 1 ↔ k = 0 := by
  rw [DihedralGroup.one_def, DihedralGroup.r.injEq, cast_eq_zero_iff_of_lt h]

/-! ### Theorem "Rotation relations"(iii) -/

/-- Among the admissible words of length `2n`, exactly one has finite order in
`W_m = D_m * C_2`, namely the one with the first mark in block `0` and the
second in block `n - 1`; that word is `r₂ (r₀ r₁)^c r₂` with `c = n - 1`.
The hypothesis `n ≤ m` is the range `c ≤ m - 1` of the paper. -/
theorem unique_finite_order (m n a j : ℕ) (hnm : n ≤ m) (h : Admissible n a j) :
    IsOfFinOrder (ev m (markBoth n a j)) ↔ (a = 0 ∧ j = n - 1) := by
  obtain ⟨han, hjn, hja, hajj⟩ := h
  have hm : 0 < m := by omega
  rcases lt_trichotomy a j with hlt | heq | hgt
  · -- the two marks in increasing order
    rw [ev_markBoth_lt m n a j hlt hjn, mid_lt]
    have hd : ((j - a - 1 : ℕ) : ZMod m) + 1 = ((j - a : ℕ) : ZMod m) := by
      have : (j - a : ℕ) = (j - a - 1 : ℕ) + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [hd]
    have hu₁ : (DihedralGroup.r (-((j - a : ℕ) : ZMod m)) : DihedralGroup m) ≠ 1 := by
      rw [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq, neg_eq_zero,
        cast_eq_zero_iff_of_lt (by omega : j - a < m)]
      omega
    rw [finite_order_iff m hm _ _ _ hu₁, DihedralGroup.r_mul_r]
    have hsum : ((n - j - 1 : ℕ) : ZMod m) + ((a : ℕ) : ZMod m)
        = ((n - j - 1 + a : ℕ) : ZMod m) := by push_cast; ring
    rw [hsum, r_eq_one_iff m _ (by omega)]
    omega
  · exact absurd heq.symm hja
  · -- the two marks in decreasing order: no word of finite order here
    rw [ev_markBoth_gt m n a j hgt han]
    have hu₁ : (DihedralGroup.r ((a - j - 1 : ℕ) : ZMod m) : DihedralGroup m) ≠ 1 := by
      rw [ne_eq, r_eq_one_iff m _ (by omega)]
      omega
    rw [finite_order_iff m hm _ _ _ hu₁, outer_gt]
    have hsum : ((j : ℕ) : ZMod m) + ((n - a - 1 : ℕ) : ZMod m) + 1
        = ((j + (n - a - 1) + 1 : ℕ) : ZMod m) := by push_cast; ring
    constructor
    · intro hc
      rw [DihedralGroup.one_def, DihedralGroup.r.injEq, neg_eq_zero, hsum,
        cast_eq_zero_iff_of_lt (by omega : j + (n - a - 1) + 1 < m)] at hc
      omega
    · intro hc
      exfalso
      obtain ⟨ha0, _⟩ := hc
      omega

end CoxeterTorsion
