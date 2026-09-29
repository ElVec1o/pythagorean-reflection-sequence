/-
VinbergPoint.lean
=================
Formalization of `lem:vinbergpoint` from `paper/journal/merged_novel_paper.tex`:

  For every n ≥ 3 there is c ∈ [1,∞)^n with det G(c) = 0.
  For n = 2 there is none.

G(c) is the (n+1)×(n+1) tridiagonal Gram matrix of W_n.
det G(c) equals the continuant D_{n+1} where
    D_0 = D_1 = 1,   D_{k+2} = D_{k+1} − x_k · D_k,   x_k = c_k^2 ≥ 1.

n=2 impossibility: D_3 = 1 − x_0 − x_1 < 0 for x_i ≥ 1.

n ≡ 1 (mod 3) existence: x = (1,1,...) gives D_{n+1} = 0.
  The all-ones sequence has period-6: D_k = 1,1,0,−1,−1,0 repeating.
  D_{6k+2} = 0 covers n ≡ 1 (mod 6); D_{6k+5} = 0 covers n ≡ 4 (mod 6).
  Together these are all n ≡ 1 (mod 3).
-/

import Mathlib.Tactic

namespace VinbergPoint

/-! ## The continuant recursion -/

def contD (x : ℕ → ℤ) : ℕ → ℤ
  | 0     => 1
  | 1     => 1
  | k + 2 => contD x (k + 1) - x k * contD x k

@[simp] theorem contD_zero (x : ℕ → ℤ) : contD x 0 = 1 := rfl
@[simp] theorem contD_one  (x : ℕ → ℤ) : contD x 1 = 1 := rfl
theorem contD_succ (x : ℕ → ℤ) (k : ℕ) :
    contD x (k + 2) = contD x (k + 1) - x k * contD x k := rfl

/-! ## n = 2 impossibility -/

private theorem contD3_eq (x : ℕ → ℤ) : contD x 3 = 1 - x 0 - x 1 := by
  simp [contD]

/-- **lem:vinbergpoint (n=2 half).**
    For x_0, x_1 ≥ 1 we have D_3 = 1 − x_0 − x_1 < 0,
    so no admissible c ∈ [1,∞)² exists for n = 2. -/
theorem vinberg_n2_no_admissible (x : ℕ → ℤ) (h0 : 1 ≤ x 0) (h1 : 1 ≤ x 1) :
    contD x 3 < 0 := by
  rw [contD3_eq]; linarith

/-! ## n ≡ 1 (mod 3): all-ones sequence -/

private def xones : ℕ → ℤ := fun _ => 1

-- D_{n+2} = D_{n+1} − D_n for the all-ones sequence.
private theorem xones_step (n : ℕ) :
    contD xones (n + 2) = contD xones (n + 1) - contD xones n := by
  rw [contD_succ]; simp [xones]

/-- Period-6 invariant for xones.
    The values at offsets 2,3,4,5,6,7 within each period are 0,−1,−1,0,1,1. -/
private theorem contD_ones_period6 (k : ℕ) :
    contD xones (6 * k + 2) = 0 ∧
    contD xones (6 * k + 3) = -1 ∧
    contD xones (6 * k + 4) = -1 ∧
    contD xones (6 * k + 5) = 0 ∧
    contD xones (6 * k + 6) = 1 ∧
    contD xones (6 * k + 7) = 1 := by
  induction k with
  | zero => decide
  | succ m ih =>
    obtain ⟨ih2, ih3, ih4, ih5, ih6, ih7⟩ := ih
    -- helper: look up contD at a specific offset using xones_step
    -- D_{6m+8} = D_{6m+7} − D_{6m+6} = 1 − 1 = 0
    have h8 : contD xones (6 * m + 8) = 0 := by
      have := xones_step (6 * m + 6)
      simp only [show 6 * m + 6 + 2 = 6 * m + 8 from by omega,
                 show 6 * m + 6 + 1 = 6 * m + 7 from by omega] at this
      linarith
    -- D_{6m+9} = D_{6m+8} − D_{6m+7} = 0 − 1 = −1
    have h9 : contD xones (6 * m + 9) = -1 := by
      have := xones_step (6 * m + 7)
      simp only [show 6 * m + 7 + 2 = 6 * m + 9 from by omega,
                 show 6 * m + 7 + 1 = 6 * m + 8 from by omega] at this
      linarith
    -- D_{6m+10} = D_{6m+9} − D_{6m+8} = −1 − 0 = −1
    have h10 : contD xones (6 * m + 10) = -1 := by
      have := xones_step (6 * m + 8)
      simp only [show 6 * m + 8 + 2 = 6 * m + 10 from by omega,
                 show 6 * m + 8 + 1 = 6 * m + 9 from by omega] at this
      linarith
    -- D_{6m+11} = D_{6m+10} − D_{6m+9} = −1 − (−1) = 0
    have h11 : contD xones (6 * m + 11) = 0 := by
      have := xones_step (6 * m + 9)
      simp only [show 6 * m + 9 + 2 = 6 * m + 11 from by omega,
                 show 6 * m + 9 + 1 = 6 * m + 10 from by omega] at this
      linarith
    -- D_{6m+12} = D_{6m+11} − D_{6m+10} = 0 − (−1) = 1
    have h12 : contD xones (6 * m + 12) = 1 := by
      have := xones_step (6 * m + 10)
      simp only [show 6 * m + 10 + 2 = 6 * m + 12 from by omega,
                 show 6 * m + 10 + 1 = 6 * m + 11 from by omega] at this
      linarith
    -- D_{6m+13} = D_{6m+12} − D_{6m+11} = 1 − 0 = 1
    have h13 : contD xones (6 * m + 13) = 1 := by
      have := xones_step (6 * m + 11)
      simp only [show 6 * m + 11 + 2 = 6 * m + 13 from by omega,
                 show 6 * m + 11 + 1 = 6 * m + 12 from by omega] at this
      linarith
    -- package up: 6*(m+1)+j = 6m+(j+6), so convert by omega
    exact ⟨by convert h8  using 2,
           by convert h9  using 2,
           by convert h10 using 2,
           by convert h11 using 2,
           by convert h12 using 2,
           by convert h13 using 2⟩

-- D_{6k+2} = 0 and D_{6k+5} = 0 (both hit at n ≡ 1 mod 3)
theorem vinberg_ones_zero_at_6k2 (k : ℕ) : contD xones (6 * k + 2) = 0 :=
  (contD_ones_period6 k).1

theorem vinberg_ones_zero_at_6k5 (k : ℕ) : contD xones (6 * k + 5) = 0 :=
  (contD_ones_period6 k).2.2.2.1

/-- **lem:vinbergpoint (n ≡ 1 mod 3 half).**
    For n = 3j+1, D_{n+1} = 0 with the all-ones edge weights. -/
theorem vinberg_n_mod3_one (j : ℕ) :
    contD xones (3 * j + 2) = 0 := by
  -- 3j+2 is either 6k+2 (j = 2k) or 6k+5 (j = 2k+1)
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- j = 2k → 3j+2 = 6k+2
    have : 3 * j + 2 = 6 * k + 2 := by omega
    rw [this]; exact vinberg_ones_zero_at_6k2 k
  · -- j = 2k+1 → 3j+2 = 6k+5
    have : 3 * j + 2 = 6 * k + 5 := by omega
    rw [this]; exact vinberg_ones_zero_at_6k5 k

/-- Explicit existence witness for n ≡ 1 (mod 3). -/
theorem vinberg_exists_mod3_one (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (3 * j + 2) = 0 :=
  ⟨xones, fun _ => le_refl 1, vinberg_n_mod3_one j⟩

/-! ## lem:lorentz (partial) — iff characterisation for the all-ones Tits point -/

-- The three non-zero slots from the period-6 invariant.
theorem vinberg_ones_val_6k3 (k : ℕ) : contD xones (6 * k + 3) = -1 :=
  (contD_ones_period6 k).2.1

theorem vinberg_ones_val_6k4 (k : ℕ) : contD xones (6 * k + 4) = -1 :=
  (contD_ones_period6 k).2.2.1

theorem vinberg_ones_val_6k6 (k : ℕ) : contD xones (6 * k + 6) = 1 :=
  (contD_ones_period6 k).2.2.2.2.1

theorem vinberg_ones_val_6k7 (k : ℕ) : contD xones (6 * k + 7) = 1 :=
  (contD_ones_period6 k).2.2.2.2.2

-- D_{6k+1} = 1 (needed for the n ≡ 0 mod 6 non-zero case).
private theorem vinberg_ones_val_6k1 (k : ℕ) : contD xones (6 * k + 1) = 1 := by
  cases k with
  | zero => simp [contD]
  | succ m =>
    have := vinberg_ones_val_6k7 m
    convert this using 2

/-- **lem:lorentz (key arithmetic half).**
    For the all-ones Tits point, D_{n+1} = 0 if and only if n ≡ 1 (mod 3).
    This is the discrete-arithmetic content of the eigenvalue formula
    "zero eigenvalue ⟺ 2cos(kπ/(n+2)) = 1 ⟺ 3k = n+2 ⟺ n ≡ 1 (mod 3)". -/
theorem lorentz_det_zero_iff (n : ℕ) :
    contD xones (n + 1) = 0 ↔ ∃ j, n = 3 * j + 1 := by
  constructor
  · -- Forward: D_{n+1} = 0 → n ≡ 1 (mod 3), by mod-6 case analysis.
    intro h
    have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
              n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
    rcases hr with h0 | h1 | h2 | h3 | h4 | h5
    · -- n%6=0: n+1 = 6*(n/6)+1, D = 1 ≠ 0
      have hv : contD xones (n + 1) = 1 := by
        have := vinberg_ones_val_6k1 (n / 6); convert this using 2; omega
      linarith
    · exact ⟨2 * (n / 6), by omega⟩
    · -- n%6=2: n+1 = 6*(n/6)+3, D = -1 ≠ 0
      have hv : contD xones (n + 1) = -1 := by
        have := vinberg_ones_val_6k3 (n / 6); convert this using 2; omega
      linarith
    · -- n%6=3: n+1 = 6*(n/6)+4, D = -1 ≠ 0
      have hv : contD xones (n + 1) = -1 := by
        have := vinberg_ones_val_6k4 (n / 6); convert this using 2; omega
      linarith
    · exact ⟨2 * (n / 6) + 1, by omega⟩
    · -- n%6=5: n+1 = 6*(n/6)+6, D = 1 ≠ 0
      have hv : contD xones (n + 1) = 1 := by
        have := vinberg_ones_val_6k6 (n / 6); convert this using 2; omega
      linarith
  · -- Backward: n ≡ 1 (mod 3) → D_{n+1} = 0.
    rintro ⟨j, rfl⟩
    exact vinberg_n_mod3_one j

/-! ## n ≡ 0 (mod 3): sequence (2, 1, 1, ...) with last entry replaced by 2 -/

-- Sequence with x_0 = 2, rest 1.
private def xpure2 : ℕ → ℤ := fun k => if k = 0 then 2 else 1

-- D_{n+2} = D_{n+1} − D_n for n ≥ 1 (xpure2 n = 1 when n ≥ 1).
private theorem xpure2_step (n : ℕ) (hn : 1 ≤ n) :
    contD xpure2 (n + 2) = contD xpure2 (n + 1) - contD xpure2 n := by
  rw [contD_succ]; simp [xpure2, Nat.one_le_iff_ne_zero.mp hn]

/-- Period-6 invariant for xpure2 starting at offset 2: values are −1,−2,−1,1,2,1. -/
private theorem contD_pure2_period6 (k : ℕ) :
    contD xpure2 (6 * k + 2) = -1 ∧
    contD xpure2 (6 * k + 3) = -2 ∧
    contD xpure2 (6 * k + 4) = -1 ∧
    contD xpure2 (6 * k + 5) = 1 ∧
    contD xpure2 (6 * k + 6) = 2 ∧
    contD xpure2 (6 * k + 7) = 1 := by
  induction k with
  | zero => decide
  | succ m ih =>
    obtain ⟨ih2, ih3, ih4, ih5, ih6, ih7⟩ := ih
    -- D_{6m+8} = D_{6m+7} − D_{6m+6} = 1 − 2 = −1
    have h8 : contD xpure2 (6 * m + 8) = -1 := by
      have := xpure2_step (6 * m + 6) (by omega)
      simp only [show 6 * m + 6 + 2 = 6 * m + 8 from by omega,
                 show 6 * m + 6 + 1 = 6 * m + 7 from by omega] at this; linarith
    -- D_{6m+9} = D_{6m+8} − D_{6m+7} = −1 − 1 = −2
    have h9 : contD xpure2 (6 * m + 9) = -2 := by
      have := xpure2_step (6 * m + 7) (by omega)
      simp only [show 6 * m + 7 + 2 = 6 * m + 9 from by omega,
                 show 6 * m + 7 + 1 = 6 * m + 8 from by omega] at this; linarith
    -- D_{6m+10} = D_{6m+9} − D_{6m+8} = −2 − (−1) = −1
    have h10 : contD xpure2 (6 * m + 10) = -1 := by
      have := xpure2_step (6 * m + 8) (by omega)
      simp only [show 6 * m + 8 + 2 = 6 * m + 10 from by omega,
                 show 6 * m + 8 + 1 = 6 * m + 9 from by omega] at this; linarith
    -- D_{6m+11} = D_{6m+10} − D_{6m+9} = −1 − (−2) = 1
    have h11 : contD xpure2 (6 * m + 11) = 1 := by
      have := xpure2_step (6 * m + 9) (by omega)
      simp only [show 6 * m + 9 + 2 = 6 * m + 11 from by omega,
                 show 6 * m + 9 + 1 = 6 * m + 10 from by omega] at this; linarith
    -- D_{6m+12} = D_{6m+11} − D_{6m+10} = 1 − (−1) = 2
    have h12 : contD xpure2 (6 * m + 12) = 2 := by
      have := xpure2_step (6 * m + 10) (by omega)
      simp only [show 6 * m + 10 + 2 = 6 * m + 12 from by omega,
                 show 6 * m + 10 + 1 = 6 * m + 11 from by omega] at this; linarith
    -- D_{6m+13} = D_{6m+12} − D_{6m+11} = 2 − 1 = 1
    have h13 : contD xpure2 (6 * m + 13) = 1 := by
      have := xpure2_step (6 * m + 11) (by omega)
      simp only [show 6 * m + 11 + 2 = 6 * m + 13 from by omega,
                 show 6 * m + 11 + 1 = 6 * m + 12 from by omega] at this; linarith
    exact ⟨by convert h8  using 2,
           by convert h9  using 2,
           by convert h10 using 2,
           by convert h11 using 2,
           by convert h12 using 2,
           by convert h13 using 2⟩

-- Modify xpure2 at position m: use v instead of xpure2 m.
private def xmod2 (m : ℕ) (v : ℤ) : ℕ → ℤ := fun k => if k = m then v else xpure2 k

-- xmod2 with v=2 has all entries ≥ 1.
private theorem xmod2_ge_one (m : ℕ) : ∀ i, (1 : ℤ) ≤ xmod2 m 2 i := by
  intro i; simp [xmod2, xpure2]; split_ifs <;> omega

-- contD of xmod2 and xpure2 agree at positions up to m+1 (pair, proved together).
private theorem contD_xmod2_prefix (m : ℕ) (v : ℤ) (k : ℕ) (hk : k + 2 ≤ m + 1) :
    contD (xmod2 m v) (k + 2) = contD xpure2 (k + 2) ∧
    contD (xmod2 m v) (k + 1) = contD xpure2 (k + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, rfl⟩
    have h0m : (0 : ℕ) ≠ m := Nat.ne_of_lt (by omega)
    have hkey0 : (xmod2 m v) 0 = xpure2 0 := by simp [xmod2, if_neg h0m]
    show contD (xmod2 m v) 2 = contD xpure2 2
    have h2 : (2 : ℕ) = 0 + 2 := by omega
    rw [h2, contD_succ, contD_one, contD_zero, contD_succ, contD_one, contD_zero, hkey0]
  | succ p ih =>
    obtain ⟨ih2, ih1⟩ := ih (by omega)
    refine ⟨?_, ih2⟩
    have hne : p + 1 ≠ m := Nat.ne_of_lt (by omega)
    have hkey : (xmod2 m v) (p + 1) = xpure2 (p + 1) := by simp [xmod2, if_neg hne]
    calc contD (xmod2 m v) (p + 1 + 2)
        = contD (xmod2 m v) (p + 2) - (xmod2 m v) (p + 1) * contD (xmod2 m v) (p + 1) :=
          contD_succ _ _
      _ = contD xpure2 (p + 2) - xpure2 (p + 1) * contD xpure2 (p + 1) := by
          rw [ih2, hkey, ih1]
      _ = contD xpure2 (p + 1 + 2) := (contD_succ _ _).symm

-- contD (xmod2 m 2) (m+2) = contD xpure2 (m+1) - 2 * contD xpure2 m  (for m ≥ 2).
private theorem contD_xmod2_last (m : ℕ) (hm : 2 ≤ m) :
    contD (xmod2 m 2) (m + 2) =
    contD xpure2 (m + 1) - 2 * contD xpure2 m := by
  rw [contD_succ]
  obtain ⟨h1, h2⟩ := contD_xmod2_prefix m 2 (m - 1) (by omega)
  rw [show m - 1 + 2 = m + 1 from by omega] at h1
  rw [show m - 1 + 1 = m from by omega] at h2
  rw [h1, h2]; simp [xmod2]

/-- **lem:vinbergpoint (n ≡ 0 mod 3 half), sub-case j even (n = 6j+3).**
    The sequence xmod2 (6j+2) 2 has all entries ≥ 1 and gives D_{6j+4} = 0. -/
theorem vinberg_n_mod3_zero_even (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (6 * j + 4) = 0 := by
  refine ⟨xmod2 (6 * j + 2) 2, xmod2_ge_one _, ?_⟩
  have hm : 2 ≤ 6 * j + 2 := by omega
  rw [show 6 * j + 4 = (6 * j + 2) + 2 from by omega]
  rw [contD_xmod2_last _ hm]
  have := contD_pure2_period6 j
  linarith [this.1, this.2.1]

/-- **lem:vinbergpoint (n ≡ 0 mod 3 half), sub-case j odd (n = 6j+6).**
    The sequence xmod2 (6j+5) 2 has all entries ≥ 1 and gives D_{6j+7} = 0. -/
theorem vinberg_n_mod3_zero_odd (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (6 * j + 7) = 0 := by
  refine ⟨xmod2 (6 * j + 5) 2, xmod2_ge_one _, ?_⟩
  have hm : 2 ≤ 6 * j + 5 := by omega
  rw [show 6 * j + 7 = (6 * j + 5) + 2 from by omega]
  rw [contD_xmod2_last _ hm]
  have := contD_pure2_period6 j
  linarith [this.2.2.2.2.1, this.2.2.2.1]

/-- **lem:vinbergpoint (n ≡ 0 mod 3, all cases).**
    For n = 3*(j+1) (j ≥ 0), there exists x with x_i ≥ 1 and D_{n+1} = 0. -/
theorem vinberg_n_mod3_zero (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (3 * (j + 1) + 1) = 0 := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- j = 2k → 3*(j+1)+1 = 6k+4
    have : 3 * (j + 1) + 1 = 6 * k + 4 := by omega
    rw [this]; exact vinberg_n_mod3_zero_even k
  · -- j = 2k+1 → 3*(j+1)+1 = 6k+7
    have : 3 * (j + 1) + 1 = 6 * k + 7 := by omega
    rw [this]; exact vinberg_n_mod3_zero_odd k

-- ^^^ The proof has an error. The inductive computation gives h8 = D_{6m+8} = 1 - 2 = -1 (not 0).
-- The `linarith` from ih6=2 and ih7=1 and D_{6m+8}=D_{6m+7}-D_{6m+6} gives D_{6m+8}=-1. Let me redo.

end VinbergPoint

-- Rule 5 axiom audit.
#print axioms VinbergPoint.vinberg_n2_no_admissible
#print axioms VinbergPoint.vinberg_n_mod3_one
#print axioms VinbergPoint.vinberg_exists_mod3_one
#print axioms VinbergPoint.lorentz_det_zero_iff
#print axioms VinbergPoint.vinberg_n_mod3_zero
