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

/-- The all-ones sequence x_k = 1, used for the path Gram matrix Tits point. -/
def xones : ℕ → ℤ := fun _ => 1

-- D_{n+2} = D_{n+1} − D_n for the all-ones sequence.
theorem xones_step (n : ℕ) :
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

/-! ## n ≡ 2 (mod 3): sequence (2, 1, 3, 1, 1, ...) with last entry replaced by 3 -/

-- Sequence with x_0 = 2, x_2 = 3, rest 1.
private def xpure3 : ℕ → ℤ := fun k => if k = 0 then 2 else if k = 2 then 3 else 1

-- D_{n+2} = D_{n+1} − D_n for n ≥ 3 (xpure3 n = 1 when n ≥ 3).
private theorem xpure3_step (n : ℕ) (hn : 3 ≤ n) :
    contD xpure3 (n + 2) = contD xpure3 (n + 1) - contD xpure3 n := by
  rw [contD_succ]; simp [xpure3, show n ≠ 0 from by omega, show n ≠ 2 from by omega]

/-- Period-6 invariant for xpure3 starting at offset 4: values are 1,3,2,−1,−3,−2. -/
private theorem contD_pure3_period6 (k : ℕ) :
    contD xpure3 (6 * k + 4) = 1 ∧
    contD xpure3 (6 * k + 5) = 3 ∧
    contD xpure3 (6 * k + 6) = 2 ∧
    contD xpure3 (6 * k + 7) = -1 ∧
    contD xpure3 (6 * k + 8) = -3 ∧
    contD xpure3 (6 * k + 9) = -2 := by
  induction k with
  | zero => decide
  | succ m ih =>
    obtain ⟨ih4, ih5, ih6, ih7, ih8, ih9⟩ := ih
    have h10 : contD xpure3 (6 * m + 10) = 1 := by
      have := xpure3_step (6 * m + 8) (by omega)
      simp only [show 6 * m + 8 + 2 = 6 * m + 10 from by omega,
                 show 6 * m + 8 + 1 = 6 * m + 9 from by omega] at this; linarith
    have h11 : contD xpure3 (6 * m + 11) = 3 := by
      have := xpure3_step (6 * m + 9) (by omega)
      simp only [show 6 * m + 9 + 2 = 6 * m + 11 from by omega,
                 show 6 * m + 9 + 1 = 6 * m + 10 from by omega] at this; linarith
    have h12 : contD xpure3 (6 * m + 12) = 2 := by
      have := xpure3_step (6 * m + 10) (by omega)
      simp only [show 6 * m + 10 + 2 = 6 * m + 12 from by omega,
                 show 6 * m + 10 + 1 = 6 * m + 11 from by omega] at this; linarith
    have h13 : contD xpure3 (6 * m + 13) = -1 := by
      have := xpure3_step (6 * m + 11) (by omega)
      simp only [show 6 * m + 11 + 2 = 6 * m + 13 from by omega,
                 show 6 * m + 11 + 1 = 6 * m + 12 from by omega] at this; linarith
    have h14 : contD xpure3 (6 * m + 14) = -3 := by
      have := xpure3_step (6 * m + 12) (by omega)
      simp only [show 6 * m + 12 + 2 = 6 * m + 14 from by omega,
                 show 6 * m + 12 + 1 = 6 * m + 13 from by omega] at this; linarith
    have h15 : contD xpure3 (6 * m + 15) = -2 := by
      have := xpure3_step (6 * m + 13) (by omega)
      simp only [show 6 * m + 13 + 2 = 6 * m + 15 from by omega,
                 show 6 * m + 13 + 1 = 6 * m + 14 from by omega] at this; linarith
    exact ⟨by convert h10 using 2, by convert h11 using 2, by convert h12 using 2,
           by convert h13 using 2, by convert h14 using 2, by convert h15 using 2⟩

-- Modify xpure3 at position m: use v instead of xpure3 m.
private def xmod3 (m : ℕ) (v : ℤ) : ℕ → ℤ := fun k => if k = m then v else xpure3 k

-- xmod3 with v=3 has all entries ≥ 1.
private theorem xmod3_ge_one (m : ℕ) : ∀ i, (1 : ℤ) ≤ xmod3 m 3 i := by
  intro i; simp [xmod3, xpure3]; split_ifs <;> omega

-- contD of xmod3 and xpure3 agree at positions up to m+1.
private theorem contD_xmod3_prefix (m : ℕ) (v : ℤ) (k : ℕ) (hk : k + 2 ≤ m + 1) :
    contD (xmod3 m v) (k + 2) = contD xpure3 (k + 2) ∧
    contD (xmod3 m v) (k + 1) = contD xpure3 (k + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, rfl⟩
    have h0m : (0 : ℕ) ≠ m := Nat.ne_of_lt (by omega)
    have hkey0 : (xmod3 m v) 0 = xpure3 0 := by simp [xmod3, if_neg h0m]
    show contD (xmod3 m v) 2 = contD xpure3 2
    have h2 : (2 : ℕ) = 0 + 2 := by omega
    rw [h2, contD_succ, contD_one, contD_zero, contD_succ, contD_one, contD_zero, hkey0]
  | succ p ih =>
    obtain ⟨ih2, ih1⟩ := ih (by omega)
    refine ⟨?_, ih2⟩
    have hne : p + 1 ≠ m := Nat.ne_of_lt (by omega)
    have hkey : (xmod3 m v) (p + 1) = xpure3 (p + 1) := by simp [xmod3, if_neg hne]
    calc contD (xmod3 m v) (p + 1 + 2)
        = contD (xmod3 m v) (p + 2) - (xmod3 m v) (p + 1) * contD (xmod3 m v) (p + 1) :=
          contD_succ _ _
      _ = contD xpure3 (p + 2) - xpure3 (p + 1) * contD xpure3 (p + 1) := by
          rw [ih2, hkey, ih1]
      _ = contD xpure3 (p + 1 + 2) := (contD_succ _ _).symm

-- contD (xmod3 m 3) (m+2) = contD xpure3 (m+1) - 3 * contD xpure3 m.
private theorem contD_xmod3_last (m : ℕ) (hm : 1 ≤ m) :
    contD (xmod3 m 3) (m + 2) =
    contD xpure3 (m + 1) - 3 * contD xpure3 m := by
  rw [contD_succ]
  obtain ⟨h1, h2⟩ := contD_xmod3_prefix m 3 (m - 1) (by omega)
  rw [show m - 1 + 2 = m + 1 from by omega] at h1
  rw [show m - 1 + 1 = m from by omega] at h2
  rw [h1, h2]; simp [xmod3]

/-- **lem:vinbergpoint (n ≡ 2 mod 3), sub-case j odd (n = 6j+5).**
    xmod3 (6j+4) 3 has all entries ≥ 1 and gives D_{6j+6} = 0. -/
theorem vinberg_n_mod3_two_a (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (6 * j + 6) = 0 := by
  refine ⟨xmod3 (6 * j + 4) 3, xmod3_ge_one _, ?_⟩
  rw [show 6 * j + 6 = (6 * j + 4) + 2 from by omega]
  rw [contD_xmod3_last _ (by omega)]
  have := contD_pure3_period6 j
  linarith [this.1, this.2.1]

/-- **lem:vinbergpoint (n ≡ 2 mod 3), sub-case j even (n = 6j+8).**
    xmod3 (6j+7) 3 has all entries ≥ 1 and gives D_{6j+9} = 0. -/
theorem vinberg_n_mod3_two_b (j : ℕ) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (6 * j + 9) = 0 := by
  refine ⟨xmod3 (6 * j + 7) 3, xmod3_ge_one _, ?_⟩
  rw [show 6 * j + 9 = (6 * j + 7) + 2 from by omega]
  rw [contD_xmod3_last _ (by omega)]
  have := contD_pure3_period6 j
  linarith [this.2.2.2.1, this.2.2.2.2.1]

/-- **lem:vinbergpoint (n ≡ 2 mod 3, all cases, j ≥ 1).**
    For j ≥ 1, there exists x with x_i ≥ 1 and D_{3*j+3} = 0  (covers n = 3j+2 ≥ 5). -/
theorem vinberg_n_mod3_two (j : ℕ) (hj : 1 ≤ j) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (3 * j + 3) = 0 := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- j = 2k (even, k ≥ 1): 3*j+3 = 6k+3 = 6*(k-1)+9
    have hk1 : 1 ≤ k := by omega
    have heq : 3 * j + 3 = 6 * (k - 1) + 9 := by omega
    rw [heq]; exact vinberg_n_mod3_two_b (k - 1)
  · -- j = 2k+1 (odd): 3*j+3 = 6k+6
    have heq : 3 * j + 3 = 6 * k + 6 := by omega
    rw [heq]; exact vinberg_n_mod3_two_a k

/-- **lem:vinbergpoint**: for every n ≥ 3, ∃ x with x_i ≥ 1 and D_{n+1} = 0. -/
theorem lem_vinbergpoint (n : ℕ) (hn : 3 ≤ n) :
    ∃ (x : ℕ → ℤ), (∀ i, 1 ≤ x i) ∧ contD x (n + 1) = 0 := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · -- n ≡ 0 mod 3: n = 3*(n/3), n/3 ≥ 1
    have hq : 1 ≤ n / 3 := by omega
    have heq : n + 1 = 3 * (n / 3 - 1 + 1) + 1 := by omega
    rw [heq]; exact vinberg_n_mod3_zero (n / 3 - 1)
  · -- n ≡ 1 mod 3: n = 3*(n/3)+1
    have heq : n + 1 = 3 * (n / 3) + 2 := by omega
    rw [heq]; exact vinberg_exists_mod3_one (n / 3)
  · -- n ≡ 2 mod 3: n = 3*(n/3)+2, n/3 ≥ 1 (since n ≥ 5)
    have hq : 1 ≤ n / 3 := by omega
    have heq : n + 1 = 3 * (n / 3) + 3 := by omega
    rw [heq]; exact vinberg_n_mod3_two (n / 3) hq

end VinbergPoint

-- Rule 5 axiom audit.
#print axioms VinbergPoint.vinberg_n2_no_admissible
#print axioms VinbergPoint.vinberg_n_mod3_one
#print axioms VinbergPoint.vinberg_exists_mod3_one
#print axioms VinbergPoint.lorentz_det_zero_iff
#print axioms VinbergPoint.vinberg_n_mod3_zero
#print axioms VinbergPoint.lem_vinbergpoint
