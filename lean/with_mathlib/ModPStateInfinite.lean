/-
  ModPStateInfinite.lean
  ======================
  Paper "extra", Proposition `prop:modp-state-infinite`: for every prime p the mod-p state
  space S_p is infinite, witnessed by the family {((XY)^n, t_n) : n >= 1}.

  WHAT THE PROPOSITION REDUCES TO.  The pairs live in Q x (M/pM).  Two pairs are distinct as
  soon as their FIRST components differ, so it suffices that the rotations (XY)^n are pairwise
  distinct, that is, that XY has infinite order.  Nothing about the translation parts t_n, and
  nothing about p, enters that statement; this is why the conclusion holds uniformly in p, and
  the argument below is correspondingly p-free.

  THE ARGUMENT.  For the 3-4-5 triangle, XY is the rotation with cos = 3/5, sin = 4/5, that is
  multiplication by the unit complex number (3+4i)/5.  Writing (3+4i)^n = a_n + b_n i, the
  rotation by n steps is trivial exactly when (3+4i)^n = 5^n, that is when b_n = 0.

  The usual proof factors 3+4i = (2+i)^2 and 5 = (2+i)(2-i) in the Gaussian integers and
  appeals to unique factorization.  That is unnecessary.  The pair (a_n, b_n) satisfies

      (a_{n+1}, b_{n+1}) = (3 a_n - 4 b_n,  4 a_n + 3 b_n),

  and modulo 5 this map fixes (3, 4):  3*3 + 4 = 13 = 3,  4*3 + 3*4 = 24 = 4  (mod 5).  Since
  (a_1, b_1) = (3, 4), we get b_n = 4 mod 5 for every n >= 1, so b_n is never zero.  The proof
  is a one-line induction and needs no algebraic number theory at all.

  SCOPE.  That XY is this particular rotation is the paper's setup for the 3-4-5 reflection
  group and is not re-derived here; what is proved is that the rotation so described has
  infinite order, which is the content the proposition actually uses.  The translation parts
  t_n are not modelled, because as noted they are not needed for distinctness.
-/

import Mathlib

namespace ModPStateInfinite

/-- `rot n = (a_n, b_n)` where `(3+4i)^n = a_n + b_n i`. -/
def rot : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => (3 * (rot n).1 - 4 * (rot n).2, 4 * (rot n).1 + 3 * (rot n).2)

@[simp] theorem rot_zero : rot 0 = (1, 0) := rfl

@[simp] theorem rot_succ_fst (n : Nat) :
    (rot (n + 1)).1 = 3 * (rot n).1 - 4 * (rot n).2 := rfl

@[simp] theorem rot_succ_snd (n : Nat) :
    (rot (n + 1)).2 = 4 * (rot n).1 + 3 * (rot n).2 := rfl

/-- **The norm is multiplicative**: `|(3+4i)^n|^2 = 25^n`.  Used only to know the rotation is
    never the zero vector. -/
theorem rot_norm (n : Nat) : (rot n).1 ^ 2 + (rot n).2 ^ 2 = 25 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    simp only [rot_succ_fst, rot_succ_snd]
    have h : (3 * (rot k).1 - 4 * (rot k).2) ^ 2 + (4 * (rot k).1 + 3 * (rot k).2) ^ 2
        = 25 * ((rot k).1 ^ 2 + (rot k).2 ^ 2) := by ring
    rw [h, ih, pow_succ]
    ring

/-- **The mod-5 invariant.**  The multiplication map fixes `(3, 4)` modulo 5, and `(a_1, b_1)`
    is `(3, 4)`, so every later term is congruent to it. -/
theorem rot_mod5 (m : Nat) : (rot (m + 1)).1 % 5 = 3 ∧ (rot (m + 1)).2 % 5 = 4 := by
  induction m with
  | zero => decide
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : (rot (k + 1 + 1)).1 = 3 * (rot (k + 1)).1 - 4 * (rot (k + 1)).2 := rfl
    have e2 : (rot (k + 1 + 1)).2 = 4 * (rot (k + 1)).1 + 3 * (rot (k + 1)).2 := rfl
    rw [e1, e2]
    omega

/-- **The imaginary part never vanishes**, for `n >= 1`.  This is the whole content: the
    rotation by `n` steps is never trivial. -/
theorem rot_snd_ne_zero (m : Nat) : (rot (m + 1)).2 ≠ 0 := by
  have h := (rot_mod5 m).2
  omega

/-- Equivalently, `(3+4i)^n` is never the real number `5^n` for `n >= 1`. -/
theorem rot_ne_real (m : Nat) : rot (m + 1) ≠ (5 ^ (m + 1), 0) := by
  intro h
  exact rot_snd_ne_zero m (by rw [h])

/-- **The group law**: `(3+4i)^(m+n)` is the complex product of `(3+4i)^m` and `(3+4i)^n`. -/
theorem rot_add (m n : Nat) :
    (rot (m + n)).1 = (rot m).1 * (rot n).1 - (rot m).2 * (rot n).2 ∧
    (rot (m + n)).2 = (rot m).1 * (rot n).2 + (rot m).2 * (rot n).1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : m + (k + 1) = (m + k) + 1 := rfl
    rw [e]
    simp only [rot_succ_fst, rot_succ_snd, h1, h2]
    exact ⟨by ring, by ring⟩

/-- **Advancing by `k >= 1` steps always changes the rotation.**  Normalising by the modulus,
    the rotation after `m + k` steps is never equal to the rotation after `m` steps; the
    comparison is written multiplicatively to avoid subtraction. -/
theorem rot_advance_ne (m k : Nat) :
    ¬ ((rot (m + (k + 1))).1 = 5 ^ (k + 1) * (rot m).1 ∧
       (rot (m + (k + 1))).2 = 5 ^ (k + 1) * (rot m).2) := by
  rintro ⟨e1, e2⟩
  obtain ⟨h1, h2⟩ := rot_add m (k + 1)
  rw [h1] at e1
  rw [h2] at e2
  -- With U = u - 5^(k+1), the two equations read xU - yv = 0 and xv + yU = 0.
  -- Then x*(second) - y*(first) gives (x^2 + y^2) * v = 0.
  have key : ((rot m).1 ^ 2 + (rot m).2 ^ 2) * (rot (k + 1)).2 = 0 := by
    linear_combination (rot m).1 * e2 - (rot m).2 * e1
  rw [rot_norm m] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero m (by norm_num))
  · exact rot_snd_ne_zero k h

/-- **The rotations are pairwise distinct**, hence `XY` has infinite order and the family
    `{((XY)^n, t_n)}` is infinite in `Q x (M/pM)` for every prime `p`: distinctness is decided
    by the first component alone, and that component does not involve `p`. -/
theorem rotations_pairwise_distinct (m n : Nat) (hmn : m < n) :
    ¬ ((rot n).1 * 5 ^ m = (rot m).1 * 5 ^ n ∧
       (rot n).2 * 5 ^ m = (rot m).2 * 5 ^ n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  rintro ⟨e1, e2⟩
  have hne : (5 : Int) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have h5 : (5 : Int) ^ (m + (k + 1)) = 5 ^ (k + 1) * 5 ^ m := by rw [pow_add]; ring
  rw [h5] at e1 e2
  refine rot_advance_ne m k ⟨?_, ?_⟩
  · refine mul_right_cancel₀ hne ?_
    rw [e1]; ring
  · refine mul_right_cancel₀ hne ?_
    rw [e2]; ring

/-! ### Axiom audit (Rule 5) -/

#print axioms rot_norm
#print axioms rot_mod5
#print axioms rot_snd_ne_zero
#print axioms rot_ne_real
#print axioms rot_add
#print axioms rot_advance_ne
#print axioms rotations_pairwise_distinct

end ModPStateInfinite
