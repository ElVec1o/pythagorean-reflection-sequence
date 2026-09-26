/-
  P3Separation.lean
  =================
  Core arithmetic of `rootunity_zeros/general/P3/P3_note.tex` ("P3: no Q=-1 relation for
  U and V"), specifically Lemma `lem:D` (and the Gauss's-lemma step of §`sec:proof` that
  uses it).

  Setting, exactly as in P3_note.tex §3 ("Arithmetic of t_1^* at odd order") and §4
  ("Proof of Theorem thm:main"):

    * N is odd, N >= 5 (the general statement below only needs N >= 3), zeta = e(a/N),
      K = Q(zeta), c = -2(1-zeta).
    * Fix a prime p | 2 of K and let v be *the* valuation on (an algebraic closure of)
      K_p with v(2) = 1.  Since N is odd, 2 is unramified in K and c is a 2-adic unit
      times 2, so v(c) = 1 (paragraph right before Lemma lem:D).
    * X := c^N, D_N := X(X+4).

  Lemma lem:D states:  v(D_N) = N + 2, which is odd; hence w (a root of
  w^2 - (2+X) w + 1 = 0, whose discriminant is D_N) is not in K, i.e. D_N is not a
  square in K.  The proof is two one-line valuation computations:
    v(X)   = N * v(c) = N            (multiplicativity of v on powers),
    v(X+4) = min(v(X), v(4)) = 2     (ultrametric inequality is an equality here because
                                       v(X) = N >= 3 != 2 = v(4), the sharpened-triangle
                                       step used throughout the paper's 2-adic estimates).
  Then v(D_N) = v(X) + v(X+4) = N + 2, and N odd gives N + 2 odd, so `D_N` cannot be a
  square (a square has even valuation).  This is exactly the corollary "hence w not in K,
  K(w) = K(sqrt D_N) is quadratic" recorded immediately after Lemma lem:D.

  WHAT IS FORMALIZED, PRECISELY.  `c` lives in a number field K, not in Z, so Mathlib's
  integer-valued `padicValNat`/`padicValInt` do not literally apply to it (those are
  valuations on Z/Q, not on the 2-adic completion of a number field).  The honest
  Mathlib-flavoured route is to axiomatize the *data* of a rank-one, Z-valued
  nonarchimedean valuation on a field exactly as the paper uses it (multiplicativity on
  nonzero elements, and the standard "equality when the two valuations differ" refinement
  of the ultrametric inequality that every nonarchimedean valuation satisfies -- see
  Mathlib's `Valuation`/`AddValuation` for the general framework this specializes).  Every
  hypothesis below is a genuine, always-true property of such a valuation; none of them
  encode the conclusion.  What is proved from them, with zero `sorry`, is exactly Lemma
  lem:D's displayed valuation N + 2, its oddness, and the resulting non-squareness.

  NOT formalized here (left as the paper's own inputs, not re-derived): the closed form
  of omega / t_1^*, Lemma lem:finite, Lemma lem:inv, and the sharper separation
  `v(omega - sigma omega) = 3/2` of Lemma lem:sep (which needs the Gauss-sum computation
  and is a strictly finer fact than lem:D). Also not formalized: that a *specific*
  concrete `v` with these axioms exists on `Q(zeta_N)` above 2 (that existence is
  standard algebraic number theory, not reproved here).
-/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic

namespace P3Separation

/-- A rank-one, `Z`-valued nonarchimedean valuation on a field `K`, given by exactly the
two properties used in `P3_note.tex`: multiplicativity on nonzero elements, and the
sharpened ultrametric inequality (equality with the smaller value, whenever the two
valuations compared are *different*) on nonzero sums with nonzero total. This is the
"`v` with `v(2) = 1`" of the paragraph preceding Lemma `lem:D`, packaged as data rather
than built from a fixed prime, since the paper only ever uses these two facts about it. -/
structure NonarchVal (K : Type*) [Field K] where
  /-- The valuation map. Only its values on nonzero elements are ever used. -/
  v : K → ℤ
  /-- Multiplicativity on nonzero elements. -/
  map_mul' : ∀ ⦃x y : K⦄, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  /-- The sharpened ultrametric inequality: if `x, y, x + y` are all nonzero and
  `v x ≠ v y`, then `v (x + y) = min (v x) (v y)`. This is the standard strict
  refinement of the ultrametric triangle inequality for a nonarchimedean valuation,
  used at every 2-adic step of `P3_note.tex` (e.g. in the proof of Lemma `lem:D` itself,
  and throughout Lemma `lem:sep`). -/
  map_add_of_ne' : ∀ ⦃x y : K⦄, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → v x ≠ v y →
      v (x + y) = min (v x) (v y)

namespace NonarchVal

variable {K : Type*} [Field K] (w : NonarchVal K)

/-- Valuation of a positive power of a nonzero element: `v (x ^ n) = n * v x` for `n ≥ 1`. -/
theorem map_pow {x : K} (hx : x ≠ 0) : ∀ {n : ℕ}, n ≠ 0 → w.v (x ^ n) = (n : ℤ) * w.v x
  | 0, h => absurd rfl h
  | 1, _ => by simp
  | (n + 2), _ => by
      have hxn : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
      have step : w.v (x ^ (n + 1) * x) = w.v (x ^ (n + 1)) + w.v x :=
        w.map_mul' hxn hx
      have hpow : x ^ (n + 2) = x ^ (n + 1) * x := by ring
      have ih : w.v (x ^ (n + 1)) = (n + 1 : ℤ) * w.v x := map_pow hx (Nat.succ_ne_zero n)
      rw [hpow, step, ih]
      push_cast
      ring

end NonarchVal

/-!
### Lemma `lem:D`: the valuation of `D_N = X(X+4)`, `X = c^N`
-/

/-- **Lemma `lem:D` of P3_note.tex, the valuation computation.**  Let `v` be a
nonarchimedean valuation on `K` with `v(2) = 1` (so `2 ≠ 0` and, since `N` is odd,
`v(c) = 1` as recorded right before Lemma `lem:D`).  For `N` odd with `N ≥ 3` and
`X := c ^ N`, write `D_N := X * (X + 4)`.  Then `v(D_N) = N + 2`, exactly the displayed
value in the paper. -/
theorem valuation_DN {K : Type*} [Field K] (w : NonarchVal K) {c : K} {N : ℕ}
    (hc0 : c ≠ 0) (hc : w.v c = 1) (h2ne : (2 : K) ≠ 0) (h2 : w.v 2 = 1)
    (hN_odd : Odd N) (hN3 : 3 ≤ N) (hX4 : c ^ N + 4 ≠ 0) :
    w.v (c ^ N * (c ^ N + 4)) = (N : ℤ) + 2 := by
  have hXne : c ^ N ≠ 0 := pow_ne_zero N hc0
  -- v(X) = N
  have hvX : w.v (c ^ N) = (N : ℤ) := by
    have := w.map_pow hc0 (n := N) (by omega)
    rw [this, hc, mul_one]
  -- v(4) = 2
  have h4eq : (4 : K) = 2 * 2 := by norm_num
  have h4ne : (4 : K) ≠ 0 := by rw [h4eq]; exact mul_ne_zero h2ne h2ne
  have hv4 : w.v (4 : K) = (2 : ℤ) := by
    rw [h4eq, w.map_mul' h2ne h2ne, h2]; norm_num
  -- v(X) ≠ v(4), since N ≥ 3 > 2
  have hne : w.v (c ^ N) ≠ w.v (4 : K) := by
    rw [hvX, hv4]; omega
  -- v(X + 4) = min(N, 2) = 2
  have hvsum : w.v (c ^ N + 4) = min (w.v (c ^ N)) (w.v (4 : K)) :=
    w.map_add_of_ne' hXne h4ne hX4 hne
  have hvsum' : w.v (c ^ N + 4) = (2 : ℤ) := by
    rw [hvsum, hvX, hv4]; omega
  -- multiply
  rw [w.map_mul' hXne hX4, hvX, hvsum']

/-- `N` odd forces `N + 2` odd, so `v(D_N)` is odd: the statement immediately following
Lemma `lem:D` ("which is odd"). -/
theorem odd_valuation_DN {K : Type*} [Field K] (w : NonarchVal K) {c : K} {N : ℕ}
    (hc0 : c ≠ 0) (hc : w.v c = 1) (h2ne : (2 : K) ≠ 0) (h2 : w.v 2 = 1)
    (hN_odd : Odd N) (hN3 : 3 ≤ N) (hX4 : c ^ N + 4 ≠ 0) :
    Odd (w.v (c ^ N * (c ^ N + 4))) := by
  rw [valuation_DN w hc0 hc h2ne h2 hN_odd hN3 hX4]
  obtain ⟨k, hk⟩ := hN_odd
  exact ⟨k + 1, by omega⟩

/-!
### Odd valuation implies non-square (the Gauss's-lemma-style conclusion)
-/

/-- A square has even valuation: if `y = z ^ 2` with `z ≠ 0`, then `v y = 2 * v z`. -/
theorem NonarchVal.even_valuation_of_isSquare {K : Type*} [Field K] (w : NonarchVal K)
    {z : K} (hz : z ≠ 0) : w.v (z ^ 2) = 2 * w.v z := by
  have := w.map_pow hz (n := 2) (by norm_num)
  simpa using this

/-- **The consequence drawn from Lemma `lem:D`** ("hence `w ∉ K`", i.e. `D_N` is not a
perfect square in `K`): if `v(y)` is odd then `y` is not the square of any element of
`K`. This is the field-valued analogue of "odd `2`-adic valuation implies not a perfect
square" (`padicValNat`'s integer avatar is e.g.
`padicValNat.eq_zero_of_not_dvd`-style reasoning; here the statement is genuinely about
a field element, so it is proved directly from the valuation axioms rather than quoted). -/
theorem NonarchVal.not_isSquare_of_odd_v {K : Type*} [Field K] (w : NonarchVal K)
    {y : K} (hy : y ≠ 0) (hv : Odd (w.v y)) : ¬ ∃ z : K, y = z ^ 2 := by
  rintro ⟨z, rfl⟩
  have hz : z ≠ 0 := by rintro rfl; simp at hy
  rw [w.even_valuation_of_isSquare hz] at hv
  obtain ⟨k, hk⟩ := hv
  omega

/-- **Main theorem.** Combining `lem:D` with "odd valuation implies non-square": under
the hypotheses of `P3_note.tex` §3 (`N` odd, `N ≥ 3`, `v(c) = v(2) = 1`, and
`X + 4 ≠ 0` where `X = c ^ N`), the quantity `D_N = X (X + 4)` is not a perfect square
in `K`. This is precisely the corollary stated right after Lemma `lem:D`
("Hence `w ∉ K`, `K(w) = K(√D_N)` is quadratic"), in the equivalent "not a square"
form that Gauss's lemma step of §`sec:proof` uses (`κ D_N ∉ K^{×2}` there specializes,
at `κ` a unit at `𝔭`, to `D_N` itself not being a square up to a unit factor; the pure
non-squareness of `D_N` proved here is the content that make that step possible). -/
theorem DN_not_isSquare {K : Type*} [Field K] (w : NonarchVal K) {c : K} {N : ℕ}
    (hc0 : c ≠ 0) (hc : w.v c = 1) (h2ne : (2 : K) ≠ 0) (h2 : w.v 2 = 1)
    (hN_odd : Odd N) (hN3 : 3 ≤ N) (hX4 : c ^ N + 4 ≠ 0) :
    ¬ ∃ z : K, c ^ N * (c ^ N + 4) = z ^ 2 := by
  apply w.not_isSquare_of_odd_v (mul_ne_zero (pow_ne_zero N hc0) hX4)
  exact odd_valuation_DN w hc0 hc h2ne h2 hN_odd hN3 hX4

end P3Separation
