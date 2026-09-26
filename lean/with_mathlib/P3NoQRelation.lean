/-
  P3NoQRelation.lean
  ==================
  A Lean formalization of the core arithmetic fact behind
  `code/zeta_probe/rootunity_zeros/general/P3/P3_note.tex` (Theorem `thm:main`: U and V satisfy no
  Q=-1 linear q-difference relation), together with the logical skeleton that turns that fact,
  plus the field-theoretic step the note proves by hand, into the final contradiction of
  `\S5` (Proof of Theorem thm:main).

  WHAT IS FORMALIZED, PRECISELY.

  The note works with a fixed prime `\mathfrak p | 2` of `K = Q(\zeta)` (`\zeta` a primitive
  `N`-th root of unity, `N` odd), and its valuation `v` on (an algebraic closure of) the
  completion `K_{\mathfrak p}`, normalised by `v(2) = 1`.  We do not build that number-theoretic
  valuation from scratch (2-adic ramification in cyclotomic fields, Kummer theory, Gauss sums,
  etc. -- all the content of Lemmas `lem:finite`/`lem:inv`/`lem:sep`).  Instead we abstract
  "a discrete, rank-one, Z-valued valuation on a field" by the two algebraic laws the note
  actually uses (multiplicativity, and the ultrametric equality when the two valuations differ),
  which is exactly what any such valuation satisfies.  Given that abstraction:

  * `DiscVal.valuation_D` is a full, sorry-free proof of Lemma `lem:D`:
        v(X) = N  and  N > 2   =>   v(X*(X+4)) = N + 2.
    (In the note, X = c^N, N >= 5 odd, v(c) = 1, so v(X) = N; this file takes v(X) = N as an
    explicit hypothesis, since producing it requires the cyclotomic-field bookkeeping of the note's
    \S2 preamble, not the valuation-theoretic content of lem:D itself.)

  * `DiscVal.not_square_of_odd_val` is a full, sorry-free proof of the standard valuation fact
    used at the very end of \S5: an element of odd valuation is not a square.

  * `DiscVal.P3_contradiction` assembles these into the exact contradiction of \S5 ("But
    v_{\mathfrak p}(\kappa_U D_N) = 0 + N + 2 is odd, a contradiction"), with the parts of the
    argument NOT re-proved here recorded as explicit hypotheses:
      - `hDval : v D = N + 2`           (Lemma lem:D, proved here as `valuation_D`)
      - `hval_kappa : v \kappa = 0`      (the note's computation that \kappa_U, \kappa_V are
                                          2-units, \S5 "are elements of K^x with v_p = e_0-e_1 = 0")
      - `hsquare : \kappa * D` is a square in K(w)
                                          (the note's Lemma lem:resid + Lemma lem:sep + Galois /
                                          Kummer argument "K(sqrt(\kappa)) = K(m) = K(w) = K(sqrt D_N),
                                          so \kappa D_N in K^{x2}" -- this is the genuinely
                                          number-theoretic step, resting on P1f/P1g's
                                          computer-assisted inputs, and is NOT re-derived here).
    Given those three hypotheses, `P3_contradiction` derives `False` purely by the valuation
    arithmetic, exactly reproducing the note's closing sentence.

  This is honestly partial: the field K(w), the Galois action, and the fact that \kappa*D is a
  square are all taken as a hypothesis (`hsquare`), standing for the hand-proved-but-unformalized
  Lemmas lem:finite/lem:inv/lem:sep plus \S5's Mobius-map computation. What IS fully machine
  checked is (a) the 2-adic valuation identity v(X(X+4)) = N+2 for N odd > 2, and (b) that this,
  together with `hsquare`, is logically sufficient to contradict `hval_kappa`, matching the note's
  proof structure exactly.
-/

import Mathlib.Tactic

/-- A discrete, integer-valued valuation on a field, presented by exactly the two laws used in
`P3_note.tex`: multiplicativity on nonzero elements, and the ultrametric equality
`v(x+y) = min(v x, v y)` when `v x ≠ v y` (the case actually used; when the two valuations agree
the note never needs the inequality `v(x+y) ≥ min(v x, v y)` in isolation). Any genuine discrete
valuation (e.g. the 2-adic valuation on an algebraic closure of a `𝔭`-adic completion, as used in
the note) satisfies both laws. -/
structure DiscVal (K : Type*) [Field K] where
  v : K → ℤ
  v_mul : ∀ ⦃x y : K⦄, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  v_add : ∀ ⦃x y : K⦄, x ≠ 0 → y ≠ 0 → v x ≠ v y → v (x + y) = min (v x) (v y)

namespace DiscVal

variable {K : Type*} [Field K] (V : DiscVal K)

/-- Squares have even valuation: `v(m*m) = 2 * v m`. -/
theorem v_sq {m : K} (hm : m ≠ 0) : V.v (m * m) = 2 * V.v m := by
  rw [V.v_mul hm hm]; ring

/-- **Lemma `lem:D` of P3\_note.tex.**
If `v(X) = N` for some `N` with `2 < N` (in the note: `X = c^N`, `N ≥ 5` odd, `v(c) = 1`),
and `four = two * two` with `v(two) = 1` (in the note: the prime `𝔭 ∣ 2`, `v(2) = 1`),
then `D := X * (X + four)` satisfies `v(D) = N + 2`.

This is exactly the note's computation: "`v(X) = N`, and `v(X+4) = 2` because `N ≥ 3`.
The discriminant of `w² - (2+X)w + 1` is `D_N`." -/
theorem valuation_D
    (X two four : K) (N : ℕ)
    (hX0 : X ≠ 0) (hXN : V.v X = (N : ℤ))
    (htwo0 : two ≠ 0) (hv2 : V.v two = 1)
    (hfour : four = two * two)
    (hN : 2 < N)
    (hD0 : X + four ≠ 0) :
    V.v (X * (X + four)) = (N : ℤ) + 2 := by
  have hfour0 : four ≠ 0 := by
    rw [hfour]; exact mul_ne_zero htwo0 htwo0
  have hv4 : V.v four = 2 := by
    rw [hfour, V.v_mul htwo0 htwo0, hv2]; norm_num
  have hne : V.v X ≠ V.v four := by
    rw [hXN, hv4]; omega
  have hsum : V.v (X + four) = min (V.v X) (V.v four) := V.v_add hX0 hfour0 hne
  have hval : V.v (X + four) = 2 := by rw [hsum, hXN, hv4]; omega
  rw [V.v_mul hX0 hD0, hXN, hval]

/-- Standard valuation fact used at the end of `\S5`: an element of *odd* valuation is not a
square in the field. -/
theorem not_square_of_odd_val {κ : K} {n : ℤ} (hκ : κ ≠ 0) (hv : V.v κ = n) (hodd : Odd n) :
    ¬ ∃ m : K, m ≠ 0 ∧ κ = m * m := by
  rintro ⟨m, hm0, rfl⟩
  have hsq := V.v_sq hm0
  rw [hv] at hsq
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **The closing contradiction of `\S5` of P3\_note.tex.**
Given:
* `hDval`   : `v(D) = N + 2` (supplied by `valuation_D` above, i.e. Lemma `lem:D`);
* `hkval`   : `v(κ) = 0` (the note's `\S5`: "`κ_U`, `κ_V` are elements of `K^×` with
              `v_𝔭 = e_0 - e_1 = 0`");
* `hsquare` : `κ * D` is a square in `K` (the note's `K(√κ) = K(w) = K(√D)` step, resting on
              Lemma `lem:resid` and the Galois/Kummer argument of Lemmas `lem:inv`/`lem:sep` --
              NOT reproved here, recorded as an explicit hypothesis);
and `N` odd, this derives `False`, exactly as the note's "`v_𝔭(κ_U D_N) = 0 + N + 2` is odd,
a contradiction." -/
theorem P3_contradiction
    (N : ℕ) (hNodd : Odd N)
    (D κ : K) (hD0 : D ≠ 0)
    (hDval : V.v D = (N : ℤ) + 2)
    (hkval : V.v κ = 0)
    (hsquare : ∃ m : K, m ≠ 0 ∧ κ * D = m * m) :
    False := by
  obtain ⟨m, hm0, hkD⟩ := hsquare
  have hprod0 : κ * D ≠ 0 := hkD ▸ mul_ne_zero hm0 hm0
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hprod0
  have hval : V.v (κ * D) = (N : ℤ) + 2 := by
    rw [V.v_mul hκ0 hD0, hkval, hDval]; ring
  have hsq := V.v_sq hm0
  rw [← hkD, hval] at hsq
  obtain ⟨k, hk⟩ := hNodd
  omega

end DiscVal
