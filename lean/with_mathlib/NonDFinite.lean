import Mathlib
import ODEPoles

/-!
# NonDFinite — thm:nonDfinite and prop:noqdiff (i), contracting case (Room E, seat E2)

* `ode_propagates`: identity theorem for the equation `∑ a_i f^{(i)} = b` (meromorphic identity
  theorem, `meromorphicOrderAt_ne_top_of_isPreconnected`); from a punctured neighbourhood of one
  point of a preconnected `Ω` to a punctured neighbourhood of every point of `Ω`.
* `lead_zero_at_pole` / `lead_zero_at_pole_inhom`: global lem:odeposes; every pole in `Ω` is a
  zero of `a_r` (homogeneous) or of `b·a_r` (inhomogeneous, via the operator `b·d/dz − b'`,
  `reduce_local`).  The local input is `ODEPoles.meromorphicOrderAt_nonneg_of_ode`.
* `eqOn_zero_of_infinite_zeros`: isolated zeros on a compact subset.
* `nonDfinite_abstract` (poles in a compact `K ⊆ Ω`), `nonDfinite_hom`, `nonDfinite_inhom`
  (two domains `Ω ⊆ U`, `K ⊆ U` compact, poles in `Ω ∩ K`).
* `nonDfinite_disc`: the paper's situation, poles in the open disc (accumulating only at the
  boundary allowed), coefficients and `b` holomorphic on `|z| < R`, `R > 1`.
* `not_DFinite_poly`: polynomial coefficients, polynomial right-hand side.
* `no_qdiff_contracting`: `∑ a_i(x) f(Q^i x) = b(x)` is impossible for `0 < |Q| < 1`.

A pole is `meromorphicOrderAt f p < 0` (`IsPole`).  All equations are assumed only on a punctured
neighbourhood `𝓝[≠] z₀` of one point `z₀` of the domain.  No `sorry`, no `native_decide`.
-/

open Filter Topology Finset

namespace NonDFinite

variable {f : ℂ → ℂ}

/-- The linear differential operator `∑_{i ≤ r} a_i f^{(i)}`. -/
noncomputable def odeOp (r : ℕ) (a : ℕ → ℂ → ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z

/-- `f` has a pole at `p`. -/
def IsPole (f : ℂ → ℂ) (p : ℂ) : Prop := meromorphicOrderAt f p < 0

lemma meromorphicOn_iteratedDeriv {Ω : Set ℂ} (hf : MeromorphicOn f Ω) (i : ℕ) :
    MeromorphicOn (iteratedDeriv i f) Ω := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterated_deriv

lemma meromorphicOn_odeOp {Ω : Set ℂ} (hf : MeromorphicOn f Ω) (r : ℕ) (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω) : MeromorphicOn (odeOp r a f) Ω := by
  intro z hz
  unfold odeOp
  refine MeromorphicAt.fun_sum fun i hi => ?_
  have hir : i ≤ r := by rw [mem_range] at hi; omega
  exact (ha i hir z hz).meromorphicAt.mul (meromorphicOn_iteratedDeriv hf i z hz)

/-- **Identity theorem for the equation.** If `L f = b` holds on a punctured neighbourhood of one
point of a preconnected set `Ω` on which everything is meromorphic, it holds on a punctured
neighbourhood of every point of `Ω`. -/
theorem ode_propagates {Ω : Set ℂ} (hΩ : IsPreconnected Ω) (hf : MeromorphicOn f Ω)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω)
    {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = b z) {p : ℂ} (hp : p ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] p, odeOp r a f z = b z := by
  set F : ℂ → ℂ := fun z => odeOp r a f z - b z with hF
  have hFm : MeromorphicOn F Ω := fun z hz =>
    (meromorphicOn_odeOp hf r a ha z hz).sub (hb z hz).meromorphicAt
  have h0 : meromorphicOrderAt F z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hode.mono fun z hz => by simp [hF, hz])
  have hp' : meromorphicOrderAt F p = ⊤ := by
    by_contra hne
    exact hFm.meromorphicOrderAt_ne_top_of_isPreconnected hΩ hp hz₀ hne h0
  exact (meromorphicOrderAt_eq_top_iff.mp hp').mono fun z hz => sub_eq_zero.mp hz

/-- **lem:odeposes, homogeneous, global form.** Every pole in `Ω` of a meromorphic solution is a
zero of the leading coefficient. -/
theorem lead_zero_at_pole {Ω : Set ℂ} (hΩ : IsPreconnected Ω) (hf : MeromorphicOn f Ω)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = 0)
    {p : ℂ} (hp : p ∈ Ω) (hpole : IsPole f p) : a r p = 0 := by
  by_contra hne
  have hloc := ode_propagates hΩ hf r a ha (b := fun _ => 0) analyticOnNhd_const hz₀ hode hp
  have := ODEPoles.meromorphicOrderAt_nonneg_of_ode (hf p hp) r a
    (fun i hi => ha i hi p hp) hne hloc
  exact absurd hpole (not_lt.mpr this)

/-- An infinite subset of a compact set accumulates somewhere in it. -/
lemma exists_frequently_of_infinite {K S : Set ℂ} (hK : IsCompact K) (hSK : S ⊆ K)
    (hS : S.Infinite) : ∃ x ∈ K, ∃ᶠ z in 𝓝[≠] x, z ∈ S := by
  obtain ⟨x, hxK, hacc⟩ := hS.exists_accPt_of_subset_isCompact hK hSK
  exact ⟨x, hxK, accPt_iff_frequently_nhdsNE.mp hacc⟩

/-- **Isolated zeros on a compact set.** An analytic function on a preconnected set `U`
vanishing on an infinite subset of a compact `K ⊆ U` vanishes identically on `U`. -/
theorem eqOn_zero_of_infinite_zeros {U K S : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U) (hSK : S ⊆ K) (hS : S.Infinite)
    (hgS : ∀ z ∈ S, g z = 0) : Set.EqOn g 0 U := by
  obtain ⟨x, hxK, hfr⟩ := exists_frequently_of_infinite hK hSK hS
  exact hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hKU hxK)
    (hfr.mono fun z hz => hgS z hz)

/-- **thm:nonDfinite, homogeneous, two-domain form.**  `f` is meromorphic on a preconnected `Ω`,
the coefficients are analytic on `Ω`, the leading coefficient is analytic and `≢ 0` on a
preconnected `U` containing a compact `K`, and `f` has infinitely many poles in `Ω ∩ K`.
Then `f` satisfies no equation `∑ a_i f^{(i)} = 0` near any point of `Ω`. -/
theorem nonDfinite_hom {Ω U K : Set ℂ} (hΩ : IsPreconnected Ω) (hU : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hf : MeromorphicOn f Ω)
    (hpoles : {p | p ∈ Ω ∧ p ∈ K ∧ IsPole f p}.Infinite)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω)
    (har : AnalyticOnNhd ℂ (a r) U) (hne : ∃ w ∈ U, a r w ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = 0) : False := by
  obtain ⟨w, hwU, hw⟩ := hne
  refine hw (eqOn_zero_of_infinite_zeros har hU hK hKU (fun p hp => hp.2.1) hpoles ?_ hwU)
  intro p hp
  exact lead_zero_at_pole hΩ hf r a ha hz₀ hode hp.1 hp.2.2

/-- **thm:nonDfinite, abstract form (homogeneous).** -/
theorem nonDfinite_abstract {Ω K : Set ℂ} (hΩ : IsPreconnected Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hf : MeromorphicOn f Ω) (hpoles : {p | p ∈ K ∧ IsPole f p}.Infinite)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω) (hne : ∃ w ∈ Ω, a r w ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = 0) : False := by
  refine nonDfinite_hom hΩ hΩ hK hKΩ hf ?_ r a ha (ha r le_rfl) hne hz₀ hode
  convert hpoles using 1
  ext p
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hKΩ h.1, h.1, h.2⟩⟩

/-! ### The inhomogeneous case: apply `b·d/dz − b'` -/

/-- Coefficients of `b·(L f)' − b'·(L f)`, an operator of order `r+1`. -/
noncomputable def redCoeff (r : ℕ) (a : ℕ → ℂ → ℂ) (b : ℂ → ℂ) (j : ℕ) : ℂ → ℂ := fun z =>
  (if j ≤ r then b z * deriv (a j) z - deriv b z * a j z else 0) +
    (if j = 0 then 0 else b z * a (j - 1) z)

lemma redCoeff_top (r : ℕ) (a : ℕ → ℂ → ℂ) (b : ℂ → ℂ) (z : ℂ) :
    redCoeff r a b (r + 1) z = b z * a r z := by
  simp [redCoeff]

lemma redCoeff_analyticAt {r : ℕ} {a : ℕ → ℂ → ℂ} {b : ℂ → ℂ} {p : ℂ}
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (hb : AnalyticAt ℂ b p) :
    ∀ j ≤ r + 1, AnalyticAt ℂ (redCoeff r a b j) p := by
  intro j hj
  unfold redCoeff
  refine AnalyticAt.add ?_ ?_
  · by_cases h : j ≤ r
    · simp only [h, if_true]
      exact (hb.mul (ha j h).deriv).sub (hb.deriv.mul (ha j h))
    · simp only [h, if_false]; exact analyticAt_const
  · by_cases h : j = 0
    · simp only [h, if_true]; exact analyticAt_const
    · simp only [h, if_false]
      exact hb.mul (ha (j - 1) (by omega))

/-- Reindexing identity behind the reduction. -/
lemma sum_reindex (r : ℕ) (A B g : ℕ → ℂ) :
    ∑ j ∈ range (r + 1 + 1), ((if j ≤ r then A j else 0) + (if j = 0 then 0 else B (j - 1))) * g j
      = ∑ i ∈ range (r + 1), (A i * g i + B i * g (i + 1)) := by
  simp only [add_mul, sum_add_distrib]
  congr 1
  · rw [sum_range_succ]
    simp only [show ¬ (r + 1 ≤ r) by omega, if_false, zero_mul, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    simp [show i ≤ r by omega]
  · rw [sum_range_succ']
    simp

/-- **Local reduction.** Near a point `p` where `a_i`, `b` are analytic and `f` is meromorphic,
`L f = b` on a punctured neighbourhood implies `L' f = 0` there, with `L'` of order `r+1` and
leading coefficient `b·a_r`. -/
theorem reduce_local {r : ℕ} {a : ℕ → ℂ → ℂ} {b : ℂ → ℂ} {p : ℂ} (hfp : MeromorphicAt f p)
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (hb : AnalyticAt ℂ b p)
    (hode : ∀ᶠ z in 𝓝[≠] p, odeOp r a f z = b z) :
    ∀ᶠ z in 𝓝[≠] p, odeOp (r + 1) (redCoeff r a b) f z = 0 := by
  have h1 : ∀ᶠ y in 𝓝[≠] p, odeOp r a f =ᶠ[𝓝 y] b := by
    have := eventually_eventually_nhdsWithin.mpr hode
    filter_upwards [this, self_mem_nhdsWithin] with y hy hyp
    rwa [isOpen_compl_singleton.nhdsWithin_eq hyp] at hy
  have hA : ∀ᶠ y in 𝓝[≠] p, ∀ i ∈ range (r + 1), AnalyticAt ℂ (a i) y := by
    rw [eventually_all_finset]
    intro i hi
    have hir : i ≤ r := by rw [mem_range] at hi; omega
    exact nhdsWithin_le_nhds (ha i hir).eventually_analyticAt
  have hB : ∀ᶠ y in 𝓝[≠] p, AnalyticAt ℂ b y := nhdsWithin_le_nhds hb.eventually_analyticAt
  filter_upwards [h1, hA, hB, hfp.eventually_analyticAt] with y hy hAy hBy hfy
  have hit : ∀ i, AnalyticAt ℂ (iteratedDeriv i f) y := by
    intro i
    induction i with
    | zero => simpa using hfy
    | succ i ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hderiv : deriv (odeOp r a f) y
      = ∑ i ∈ range (r + 1), (deriv (a i) y * iteratedDeriv i f y
          + a i y * iteratedDeriv (i + 1) f y) := by
    unfold odeOp
    rw [deriv_fun_sum (A := fun i z => a i z * iteratedDeriv i f z) fun i hi =>
      ((hAy i hi).differentiableAt.mul (hit i).differentiableAt)]
    refine sum_congr rfl fun i hi => ?_
    rw [deriv_fun_mul (hAy i hi).differentiableAt (hit i).differentiableAt, iteratedDeriv_succ]
  have hval : odeOp r a f y = b y := hy.eq_of_nhds
  have hdb : deriv (odeOp r a f) y = deriv b y := hy.deriv_eq
  have key : odeOp (r + 1) (redCoeff r a b) f y
      = b y * (∑ i ∈ range (r + 1), (deriv (a i) y * iteratedDeriv i f y
          + a i y * iteratedDeriv (i + 1) f y))
        - deriv b y * ∑ i ∈ range (r + 1), a i y * iteratedDeriv i f y := by
    unfold odeOp
    simp only [redCoeff]
    rw [sum_reindex r (fun j => b y * deriv (a j) y - deriv b y * a j y) (fun i => b y * a i y)
      (fun j => iteratedDeriv j f y), mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hsum : ∑ i ∈ range (r + 1), a i y * iteratedDeriv i f y = odeOp r a f y := rfl
  rw [key, ← hderiv, hsum, hval, hdb]
  ring

/-- **lem:odeposes, inhomogeneous, global form.** Every pole in `Ω` of a meromorphic solution of
`L f = b` is a zero of `b·a_r`. -/
theorem lead_zero_at_pole_inhom {Ω : Set ℂ} (hΩ : IsPreconnected Ω) (hf : MeromorphicOn f Ω)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω)
    {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = b z)
    {p : ℂ} (hp : p ∈ Ω) (hpole : IsPole f p) : b p * a r p = 0 := by
  by_contra hne
  have hloc := ode_propagates hΩ hf r a ha hb hz₀ hode hp
  have hred := reduce_local (hf p hp) (fun i hi => ha i hi p hp) (hb p hp) hloc
  have := ODEPoles.meromorphicOrderAt_nonneg_of_ode (hf p hp) (r + 1) (redCoeff r a b)
    (redCoeff_analyticAt (fun i hi => ha i hi p hp) (hb p hp)) (by rwa [redCoeff_top]) hred
  exact absurd hpole (not_lt.mpr this)

/-- **thm:nonDfinite, inhomogeneous, two-domain form.**  `Ω ⊆ U`, both preconnected, `Ω` open;
`f` meromorphic on `Ω` with infinitely many poles in `Ω ∩ K`, `K ⊆ U` compact; `a_0,…,a_r`
analytic on `Ω`; `a_r` and `b` analytic on `U`, `a_r ≢ 0` on `U`.  Then `∑ a_i f^{(i)} = b`
fails near every point of `Ω`.  (No hypothesis on `b` beyond analyticity: `b ≡ 0` is allowed.) -/
theorem nonDfinite_inhom {Ω U K : Set ℂ} (hΩo : IsOpen Ω) (hΩ : IsPreconnected Ω)
    (hU : IsPreconnected U) (hΩU : Ω ⊆ U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : MeromorphicOn f Ω) (hpoles : {p | p ∈ Ω ∧ p ∈ K ∧ IsPole f p}.Infinite)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) Ω)
    (har : AnalyticOnNhd ℂ (a r) U) (hne : ∃ w ∈ U, a r w ≠ 0)
    {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = b z) : False := by
  by_cases hb0 : ∃ w ∈ Ω, b w ≠ 0
  · obtain ⟨w, hwΩ, hw⟩ := hb0
    obtain ⟨v, hvU, hv⟩ := hne
    obtain ⟨x, hxK, hfr⟩ := exists_frequently_of_infinite hK (fun p hp => hp.2.1) hpoles
    have hfr' : ∃ᶠ z in 𝓝[≠] x, b z = 0 ∨ a r z = 0 := by
      refine hfr.mono fun p hp => ?_
      exact mul_eq_zero.mp
        (lead_zero_at_pole_inhom hΩ hf r a ha (hb.mono hΩU) hz₀ hode hp.1 hp.2.2)
    rcases frequently_or_distrib.mp hfr' with h | h
    · exact hw (hb.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hKU hxK) h (hΩU hwΩ))
    · exact hv (har.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hKU hxK) h hvU)
  · push Not at hb0
    refine nonDfinite_hom hΩ hU hK hKU hf hpoles r a ha har hne hz₀ ?_
    have hin : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Ω :=
      nhdsWithin_le_nhds (hΩo.mem_nhds hz₀)
    filter_upwards [hode, hin] with z hz hzΩ
    rw [hz, hb0 z hzΩ]

/-! ### The unit disc: poles accumulating at the boundary -/

open Metric in
/-- **thm:nonDfinite, disc form (the paper's situation).**  `f` is meromorphic on the open unit
disc and has infinitely many poles there (they may accumulate only at the boundary).  Then `f`
satisfies no equation `∑_{i ≤ r} a_i f^{(i)} = b` near any point of the disc, with `a_i`, `b`
holomorphic on a disc `|z| < R`, `R > 1` (a neighbourhood of the closed unit disc) and
`a_r ≢ 0`. -/
theorem nonDfinite_disc {R : ℝ} (hR : 1 < R) (hf : MeromorphicOn f (ball 0 1))
    (hpoles : {p | p ∈ ball (0 : ℂ) 1 ∧ IsPole f p}.Infinite)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) (ball 0 R))
    (hne : ∃ w ∈ ball (0 : ℂ) R, a r w ≠ 0)
    {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b (ball 0 R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hode : ∀ᶠ z in 𝓝[≠] z₀, odeOp r a f z = b z) :
    False := by
  have hsub : ball (0 : ℂ) 1 ⊆ ball 0 R := ball_subset_ball hR.le
  refine nonDfinite_inhom (K := closedBall 0 1) isOpen_ball (convex_ball 0 1).isPreconnected
    (convex_ball 0 R).isPreconnected hsub (isCompact_closedBall 0 1)
    (closedBall_subset_ball hR) hf ?_ r a (fun i hi => (ha i hi).mono hsub) (ha r le_rfl) hne hb
    hz₀ hode
  convert hpoles using 1
  ext p
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ball_subset_closedBall h.1, h.2⟩⟩

open Metric Polynomial in
/-- **thm:nonDfinite, polynomial form.**  A function meromorphic on the open unit disc with
infinitely many poles there is not `D`-finite: it satisfies no equation
`∑_{i ≤ r} P_i(z) f^{(i)}(z) = B(z)` with polynomial coefficients and `P_r ≠ 0`, on a punctured
neighbourhood of any point of the disc. -/
theorem not_DFinite_poly (hf : MeromorphicOn f (ball 0 1))
    (hpoles : {p | p ∈ ball (0 : ℂ) 1 ∧ IsPole f p}.Infinite) :
    ¬ ∃ (r : ℕ) (P : ℕ → ℂ[X]) (B : ℂ[X]) (z₀ : ℂ), z₀ ∈ ball (0 : ℂ) 1 ∧ P r ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, ∑ i ∈ range (r + 1), (P i).eval z * iteratedDeriv i f z = B.eval z := by
  rintro ⟨r, P, B, z₀, hz₀, hPr, hode⟩
  have hana : ∀ Q : ℂ[X], AnalyticOnNhd ℂ (fun z => Q.eval z) Set.univ :=
    fun Q z _ => Q.differentiable.analyticAt z
  have hne : ∃ w ∈ (Set.univ : Set ℂ), (P r).eval w ≠ 0 := by
    by_contra h
    push Not at h
    exact hPr (Polynomial.funext fun w => by simpa using h w trivial)
  refine nonDfinite_inhom (U := Set.univ) (K := closedBall 0 1) isOpen_ball
    (convex_ball 0 1).isPreconnected isPreconnected_univ (Set.subset_univ _)
    (isCompact_closedBall 0 1) (Set.subset_univ _) hf ?_ r (fun i z => (P i).eval z)
    (fun i _ => (hana (P i)).mono (Set.subset_univ _)) (hana (P r)) hne (hana B) hz₀ hode
  convert hpoles using 1
  ext p
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ball_subset_closedBall h.1, h.2⟩⟩

/-! ### Linear `q`-difference equations with `0 < |Q| < 1` (prop:noqdiff (i), contracting case) -/

/-- The `q`-difference operator `∑_{i ≤ r} a_i(x) f(Q^i x)`. -/
noncomputable def qOp (r : ℕ) (Q : ℂ) (a : ℕ → ℂ → ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun x => ∑ i ∈ range (r + 1), a i x * f (Q ^ i * x)

/-- `f` is removable at `p`: off `p` it agrees near `p` with a function analytic at `p`. -/
def Tame (f : ℂ → ℂ) (p : ℂ) : Prop := ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ f =ᶠ[𝓝[≠] p] g

lemma not_isPole_of_tame {p : ℂ} (h : Tame f p) : ¬ IsPole f p := by
  obtain ⟨g, hg, hfg⟩ := h
  unfold IsPole
  rw [meromorphicOrderAt_congr hfg]
  exact not_lt.mpr hg.meromorphicOrderAt_nonneg

lemma tame_of_not_isPole {p : ℂ} (hf : MeromorphicAt f p) (h : ¬ IsPole f p) : Tame f p := by
  have h0 : 0 ≤ meromorphicOrderAt f p := not_lt.mp h
  by_cases htop : meromorphicOrderAt f p = ⊤
  · exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp htop⟩
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨g, hg, _, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    have hn0 : 0 ≤ n := by rw [← hn] at h0; exact_mod_cast h0
    refine ⟨fun z => (z - p) ^ n.toNat * g z,
      ((analyticAt_id.sub analyticAt_const).pow _).mul hg, ?_⟩
    filter_upwards [hfg] with z hz
    rw [hz, smul_eq_mul, ← zpow_natCast, Int.toNat_of_nonneg hn0]

/-- Transport along `x ↦ c x`, `c ≠ 0`. -/
lemma tame_comp_mul {c p : ℂ} (hc : c ≠ 0) (h : Tame f (c * p)) :
    Tame (fun x => f (c * x)) p := by
  obtain ⟨g, hg, hfg⟩ := h
  have hlin : AnalyticAt ℂ (fun x : ℂ => c * x) p := analyticAt_const.mul analyticAt_id
  refine ⟨fun x => g (c * x), hg.comp hlin, ?_⟩
  have ht : Tendsto (fun x : ℂ => c * x) (𝓝[≠] p) (𝓝[≠] (c * p)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hlin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun hEq => hx (mul_left_cancel₀ hc hEq)
  exact ht.eventually hfg

/-- **Local step.**  If `a_0(p) ≠ 0`, the equation holds near `p`, and `f` is removable at every
`Q^i p`, `1 ≤ i ≤ r`, then `f` is removable at `p`. -/
theorem tame_of_qdiff {r : ℕ} {Q : ℂ} (hQ0 : Q ≠ 0) {a : ℕ → ℂ → ℂ} {b : ℂ → ℂ} {p : ℂ}
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (hb : AnalyticAt ℂ b p) (ha0 : a 0 p ≠ 0)
    (hsucc : ∀ i ∈ range r, Tame f (Q ^ (i + 1) * p))
    (hq : ∀ᶠ x in 𝓝[≠] p, qOp r Q a f x = b x) : Tame f p := by
  have hT : ∀ i ∈ range r, Tame (fun x => f (Q ^ (i + 1) * x)) p := fun i hi =>
    tame_comp_mul (pow_ne_zero _ hQ0) (hsucc i hi)
  have hT' : ∀ i : ℕ, ∃ g : ℂ → ℂ, i ∈ range r →
      AnalyticAt ℂ g p ∧ (fun x => f (Q ^ (i + 1) * x)) =ᶠ[𝓝[≠] p] g := by
    intro i
    by_cases hi : i ∈ range r
    · obtain ⟨g, hg⟩ := hT i hi; exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
  choose G hG using hT'
  set H : ℂ → ℂ := fun x => (b x - ∑ i ∈ range r, a (i + 1) x * G i x) / a 0 x with hH
  refine ⟨H, ?_, ?_⟩
  · refine AnalyticAt.fun_div (hb.sub (Finset.analyticAt_fun_sum _ fun i hi => ?_)) (ha 0 (by omega)) ha0
    have hir : i < r := by rwa [mem_range] at hi
    exact (ha (i + 1) (by omega)).mul (hG i hi).1
  · have hall : ∀ᶠ x in 𝓝[≠] p, ∀ i ∈ range r, f (Q ^ (i + 1) * x) = G i x := by
      rw [eventually_all_finset]; intro i hi; exact (hG i hi).2
    have hne : ∀ᶠ x in 𝓝[≠] p, a 0 x ≠ 0 :=
      nhdsWithin_le_nhds ((ha 0 (by omega)).continuousAt.eventually_ne ha0)
    filter_upwards [hq, hall, hne] with x hx hxall hx0
    rw [hH]
    simp only
    rw [eq_div_iff hx0]
    have hsplit : qOp r Q a f x
        = ∑ i ∈ range r, a (i + 1) x * f (Q ^ (i + 1) * x) + a 0 x * f x := by
      unfold qOp; rw [sum_range_succ']; simp
    have hsum : ∑ i ∈ range r, a (i + 1) x * f (Q ^ (i + 1) * x)
        = ∑ i ∈ range r, a (i + 1) x * G i x :=
      sum_congr rfl fun i hi => by rw [hxall i hi]
    rw [hsplit, hsum] at hx
    linear_combination hx

/-- **Successor combinatorics.**  If every point of `P` outside a finite `E` has a successor
`Q^i p ∈ P` with `1 ≤ i ≤ r`, and `P` lies in the annulus `ρ ≤ |x| < 1`, `0 < |Q| < 1`, then `P`
is finite. -/
theorem finite_of_successor {P E : Set ℂ} {Q : ℂ} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hPρ : ∀ p ∈ P, ρ ≤ ‖p‖) (hP1 : ∀ p ∈ P, ‖p‖ < 1) (hE : E.Finite) (r : ℕ)
    (hsucc : ∀ p ∈ P, p ∉ E → ∃ i, 1 ≤ i ∧ i ≤ r ∧ Q ^ i * p ∈ P) : P.Finite := by
  have hQn : 0 ≤ ‖Q‖ := norm_nonneg _
  have key : ∀ n : ℕ, {p | p ∈ P ∧ ‖p‖ * ‖Q‖ ^ n < ρ}.Finite := by
    intro n
    induction n with
    | zero =>
      convert Set.finite_empty
      ext p
      simp only [pow_zero, mul_one, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt]
      exact hPρ p
    | succ n ih =>
      refine (hE.union (Set.Finite.biUnion (Finset.finite_toSet (Finset.Icc 1 r))
        fun i _ => ih.preimage (f := fun x => Q ^ i * x) ?_)).subset ?_
      · intro x _ y _ hxy
        exact mul_left_cancel₀ (pow_ne_zero i hQ0) hxy
      · rintro p ⟨hpP, hpn⟩
        by_cases hpE : p ∈ E
        · exact Or.inl hpE
        · right
          obtain ⟨i, hi1, hir, hiP⟩ := hsucc p hpP hpE
          refine Set.mem_biUnion (x := i) (by simp [hi1, hir]) ⟨hiP, ?_⟩
          have hle : ‖Q‖ ^ i ≤ ‖Q‖ := pow_le_of_le_one hQn hQ1.le (by omega)
          calc ‖Q ^ i * p‖ * ‖Q‖ ^ n = ‖Q‖ ^ i * (‖p‖ * ‖Q‖ ^ n) := by
                rw [norm_mul, norm_pow]; ring
            _ ≤ ‖Q‖ * (‖p‖ * ‖Q‖ ^ n) :=
                mul_le_mul_of_nonneg_right hle (by positivity)
            _ = ‖p‖ * ‖Q‖ ^ (n + 1) := by ring
            _ < ρ := hpn
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hρ hQ1
  refine (key N).subset fun p hp => ⟨hp, ?_⟩
  calc ‖p‖ * ‖Q‖ ^ N ≤ 1 * ‖Q‖ ^ N :=
        mul_le_mul_of_nonneg_right (hP1 p hp).le (by positivity)
    _ = ‖Q‖ ^ N := one_mul _
    _ < ρ := hN

open Metric in
/-- **prop:noqdiff (i), contracting case `0 < |Q| < 1`, abstract form.**  Let `f` be meromorphic
on the open unit disc, analytic at `0`, with infinitely many poles in the disc.  Let `a_0,…,a_r`,
`b` be holomorphic on `|x| < R`, `R > 1`, with `a_0 ≢ 0`.  Then
`∑_{i ≤ r} a_i(x) f(Q^i x) = b(x)` fails on every punctured neighbourhood of every point of the
disc. -/
theorem no_qdiff_contracting {R : ℝ} (hR : 1 < R) {Q : ℂ} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1)
    (hf : MeromorphicOn f (ball 0 1)) (hf0 : AnalyticAt ℂ f 0)
    (hpoles : {p | p ∈ ball (0 : ℂ) 1 ∧ IsPole f p}.Infinite)
    (r : ℕ) (a : ℕ → ℂ → ℂ) (ha : ∀ i ≤ r, AnalyticOnNhd ℂ (a i) (ball 0 R))
    (hne : ∃ w ∈ ball (0 : ℂ) R, a 0 w ≠ 0)
    {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b (ball 0 R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hq : ∀ᶠ x in 𝓝[≠] z₀, qOp r Q a f x = b x) :
    False := by
  set D : Set ℂ := ball 0 1 with hD
  have hsub : D ⊆ ball 0 R := ball_subset_ball hR.le
  have hQi : ∀ (i : ℕ) (x : ℂ), x ∈ D → Q ^ i * x ∈ D := by
    intro i x hx
    rw [hD, mem_ball_zero_iff] at hx ⊢
    rw [norm_mul, norm_pow]
    calc ‖Q‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hQ1.le) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hx
  -- the equation holds near every point of `D`
  have hprop : ∀ p ∈ D, ∀ᶠ x in 𝓝[≠] p, qOp r Q a f x = b x := by
    set F : ℂ → ℂ := fun x => qOp r Q a f x - b x with hF
    have hFm : MeromorphicOn F D := by
      intro z hz
      refine MeromorphicAt.sub (MeromorphicAt.fun_sum fun i hi => ?_) (hb z (hsub hz)).meromorphicAt
      have hir : i ≤ r := by rw [mem_range] at hi; omega
      have hcomp : MeromorphicAt (f ∘ fun x => Q ^ i * x) z :=
        (hf _ (hQi i z hz)).comp_analyticAt (analyticAt_const.mul analyticAt_id)
      exact (ha i hir z (hsub hz)).meromorphicAt.mul hcomp
    have h0 : meromorphicOrderAt F z₀ = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (hq.mono fun z hz => by simp [hF, hz])
    intro p hp
    have hp' : meromorphicOrderAt F p = ⊤ := by
      by_contra hne
      exact hFm.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball 0 1).isPreconnected
        hp hz₀ hne h0
    exact (meromorphicOrderAt_eq_top_iff.mp hp').mono fun z hz => sub_eq_zero.mp hz
  set P : Set ℂ := {p | p ∈ D ∧ IsPole f p} with hP
  set E : Set ℂ := {p | p ∈ P ∧ a 0 p = 0} with hE
  -- `E` is finite: isolated zeros of `a_0` on the compact closed disc
  have hEfin : E.Finite := by
    by_contra hinf
    obtain ⟨w, hwR, hw⟩ := hne
    exact hw (eqOn_zero_of_infinite_zeros (ha 0 (by omega)) (convex_ball 0 R).isPreconnected
      (isCompact_closedBall 0 1) (closedBall_subset_ball hR)
      (fun p hp => ball_subset_closedBall hp.1.1) hinf (fun p hp => hp.2) hwR)
  -- no poles near `0`
  obtain ⟨ρ, hρ, hρball⟩ : ∃ ρ > 0, ∀ z ∈ ball (0 : ℂ) ρ, AnalyticAt ℂ f z :=
    Metric.eventually_nhds_iff_ball.mp hf0.eventually_analyticAt
  have hPρ : ∀ p ∈ P, ρ ≤ ‖p‖ := by
    intro p hp
    by_contra hlt
    push Not at hlt
    have := (hρball p (mem_ball_zero_iff.mpr hlt)).meromorphicOrderAt_nonneg
    exact absurd hp.2 (not_lt.mpr this)
  -- successors
  have hsucc : ∀ p ∈ P, p ∉ E → ∃ i, 1 ≤ i ∧ i ≤ r ∧ Q ^ i * p ∈ P := by
    intro p hp hpE
    have ha0 : a 0 p ≠ 0 := fun h => hpE ⟨hp, h⟩
    by_contra hno
    push Not at hno
    have hT : ∀ i ∈ range r, Tame f (Q ^ (i + 1) * p) := by
      intro i hi
      have hir : i < r := by rwa [mem_range] at hi
      have hmem := hQi (i + 1) p hp.1
      refine tame_of_not_isPole (hf _ hmem) fun hpole => ?_
      exact hno (i + 1) (by omega) (by omega) ⟨hmem, hpole⟩
    exact not_isPole_of_tame (tame_of_qdiff hQ0 (fun i hi => ha i hi p (hsub hp.1))
      (hb p (hsub hp.1)) ha0 hT (hprop p hp.1)) hp.2
  exact hpoles (finite_of_successor hQ0 hQ1 hρ hPρ (fun p hp => mem_ball_zero_iff.mp hp.1)
    hEfin r hsucc)

end NonDFinite

#print axioms NonDFinite.reduce_local
#print axioms NonDFinite.lead_zero_at_pole_inhom
#print axioms NonDFinite.nonDfinite_inhom
#print axioms NonDFinite.nonDfinite_disc
#print axioms NonDFinite.not_DFinite_poly
#print axioms NonDFinite.ode_propagates
#print axioms NonDFinite.lead_zero_at_pole
#print axioms NonDFinite.eqOn_zero_of_infinite_zeros
#print axioms NonDFinite.nonDfinite_hom
#print axioms NonDFinite.nonDfinite_abstract
#print axioms NonDFinite.tame_of_qdiff
#print axioms NonDFinite.finite_of_successor
#print axioms NonDFinite.no_qdiff_contracting
