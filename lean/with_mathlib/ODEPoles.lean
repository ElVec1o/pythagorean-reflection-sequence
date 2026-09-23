import Mathlib

/-!
# ODEPoles — meromorphic solutions of a regular linear ODE have no pole (Room A, lem:odeposes)

Let `a_0, …, a_r` be analytic at `p ∈ ℂ` with `a_r(p) ≠ 0`, and let `f` be meromorphic at `p`
with `∑_{i ≤ r} a_i(z) f^{(i)}(z) = 0` on a punctured neighbourhood of `p`.  Then `f` has no pole
at `p`: `meromorphicOrderAt f p ≥ 0` (`meromorphicOrderAt_nonneg_of_ode`); equivalently `f`
agrees near `p` (off `p`) with a function analytic at `p` (`removable_of_ode`), and `f` has a
finite limit at `p` (`tendsto_of_ode`).

The proof is the elementary indicial argument, not the Cauchy existence theorem (which is not in
Mathlib for holomorphic ODEs).  If `f = (z-p)^{-m} g` with `m ≥ 1`, `g(p) ≠ 0`, then
`f^{(j)} = (z-p)^{-(m+j)} G_j` with `G_j` analytic and `G_j(p) = (-m)(-m-1)⋯(-m-j+1) g(p) ≠ 0`
(`iteratedDeriv_eq`, `Gs_at`).  Multiplying the equation by `(z-p)^{m+r}` gives
`∑ a_i (z-p)^{r-i} G_i = 0` off `p`; the left side is continuous at `p`, so `a_r(p) G_r(p) = 0`,
a contradiction.  `iteratedDeriv` is Mathlib's global iterated derivative; only its values
off `p` enter, where it is computed from local equality.
-/

open Filter Topology Finset

namespace ODEPoles

variable {f g : ℂ → ℂ} {p : ℂ}

/-- The numerators of the successive derivatives of `(z-p)^{-m} g(z)`. -/
noncomputable def Gs (p : ℂ) (m : ℕ) (g : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | j + 1 => fun z => -((m + j : ℕ) : ℂ) * Gs p m g j z + (z - p) * deriv (Gs p m g j) z

lemma Gs_analyticAt (m : ℕ) (hg : AnalyticAt ℂ g p) : ∀ j, AnalyticAt ℂ (Gs p m g j) p
  | 0 => hg
  | j + 1 => by
    have ih := Gs_analyticAt m hg j
    have hlin : AnalyticAt ℂ (fun z : ℂ => z - p) p := analyticAt_id.sub analyticAt_const
    exact (analyticAt_const.mul ih).add (hlin.mul ih.deriv)

lemma Gs_at (m : ℕ) : ∀ j, Gs p m g j p = (∏ i ∈ range j, -((m + i : ℕ) : ℂ)) * g p
  | 0 => by simp [Gs]
  | j + 1 => by
    simp only [Gs, sub_self, zero_mul, add_zero, Gs_at m j, prod_range_succ]
    ring

lemma Gs_ne_zero {m : ℕ} (hm : 1 ≤ m) (hg0 : g p ≠ 0) (j : ℕ) : Gs p m g j p ≠ 0 := by
  rw [Gs_at]
  refine mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => ?_) hg0
  rw [neg_ne_zero, Nat.cast_ne_zero]; omega

/-- One differentiation step off `p`. -/
lemma deriv_step {G : ℂ → ℂ} {y : ℂ} (hy : y ≠ p) (hG : DifferentiableAt ℂ G y) (e : ℤ) :
    deriv (fun z => (z - p) ^ e * G z) y
      = (y - p) ^ (e - 1) * ((e : ℂ) * G y + (y - p) * deriv G y) := by
  have hw : y - p ≠ 0 := sub_ne_zero.mpr hy
  have h0 : HasDerivAt (fun x : ℂ => x ^ e) ((e : ℂ) * (y - p) ^ (e - 1)) (y - p) :=
    hasDerivAt_zpow e (y - p) (Or.inl hw)
  have hl : HasDerivAt (fun z : ℂ => z - p) 1 y := (hasDerivAt_id y).sub_const p
  have h1 := HasDerivAt.comp (h₂ := fun x : ℂ => x ^ e) y h0 hl
  have h2 : HasDerivAt (fun z => (z - p) ^ e * G z)
      ((e : ℂ) * (y - p) ^ (e - 1) * 1 * G y + (y - p) ^ e * deriv G y) y :=
    h1.mul hG.hasDerivAt
  rw [h2.deriv, zpow_sub_one₀ hw]
  field_simp

/-- `f^{(j)} = (z-p)^{-(m+j)} G_j` on a punctured neighbourhood of `p`. -/
lemma iteratedDeriv_eq (m : ℕ) (hg : AnalyticAt ℂ g p)
    (hf : f =ᶠ[𝓝[≠] p] fun z => (z - p) ^ (-(m : ℤ)) * g z) :
    ∀ j, iteratedDeriv j f =ᶠ[𝓝[≠] p] fun z => (z - p) ^ (-((m + j : ℕ) : ℤ)) * Gs p m g j z
  | 0 => by simpa [iteratedDeriv_zero, Gs] using hf
  | j + 1 => by
    have ih := iteratedDeriv_eq m hg hf j
    have h1 : ∀ᶠ y in 𝓝[≠] p, iteratedDeriv j f =ᶠ[𝓝 y]
        fun z => (z - p) ^ (-((m + j : ℕ) : ℤ)) * Gs p m g j z := by
      have := eventually_eventually_nhdsWithin.mpr ih
      filter_upwards [this, self_mem_nhdsWithin] with y hy hyp
      rwa [isOpen_compl_singleton.nhdsWithin_eq hyp] at hy
    have h2 : ∀ᶠ y in 𝓝[≠] p, AnalyticAt ℂ (Gs p m g j) y :=
      nhdsWithin_le_nhds (Gs_analyticAt m hg j).eventually_analyticAt
    filter_upwards [h1, h2, self_mem_nhdsWithin] with y hy hyA hyp
    rw [iteratedDeriv_succ, hy.deriv_eq, deriv_step hyp hyA.differentiableAt]
    simp only [Gs]
    congr 1
    · congr 1; push_cast; ring
    · push_cast; ring

/-- **Core.** A function with a genuine pole `(z-p)^{-m} g`, `m ≥ 1`, `g(p) ≠ 0`, cannot solve a
linear ODE whose leading coefficient is non-zero at `p`. -/
theorem no_pole_of_factor (r m : ℕ) (hm : 1 ≤ m) (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (har : a r p ≠ 0)
    (hg : AnalyticAt ℂ g p) (hg0 : g p ≠ 0)
    (hf : f =ᶠ[𝓝[≠] p] fun z => (z - p) ^ (-(m : ℤ)) * g z)
    (hode : ∀ᶠ z in 𝓝[≠] p, ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z = 0) : False := by
  set Φ : ℂ → ℂ := fun z => ∑ i ∈ range (r + 1), a i z * (z - p) ^ (r - i) * Gs p m g i z
    with hΦ
  have hΦ0 : ∀ᶠ z in 𝓝[≠] p, Φ z = 0 := by
    have hall : ∀ᶠ z in 𝓝[≠] p, ∀ i ∈ range (r + 1),
        iteratedDeriv i f z = (z - p) ^ (-((m + i : ℕ) : ℤ)) * Gs p m g i z := by
      rw [eventually_all_finset]; intro i _; exact iteratedDeriv_eq m hg hf i
    filter_upwards [hode, hall, self_mem_nhdsWithin] with z hz hall hzp
    have hw : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have key : Φ z = (z - p) ^ (m + r) * ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z := by
      rw [hΦ, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [hall i hi]
      have hir : i ≤ r := by rw [mem_range] at hi; omega
      have hpow : (z - p) ^ (m + r) * (z - p) ^ (-((m + i : ℕ) : ℤ)) = (z - p) ^ (r - i) := by
        rw [← zpow_natCast, ← zpow_add₀ hw, ← zpow_natCast]
        congr 1; push_cast [Nat.cast_sub hir]; ring
      rw [show (z - p) ^ (m + r) * (a i z * ((z - p) ^ (-((m + i : ℕ) : ℤ)) * Gs p m g i z))
          = a i z * ((z - p) ^ (m + r) * (z - p) ^ (-((m + i : ℕ) : ℤ))) * Gs p m g i z by ring,
        hpow]
    rw [key, hz, mul_zero]
  have hlim : Tendsto Φ (𝓝[≠] p) (𝓝 (Φ p)) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hir : i ≤ r := by rw [mem_range] at hi; omega
    have hc : ContinuousAt (fun z => a i z * (z - p) ^ (r - i) * Gs p m g i z) p :=
      ((ha i hir).continuousAt.mul ((continuousAt_id.sub continuousAt_const).pow _)).mul
        (Gs_analyticAt m hg i).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hΦp : Φ p = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hΦ0.mono fun z hz => hz.symm))
  have hΦval : Φ p = a r p * Gs p m g r p := by
    rw [hΦ]
    simp only
    rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    rw [sum_eq_zero fun i hi => by
      rw [mem_range] at hi
      rw [sub_self, zero_pow (by omega), mul_zero, zero_mul]]
    rw [zero_add]
  exact mul_ne_zero har (Gs_ne_zero hm hg0 r) (hΦval ▸ hΦp)

/-- **lem:odeposes.** A meromorphic solution of a linear ODE whose leading coefficient does not
vanish at `p` has no pole at `p`. -/
theorem meromorphicOrderAt_nonneg_of_ode (hf : MeromorphicAt f p) (r : ℕ) (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (har : a r p ≠ 0)
    (hode : ∀ᶠ z in 𝓝[≠] p, ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z = 0) :
    0 ≤ meromorphicOrderAt f p := by
  by_contra hneg
  push Not at hneg
  have hne : meromorphicOrderAt f p ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hn0 : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
  refine no_pole_of_factor (f := f) (g := g) r (-n).toNat (by omega) a ha har hg hg0 ?_ hode
  filter_upwards [hfg] with z hz
  rw [hz, smul_eq_mul]
  congr 2
  omega

/-- The singularity is removable: off `p`, `f` agrees near `p` with a function analytic at `p`. -/
theorem removable_of_ode (hf : MeromorphicAt f p) (r : ℕ) (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (har : a r p ≠ 0)
    (hode : ∀ᶠ z in 𝓝[≠] p, ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G p ∧ f =ᶠ[𝓝[≠] p] G := by
  have h0 := meromorphicOrderAt_nonneg_of_ode hf r a ha har hode
  by_cases htop : meromorphicOrderAt f p = ⊤
  · exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp htop⟩
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨g, hg, _, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    have hn0 : 0 ≤ n := by rw [← hn] at h0; exact_mod_cast h0
    refine ⟨fun z => (z - p) ^ n.toNat * g z,
      ((analyticAt_id.sub analyticAt_const).pow _).mul hg, ?_⟩
    filter_upwards [hfg] with z hz
    rw [hz, smul_eq_mul, ← zpow_natCast, Int.toNat_of_nonneg hn0]

/-- `f` has a finite limit at `p`. -/
theorem tendsto_of_ode (hf : MeromorphicAt f p) (r : ℕ) (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ≤ r, AnalyticAt ℂ (a i) p) (har : a r p ≠ 0)
    (hode : ∀ᶠ z in 𝓝[≠] p, ∑ i ∈ range (r + 1), a i z * iteratedDeriv i f z = 0) :
    ∃ c, Tendsto f (𝓝[≠] p) (𝓝 c) :=
  tendsto_nhds_of_meromorphicOrderAt_nonneg hf (meromorphicOrderAt_nonneg_of_ode hf r a ha har hode)

end ODEPoles
