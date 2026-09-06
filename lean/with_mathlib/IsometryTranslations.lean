/-
  IsometryTranslations.lean
  =========================
  Discharging the geometric hypothesis of `TransTrick` and `PointGroupReduction`.

  Both files formalize their paper proposition against an abstract hypothesis

      hab : ∀ x y : H, π x = 1 → π y = 1 → x * y = y * x

  which reads, at the intended instance, "two isometries with trivial linear part -- i.e.
  two translations of `R^n` -- commute".  That was left as a hypothesis so the group
  theory could be stated without developing Euclidean isometries.

  Here it is PROVED, for the honest object: `AffineIsometryEquiv` on a normed add-torsor,
  which is Mathlib's group of affine isometries and carries `instGroup`.  The linear part
  is `AffineIsometryEquiv.linearIsometryEquiv`, and the bridge is `map_vadd`:

      e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p.

  The argument is the paper's, with no extra input: an isometry whose linear part is the
  identity has a CONSTANT translation vector (`vsub_const_of_linear_trivial`, obtained by
  feeding `v = q -ᵥ p` to `map_vadd`), and two constant translations commute because the
  vector space is abelian.

  Trivial linear part is spelled pointwise (`∀ v, e.linearIsometryEquiv v = v`) rather
  than as `= 1`, so no group structure on the linear-isometry side is needed.

  No `sorry`.
-/

import Mathlib.Analysis.Normed.Affine.Isometry
import TransTrick

namespace IsometryTranslations

variable {𝕜 V P : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **An isometry with trivial linear part translates by a constant vector.**  Feed
`v = q -ᵥ p` to `map_vadd`: it sends `q` to `(q -ᵥ p) +ᵥ e p`, so `e q -ᵥ q = e p -ᵥ p`. -/
theorem vsub_const_of_linear_trivial (e : P ≃ᵃⁱ[𝕜] P)
    (he : ∀ v : V, e.linearIsometryEquiv v = v) (p q : P) :
    e q -ᵥ q = e p -ᵥ p := by
  have hq : e q = (q -ᵥ p) +ᵥ e p := by
    have h := e.map_vadd p (q -ᵥ p)
    rw [he (q -ᵥ p)] at h
    simpa using h
  rw [hq, vadd_vsub_assoc, add_comm]
  exact vsub_add_vsub_cancel _ _ _

/-- **An isometry with trivial linear part acts as its translation vector everywhere.** -/
theorem apply_eq_vadd_of_linear_trivial (e : P ≃ᵃⁱ[𝕜] P)
    (he : ∀ v : V, e.linearIsometryEquiv v = v) (p q : P) :
    e q = (e p -ᵥ p) +ᵥ q := by
  have h := vsub_const_of_linear_trivial e he p q
  rw [← h]
  simp

/-- **Two translations commute.**  This is `hab` of `TransTrick`/`PointGroupReduction`,
proved rather than assumed. -/
theorem commute_of_linear_trivial (e f : P ≃ᵃⁱ[𝕜] P)
    (he : ∀ v : V, e.linearIsometryEquiv v = v)
    (hf : ∀ v : V, f.linearIsometryEquiv v = v) :
    e * f = f * e := by
  ext q
  have hmul : ∀ a b : P ≃ᵃⁱ[𝕜] P, (a * b) q = a (b q) := fun a b => rfl
  rw [hmul, hmul]
  -- push each outer map through, using that its translation vector is constant
  rw [apply_eq_vadd_of_linear_trivial e he q (f q),
      apply_eq_vadd_of_linear_trivial f hf q (e q)]
  -- both sides are the two translation vectors applied to `q`, in opposite orders
  have hL : (e q -ᵥ q) +ᵥ f q = ((e q -ᵥ q) + (f q -ᵥ q)) +ᵥ q := by
    rw [← vadd_vadd, vsub_vadd]
  have hR : (f q -ᵥ q) +ᵥ e q = ((f q -ᵥ q) + (e q -ᵥ q)) +ᵥ q := by
    rw [← vadd_vadd, vsub_vadd]
  rw [hL, hR, add_comm]

/-- **The translation trick, unconditionally, for real Euclidean isometries.**  This is
`prop:transtrick` with its geometric hypothesis discharged: for any homomorphism `ρ` into
the affine isometry group, if `ρ u` has trivial linear part then the commutator
`[u, g u g⁻¹]` is killed by `ρ`, for every `g`.

`π` is still taken as an abstract homomorphism detecting triviality of the linear part;
what is no longer assumed is that its kernel is abelian -- that is now
`commute_of_linear_trivial`. -/
theorem transtrick_isometry {G K : Type*} [Group G] [Group K]
    (ρ : G →* (P ≃ᵃⁱ[𝕜] P)) (π : (P ≃ᵃⁱ[𝕜] P) →* K)
    (hπ : ∀ x : P ≃ᵃⁱ[𝕜] P, π x = 1 → ∀ v : V, x.linearIsometryEquiv v = v)
    (u g : G) (hu : π (ρ u) = 1) :
    ρ (u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹) = 1 :=
  TransTrick.transtrick ρ π
    (fun x y hx hy => commute_of_linear_trivial x y (hπ x hx) (hπ y hy)) u g hu

end IsometryTranslations

#print axioms IsometryTranslations.vsub_const_of_linear_trivial
#print axioms IsometryTranslations.apply_eq_vadd_of_linear_trivial
#print axioms IsometryTranslations.commute_of_linear_trivial
#print axioms IsometryTranslations.transtrick_isometry
