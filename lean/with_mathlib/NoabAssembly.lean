/-
NoabAssembly.lean
=================
Hypothesis-relative assembly of everything in `merged_novel_paper.tex` that hangs off
`lem:noab` ("`W_n` has no nontrivial normal abelian subgroup").

`lem:noab` itself is NOT proved here.  The paper proves it from Caprace--Fujiwara
(rank-one isometry => acylindrical hyperbolicity) and Osin (amenable radical = finite radical),
neither of which is in Mathlib.  It enters below ONLY as the explicit hypothesis
`NoNormalAbelian G`.  Nothing in this file raises the logical status of `lem:noab`.

Proved relative to `NoNormalAbelian G` (G an arbitrary group, so this covers every `W_n`):

  * `injective_of_ker_comm`     -- the engine: commutative kernel => injective.
  * `reduce_injective`          -- `prop:reduce` core and `cor:necessary` (same argument): if
                                   `phi : G -> H` is injective and `L : H -> K` has commutative
                                   kernel, `L o phi` is injective.
  * `embeds_isom_iff_embeds_O2` -- `prop:reduce` concretely for the plane: `G` embeds in
                                   `Isom(C)` iff it embeds in `O(2)`.
  * `quotient_faithful`         -- the linear-algebra core of `lem:quotfaith` / `thm:dimdrop`:
                                   a faithful linear action fixing a vector `z` stays faithful
                                   on `V / <z>`.

NOT assembled here (need more than `lem:noab`): `thm:alln`, `thm:dimdrop`'s Vinberg input,
`thm:unify` (algebraic-subset genericity), `lem:perron` / `lem:Kplus` (Perron--Frobenius).
-/
import Mathlib.Tactic
import CorPlane

namespace NoabAssembly

open CorPlane

/-- The hypothesis `lem:noab`, abstracted to any group. -/
def NoNormalAbelian (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → N = ⊥

/-- Engine: under `lem:noab`, a homomorphism with commutative kernel is injective. -/
theorem injective_of_ker_comm {G K : Type*} [Group G] [Group K] (h : NoNormalAbelian G)
    (ψ : G →* K) (hc : ∀ x ∈ ψ.ker, ∀ y ∈ ψ.ker, x * y = y * x) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact h _ inferInstance hc

/-- `prop:reduce` / `cor:necessary` core. -/
theorem reduce_injective {G H K : Type*} [Group G] [Group H] [Group K]
    (h : NoNormalAbelian G) (φ : G →* H) (hφ : Function.Injective φ) (L : H →* K)
    (hL : ∀ x ∈ L.ker, ∀ y ∈ L.ker, x * y = y * x) : Function.Injective (L.comp φ) := by
  apply injective_of_ker_comm h
  intro x hx y hy
  apply hφ
  rw [map_mul, map_mul]
  exact hL _ (by simpa [MonoidHom.mem_ker] using hx) _ (by simpa [MonoidHom.mem_ker] using hy)

/-! ### The plane instance of `prop:reduce` -/

theorem ker_linPart_comm : ∀ x ∈ linPart.ker, ∀ y ∈ linPart.ker, x * y = y * x := by
  have key : ∀ f ∈ linPart.ker, ∃ v : Multiplicative ℂ, transHom v = f := by
    intro f hf
    rw [MonoidHom.mem_ker] at hf
    refine ⟨Multiplicative.ofAdd (f 0), ?_⟩
    ext x
    have h1 : f.linearIsometryEquiv = 1 := hf
    have h2 := lin_apply f x
    rw [h1] at h2
    have h3 : x = f x - f 0 := by simpa using h2
    simp [transHom]
    rw [add_comm]; linear_combination h3
  intro x hx y hy
  obtain ⟨u, rfl⟩ := key x hx
  obtain ⟨v, rfl⟩ := key y hy
  rw [← map_mul, ← map_mul, mul_comm]

/-- `O(2)` sits inside `Isom(C)`. -/
noncomputable def toAff : (ℂ ≃ₗᵢ[ℝ] ℂ) →* Isom where
  toFun f := f.toAffineIsometryEquiv
  map_one' := by ext x; simp
  map_mul' f g := by ext x; simp

theorem toAff_injective : Function.Injective toAff := by
  intro f g h
  ext x
  have := congrArg (fun e : Isom => e x) h
  simpa [toAff] using this

/-- `prop:reduce` for `n = 2`, relative to `lem:noab`: embeds in `Isom(C)` iff embeds in `O(2)`. -/
theorem embeds_isom_iff_embeds_O2 {G : Type*} [Group G] (h : NoNormalAbelian G) :
    (∃ φ : G →* Isom, Function.Injective φ) ↔
      (∃ ψ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ), Function.Injective ψ) := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨linPart.comp φ, reduce_injective h φ hφ linPart ker_linPart_comm⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨toAff.comp ψ, toAff_injective.comp hψ⟩

/-! ### The linear-algebra core of `lem:quotfaith` / `thm:dimdrop` -/

section Quot

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V] [Group G]

/-- Faithful linear action fixing `z` (a generator of the radical line) stays faithful on
`V / k z`: any `g` acting trivially modulo `z` is the identity.  Relative to `lem:noab`. -/
theorem quotient_faithful (hG : NoNormalAbelian G) (ρ : G →* Module.End k V)
    (hρ : Function.Injective ρ) (z : V) (hz : ∀ g, ρ g z = z)
    (g : G) (hg : ∀ v, ∃ c : k, ρ g v = v + c • z) : g = 1 := by
  have hinv : ∀ h : G, ∀ v, ρ h (ρ h⁻¹ v) = v := by
    intro h v
    have : ρ h * ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simpa using congrArg (fun f : Module.End k V => f v) this
  let N : Subgroup G :=
    { carrier := {g | ∀ v, ∃ c : k, ρ g v = v + c • z}
      one_mem' := fun v => ⟨0, by simp⟩
      mul_mem' := by
        intro a b ha hb v
        obtain ⟨cb, hcb⟩ := hb v
        obtain ⟨ca, hca⟩ := ha v
        refine ⟨ca + cb, ?_⟩
        have : ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl
        rw [this, hcb, map_add, map_smul, hz, hca]
        module
      inv_mem' := by
        intro a ha v
        obtain ⟨c, hc⟩ := ha (ρ a⁻¹ v)
        refine ⟨-c, ?_⟩
        rw [hinv] at hc
        rw [eq_sub_of_add_eq hc.symm]; module }
  have hN : N = ⊥ := by
    apply hG
    · refine ⟨fun n hn h v => ?_⟩
      obtain ⟨c, hc⟩ := hn (ρ h⁻¹ v)
      refine ⟨c, ?_⟩
      have : ρ (h * n * h⁻¹) v = ρ h (ρ n (ρ h⁻¹ v)) := by
        rw [map_mul, map_mul]; rfl
      rw [this, hc, map_add, map_smul, hz, hinv]
    · intro x hx y hy
      apply hρ
      apply LinearMap.ext
      intro v
      obtain ⟨cx, hcx⟩ := hx v
      obtain ⟨cy, hcy⟩ := hy v
      have h1 : ρ (x * y) v = ρ x (ρ y v) := by rw [map_mul]; rfl
      have h2 : ρ (y * x) v = ρ y (ρ x v) := by rw [map_mul]; rfl
      rw [h1, h2, hcy, hcx, map_add, map_add, map_smul, map_smul, hz, hz, hcx, hcy]
      module
  have : g ∈ N := hg
  rw [hN] at this
  exact Subgroup.mem_bot.mp this

end Quot

end NoabAssembly

-- Rule 5 axiom audit.
#print axioms NoabAssembly.injective_of_ker_comm
#print axioms NoabAssembly.reduce_injective
#print axioms NoabAssembly.embeds_isom_iff_embeds_O2
#print axioms NoabAssembly.quotient_faithful
