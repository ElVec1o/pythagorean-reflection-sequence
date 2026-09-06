/-
  PointGroupReduction.lean
  ========================
  `prop:reduce` of `paper/journal/merged_novel_paper.tex` (line 219, labelled PROVED):

    Let `n >= 2` and `phi : W_n -> Isom(R^n)` be injective.  Then `L . phi` is injective,
    where `L` is the linear part.  Consequently `W_n` embeds in `Isom(R^n)` iff `W_n`
    embeds in `O(n)`.

  The paper's proof: `ker (L . phi)` is normal in `W_n` and embeds in the abelian group
  `R^n` of translations, hence is abelian; by `lem:noab` (`W_n` has no nontrivial normal
  abelian subgroup) it is trivial.

  Two of those three steps are pure group theory and are proved here:
    * `ker (L . phi)` is abelian, because `phi` is injective and `ker L` is abelian
      (`ker_comp_comm`);
    * normality is automatic, `ker` of a homomorphism being normal;
  and the third, `lem:noab`, is taken as a hypothesis.  That is deliberate and is the
  honest boundary: `lem:noab`'s own proof runs through Caprace-Fujiwara (a rank-one
  isometry on the Davis complex), acylindrical hyperbolicity, and Osin's identification of
  the amenable radical with the finite radical.  None of that is in Mathlib, and none of it
  is reconstructed here.

  What IS gained: given `lem:noab` as an input, the reduction to the compact group is
  mechanical, and that mechanical step is now kernel-checked rather than prose.

  No `sorry`.
-/

import Mathlib.Tactic

namespace PointGroupReduction

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- **The kernel of `L . phi` is abelian.**  `phi` carries it injectively into `ker L`,
which is abelian (for the intended instance, `ker L` is the translation subgroup `R^n`),
so any two of its elements commute.  This is the paper's "isomorphic to a subgroup of the
abelian group `R^n`, hence abelian". -/
theorem ker_comp_comm (φ : G →* H) (L : H →* K) (hφ : Function.Injective φ)
    (hab : ∀ x y : H, L x = 1 → L y = 1 → x * y = y * x)
    {a b : G} (ha : L (φ a) = 1) (hb : L (φ b) = 1) :
    a * b = b * a := by
  apply hφ
  rw [map_mul, map_mul]
  exact hab (φ a) (φ b) ha hb

/-- **The reduction.**  If `phi` is injective, `ker L` is abelian, and `G` has no
nontrivial normal abelian subgroup, then `L . phi` is injective.

`hnoab` is `lem:noab` for `G`, supplied as a hypothesis: its proof is Coxeter-theoretic
and well outside what is formalized here. -/
theorem injective_comp_of_no_normal_abelian (φ : G →* H) (L : H →* K)
    (hφ : Function.Injective φ)
    (hab : ∀ x y : H, L x = 1 → L y = 1 → x * y = y * x)
    (hnoab : ∀ N : Subgroup G, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → N = ⊥) :
    Function.Injective (L.comp φ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply hnoab
  · exact MonoidHom.normal_ker (L.comp φ)
  · intro x hx y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx hy
    exact ker_comp_comm φ L hφ hab hx hy

/-- **The equivalence the proposition draws.**  One direction is the reduction above,
composing an embedding into `Isom(R^n)` with the linear part to land in `O(n)`; the other
is the inclusion `O(n) <= Isom(R^n)`, here any injective `iota`. -/
theorem embeds_iff (φ : G →* H) (L : H →* K)
    (hab : ∀ x y : H, L x = 1 → L y = 1 → x * y = y * x)
    (hnoab : ∀ N : Subgroup G, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → N = ⊥)
    (ι : K →* H) (hι : Function.Injective ι) :
    (∃ f : G →* H, Function.Injective f) ↔ (∃ f : G →* K, Function.Injective f) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨L.comp f, injective_comp_of_no_normal_abelian f L hf hab hnoab⟩
  · rintro ⟨f, hf⟩
    exact ⟨ι.comp f, by simpa [MonoidHom.coe_comp] using hι.comp hf⟩

end PointGroupReduction

#print axioms PointGroupReduction.ker_comp_comm
#print axioms PointGroupReduction.injective_comp_of_no_normal_abelian
#print axioms PointGroupReduction.embeds_iff
