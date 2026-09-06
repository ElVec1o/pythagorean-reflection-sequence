/-
  TransTrick.lean
  ===============
  `prop:transtrick` of `paper/journal/merged_novel_paper.tex` (line 296, labelled PROVED):

    Let `a` be a positive tuple and `u` in `W_n` satisfy `pi (rho_a u) = I`, i.e. `rho_a u`
    has trivial linear part.  Then for every `g`, the commutator `[u, g u g^-1]` lies in
    `ker rho_a`.

  The paper's proof is: an isometry with trivial linear part is a translation; a conjugate
  of a translation is a translation; two translations commute; so the commutator dies.

  Every step of that is group theory about the kernel of the linear-part homomorphism.
  Nothing about `R^n`, about `W_n`, or about the tuple `a` is used -- only that the
  translations are exactly `ker pi` and that this kernel is abelian.  So the statement is
  formalised here at that level of generality, with "two translations commute" supplied as
  the hypothesis `hab` rather than re-developing Euclidean isometry theory.  Instantiating
  `pi` at the linear part of `Isom(R^n)` and `rho` at `rho_a` recovers the paper statement
  verbatim; `hab` is then the (true, standard) fact that translations of `R^n` commute.

  Normality is NOT an extra hypothesis: the conjugate of an element of `ker pi` lies in
  `ker pi` automatically, because `ker` of a homomorphism is normal.  That is
  `conj_mem_ker` below, and it is where the paper's "a conjugate of a translation is a
  translation" is discharged.

  No `sorry`.
-/

import Mathlib.Tactic

namespace TransTrick

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- **A conjugate of a trivial-linear-part element again has trivial linear part.**  The
paper's "a conjugate of a translation by an isometry is again a translation", with no
geometry: it is just that a kernel is closed under conjugation. -/
theorem conj_mem_ker (π : H →* K) {x : H} (hx : π x = 1) (h : H) :
    π (h * x * h⁻¹) = 1 := by
  simp [map_mul, map_inv, hx]

/-- **The translation trick.**  If `ρ u` has trivial linear part, then for every `g` the
commutator `[u, g u g⁻¹]` is killed by `ρ`.

Stated with the commutator written out, so the only Mathlib notions involved are group
homomorphisms; `hab` is exactly "two elements with trivial linear part commute", i.e. the
paper's "two translations of `R^n` commute". -/
theorem transtrick (ρ : G →* H) (π : H →* K)
    (hab : ∀ x y : H, π x = 1 → π y = 1 → x * y = y * x)
    (u g : G) (hu : π (ρ u) = 1) :
    ρ (u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹) = 1 := by
  -- the two elements whose commutator is taken, pushed through `ρ`
  set A : H := ρ u with hA
  set B : H := ρ g * ρ u * (ρ g)⁻¹ with hB
  -- both have trivial linear part: `A` by hypothesis, `B` because kernels are normal
  have hAk : π A = 1 := hu
  have hBk : π B = 1 := conj_mem_ker π hu (ρ g)
  -- hence they commute
  have hcomm : A * B = B * A := hab A B hAk hBk
  -- and the commutator collapses
  have hρ : ρ (u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹) = A * B * A⁻¹ * B⁻¹ := by
    simp [hA, hB, map_mul, map_inv, mul_assoc]
  rw [hρ, hcomm]
  group

/-- **The kernel form, matching the paper's `[u, g u g⁻¹] ∈ ker ρ_a`.** -/
theorem transtrick_mem_ker (ρ : G →* H) (π : H →* K)
    (hab : ∀ x y : H, π x = 1 → π y = 1 → x * y = y * x)
    (u g : G) (hu : π (ρ u) = 1) :
    u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹ ∈ ρ.ker :=
  MonoidHom.mem_ker.mpr (transtrick ρ π hab u g hu)

/-- **Why the trick produces kernel elements at all.**  If in addition the commutator is
not itself trivial in `G`, it witnesses that `ρ` is not injective -- which is how
`thm:masterCfalse` uses it to refute Conjecture C. -/
theorem not_injective_of_transtrick (ρ : G →* H) (π : H →* K)
    (hab : ∀ x y : H, π x = 1 → π y = 1 → x * y = y * x)
    (u g : G) (hu : π (ρ u) = 1)
    (hne : u * (g * u * g⁻¹) * u⁻¹ * (g * u * g⁻¹)⁻¹ ≠ 1) :
    ¬ Function.Injective ρ := by
  intro hinj
  exact hne (hinj (by rw [transtrick ρ π hab u g hu, map_one]))

end TransTrick

#print axioms TransTrick.conj_mem_ker
#print axioms TransTrick.transtrick
#print axioms TransTrick.transtrick_mem_ker
#print axioms TransTrick.not_injective_of_transtrick
