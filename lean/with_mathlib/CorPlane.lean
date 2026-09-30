/-
CorPlane.lean
=============
`cor:plane` of `paper/journal/merged_novel_paper.tex`: `W_2` does not embed in `Isom(R^2)`.

`W_2 = (Z/2 x Z/2) * Z/2` is the Coxeter group on generators `a, b, c` with relations
`a^2 = b^2 = c^2 = (ab)^2 = 1` (a free product of the Klein four-group `<a,b>` and `<c>`).

Proof route here (differs from the paper's "contains F_2 + amenable", but proves the same
statement): `W_2` surjects onto `S_5`, so it is not solvable; `Isom(C)` is solvable
(translations abelian, linear part in `O(2)`, whose rotations are abelian of index 2).
Hence no injective homomorphism `W_2 -> Isom(C)` exists.

SCOPE: the plane is modelled as `C` with its Euclidean metric.  Isometries are
`C ≃ᵃⁱ[R] C`; for `C ≃ᵢ C` see `no_embedding_isometryEquiv` (Mazur--Ulam).
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Complex.Determinant

namespace CorPlane

open Equiv

/-- Relations of `W_2`. -/
def rels : Set (FreeGroup (Fin 3)) :=
  {FreeGroup.of 0 ^ 2, FreeGroup.of 1 ^ 2, FreeGroup.of 2 ^ 2,
   (FreeGroup.of 0 * FreeGroup.of 1) ^ 2}

/-- `W_2 = (Z/2)^2 * Z/2` as a Coxeter presentation. -/
abbrev W2 : Type := PresentedGroup rels

/-- Generator images in `S_5`. -/
def gen : Fin 3 → Perm (Fin 5) :=
  ![swap 0 1, swap 2 3, swap 1 2 * swap 3 4]

theorem gen_rels : ∀ r ∈ rels, FreeGroup.lift gen r = 1 := by
  intro r hr
  simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [gen] <;> decide

/-- The homomorphism `W_2 -> S_5`. -/
def toS5 : W2 →* Perm (Fin 5) := PresentedGroup.toGroup gen_rels

theorem toS5_surjective : Function.Surjective toS5 := by
  have hA : swap (0 : Fin 5) 1 ∈ toS5.range := ⟨PresentedGroup.of 0, by simp [toS5, gen]⟩
  have hB : swap (2 : Fin 5) 3 ∈ toS5.range := ⟨PresentedGroup.of 1, by simp [toS5, gen]⟩
  have hC : swap (1 : Fin 5) 2 * swap 3 4 ∈ toS5.range :=
    ⟨PresentedGroup.of 2, by simp [toS5, gen]⟩
  have hD : swap (0 : Fin 5) 2 ∈ toS5.range := by
    have e : swap (0 : Fin 5) 2 =
        (swap 1 2 * swap 3 4) * swap 0 1 * (swap 1 2 * swap 3 4) := by decide
    rw [e]; exact mul_mem (mul_mem hC hA) hC
  have hE : swap (0 : Fin 5) 3 ∈ toS5.range := by
    have e : swap (0 : Fin 5) 3 = swap 2 3 * swap 0 2 * swap 2 3 := by decide
    rw [e]; exact mul_mem (mul_mem hB hD) hB
  have hF : swap (0 : Fin 5) 4 ∈ toS5.range := by
    have e : swap (0 : Fin 5) 4 =
        (swap 1 2 * swap 3 4) * swap 0 3 * (swap 1 2 * swap 3 4) := by decide
    rw [e]; exact mul_mem (mul_mem hC hE) hC
  have h12 : swap (1 : Fin 5) 2 ∈ toS5.range := by
    have e : swap (1 : Fin 5) 2 = swap 0 1 * swap 0 2 * swap 0 1 := by decide
    rw [e]; exact mul_mem (mul_mem hA hD) hA
  have h34 : swap (3 : Fin 5) 4 ∈ toS5.range := by
    have e : swap (3 : Fin 5) 4 = swap 0 3 * swap 0 4 * swap 0 3 := by decide
    rw [e]; exact mul_mem (mul_mem hE hF) hE
  have htop : (⊤ : Submonoid (Perm (Fin 5))) ≤ toS5.range.toSubmonoid := by
    rw [← Perm.mclosure_swap_castSucc_succ 4, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hA
    · exact h12
    · exact hB
    · exact h34
  intro x
  exact htop (Submonoid.mem_top x)

theorem W2_not_solvable : ¬ IsSolvable W2 := by
  intro h
  exact Perm.fin_5_not_solvable (solvable_of_surjective toS5_surjective)

/-! ## `Isom(C)` is solvable -/

open Complex

/-- Determinant of an orthogonal map of the plane, as a hom to `R^x`. -/
noncomputable def detHom : (ℂ ≃ₗᵢ[ℝ] ℂ) →* ℝˣ where
  toFun f := LinearEquiv.det f.toLinearEquiv
  map_one' := by
    have : (1 : ℂ ≃ₗᵢ[ℝ] ℂ).toLinearEquiv = 1 := rfl
    rw [this]; exact map_one _
  map_mul' f g := by
    have : (f * g).toLinearEquiv = f.toLinearEquiv * g.toLinearEquiv := rfl
    rw [this]; exact map_mul _ _ _

theorem detHom_rotation (a : Circle) : detHom (rotation a) = 1 :=
  linearEquiv_det_rotation a

theorem detHom_conj : detHom conjLIE = -1 := by
  have : conjLIE.toLinearEquiv = conjAe.toLinearEquiv := rfl
  exact (show LinearEquiv.det conjLIE.toLinearEquiv = -1 by rw [this]; exact linearEquiv_det_conjAe)

/-- `O(2)` (linear isometries of `C`) is solvable. -/
theorem solvable_O2 : IsSolvable (ℂ ≃ₗᵢ[ℝ] ℂ) := by
  refine solvable_of_ker_le_range (rotation : Circle →* (ℂ ≃ₗᵢ[ℝ] ℂ)) detHom ?_
  intro f hf
  rw [MonoidHom.mem_ker] at hf
  obtain ⟨a, h | h⟩ := linear_isometry_complex f
  · exact ⟨a, h.symm⟩
  · exfalso
    have hf' : f = rotation a * conjLIE := by rw [h]; rfl
    rw [hf', map_mul, detHom_rotation, detHom_conj] at hf
    have : ((1 * -1 : ℝˣ) : ℝ) = 1 := by rw [hf]; rfl
    norm_num at this

/-- The plane isometry group (affine isometric equivalences of `C`). -/
abbrev Isom : Type := ℂ ≃ᵃⁱ[ℝ] ℂ

theorem lin_apply (f : Isom) (x : ℂ) : f.linearIsometryEquiv x = f x - f 0 := by
  have := f.map_vadd (0 : ℂ) x
  simp only [vadd_eq_add, add_zero] at this
  rw [this]; ring

/-- Linear part. -/
noncomputable def linPart : Isom →* (ℂ ≃ₗᵢ[ℝ] ℂ) where
  toFun f := f.linearIsometryEquiv
  map_one' := by ext x; rw [lin_apply]; simp
  map_mul' f g := by
    ext x
    show (f * g).linearIsometryEquiv x = f.linearIsometryEquiv (g.linearIsometryEquiv x)
    have hz : (f * g) x = f (g x) := rfl
    have hz0 : (f * g) 0 = f (g 0) := rfl
    rw [lin_apply (f * g) x, lin_apply g x, hz, hz0, map_sub, lin_apply f (g x),
      lin_apply f (g 0)]
    ring

/-- Translations. -/
noncomputable def transHom : Multiplicative ℂ →* Isom where
  toFun v := AffineIsometryEquiv.constVAdd ℝ ℂ v.toAdd
  map_one' := by ext; simp
  map_mul' u v := by ext; simp; ring

theorem solvable_Isom : IsSolvable Isom := by
  haveI := solvable_O2
  refine solvable_of_ker_le_range transHom linPart ?_
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

/-- **`cor:plane`.** `W_2` does not embed in `Isom(C)`: no injective homomorphism. -/
theorem no_embedding : ¬ ∃ φ : W2 →* Isom, Function.Injective φ := by
  rintro ⟨φ, hφ⟩
  haveI := solvable_Isom
  exact W2_not_solvable (solvable_of_solvable_injective hφ)

/-- The same for `C ≃ᵢ C` (Mazur--Ulam: every surjective isometry is affine). -/
noncomputable def toIsom : (ℂ ≃ᵢ ℂ) →* Isom where
  toFun f := f.toRealAffineIsometryEquiv
  map_one' := by ext x; simp
  map_mul' f g := by ext x; simp

theorem toIsom_injective : Function.Injective toIsom := by
  intro f g h
  ext x
  have := congrArg (fun e : Isom => e x) h
  simpa [toIsom] using this

theorem no_embedding_isometryEquiv :
    ¬ ∃ φ : W2 →* (ℂ ≃ᵢ ℂ), Function.Injective φ := by
  rintro ⟨φ, hφ⟩
  exact no_embedding ⟨toIsom.comp φ, toIsom_injective.comp hφ⟩



#print axioms CorPlane.W2_not_solvable
#print axioms CorPlane.solvable_Isom
#print axioms CorPlane.no_embedding
#print axioms CorPlane.no_embedding_isometryEquiv
