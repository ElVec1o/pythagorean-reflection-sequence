/-
Paper1TierA.lean
=================
Formalization-debt paydown: Tier-A items from `paper/journal/paper1.tex` that
previously had zero Lean coverage (2026-09-28 triage, `private/FORMALIZATION_TRIAGE.md`).
Session target was four items; three got genuine proofs, the fourth (`lem:swap`) was
attempted and abandoned with the reason recorded below.

  * `lem:dilation-invariance` -- conjugating the side-reflection representation of a
    right triangle `T` by a central dilation `D_λ` gives the representation of `λT`;
    consequently the two representations have the same kernel. DONE.
  * `lem:glide-square-restate` -- the glide reflection `g = R_x R_y R_h` squares to the
    pure translation by `2(ζ⁻¹-1)`, and conjugating a translation by a rotation of
    coefficient `μ` scales the translation vector by `μ⁻¹`. DONE.
  * `lem:rho-abs` -- the abstract realization `ρ_abs : W → Q ⋉ M` sending the three
    generators to `(X,0), (X',0), (Y,h)` is a well-defined homomorphism, i.e. it kills
    the three defining relators of `W`. DONE.
  * `lem:swap` -- NOT DONE. See the note at the bottom of this file.

Section `Dilation` and `GlideSquare` model reflections/translations/rotations as maps
`ℂ → ℂ`, the standard affine-isometry parametrisation `z ↦ ζ * conj z + b` (reflection,
`|ζ| = 1`) and `z ↦ μ * z` (rotation/dilation), matching the paper's own symbolic-tuple
bookkeeping. Section `RhoAbs` models the semidirect product `Q ⋉ M` abstractly, for any
group `Q` and any `Q`-module `M`, matching the style of `TranslationTrick.lean` and
`IsometryTranslations.lean` (state the needed algebraic hypotheses, not a specific `Q`
or `M`).

No `sorry`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Group.Subgroup.Basic

namespace Paper1TierA

/-! ## `lem:dilation-invariance` -/

namespace Dilation

open Complex

/-- A side reflection, parametrised as `z ↦ ζ * conj z + b` with `ζ` a unit complex
number (encoding the line's direction) and `b` the translation part. This is the
symbolic-tuple form used throughout `paper1.tex` §"glide-square translation lattice". -/
noncomputable def reflect (ζ b : ℂ) (z : ℂ) : ℂ := ζ * (starRingEnd ℂ) z + b

/-- The central dilation by `λ`, about the origin (the right-angle vertex, in the
paper's normalisation). -/
def dilate (lam : ℂ) (z : ℂ) : ℂ := lam * z

/-- **`lem:dilation-invariance`, the per-generator identity**, for the paper's
hypothesis `λ > 0` (in particular `λ` real): "reflecting across a line and then
rescaling about the centre coincides with rescaling and then reflecting across the
scaled line," i.e. `ρ_{λT}(R_i) = D_λ ∘ ρ_T(R_i) ∘ D_λ⁻¹` for each generator `R_i`,
with `ρ_T(R_i)` the reflection `reflect ζ b` and `ρ_{λT}(R_i)` the reflection
`reflect ζ (λ b)` of the scaled triangle.

(A real, or more generally unimodular, dilation factor is essential here: for a
general complex `λ` the identity fails, since it needs `conj λ = λ`, which is exactly
where the geometric hypothesis "central dilation," i.e. scaling by a positive real
factor, enters.) -/
theorem dilate_conj_reflect (lam : ℝ) (ζ b : ℂ) (hlam : lam ≠ 0) (z : ℂ) :
    dilate (lam : ℂ) (reflect ζ b (dilate (lam : ℂ)⁻¹ z)) = reflect ζ ((lam : ℂ) * b) z := by
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hconjmul : (starRingEnd ℂ) ((lam : ℂ)⁻¹ * z)
      = (lam : ℂ)⁻¹ * (starRingEnd ℂ) z := by
    rw [map_mul, map_inv₀, Complex.conj_ofReal]
  unfold dilate reflect
  rw [hconjmul]
  field_simp

/-- **Consequence: equal kernels.**  If `ψ = c ⬝ φ ⬝ c⁻¹` pointwise for group
homomorphisms `φ, ψ : G →* K` and a unit `c : K`, then `φ` and `ψ` have the same
kernel — the "In particular `ker(ρ_{λT}) = ker(ρ_T)`" half of `lem:dilation-invariance`,
which needs no analytic input beyond conjugation being a group automorphism. -/
theorem ker_eq_of_conj {G K : Type*} [Group G] [Group K]
    (φ ψ : G →* K) (c : K) (hconj : ∀ g : G, ψ g = c * φ g * c⁻¹) :
    ψ.ker = φ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, hconj]
  constructor
  · intro h
    have : φ g = c⁻¹ * (c * φ g * c⁻¹) * c := by group
    rw [h] at this
    simpa using this
  · intro h
    rw [h]; group

end Dilation

/-! ## `lem:glide-square-restate` -/

namespace GlideSquare

open Complex

/-- The glide reflection `g(z) = -ζ⁻¹ conj z - (1-ζ⁻¹)`, with `ζ` a unit complex
number encoding the hypotenuse direction (`|ζ|=1`, i.e. `ζ * conj ζ = 1`). -/
noncomputable def g (zeta : ℂ) (z : ℂ) : ℂ := -zeta⁻¹ * (starRingEnd ℂ) z - (1 - zeta⁻¹)

/-- **`lem:glide-square-restate`, the glide-square computation.**
`g² (z) = z + 2(ζ⁻¹ - 1)`: the square of the glide reflection is the pure translation
by `2(ζ⁻¹-1)`, using only `ζ * conj ζ = 1`. -/
theorem g_sq (zeta z : ℂ) (hzeta : zeta * (starRingEnd ℂ) zeta = 1) :
    g zeta (g zeta z) = z + 2 * (zeta⁻¹ - 1) := by
  have hzne : zeta ≠ 0 := by
    intro h; rw [h, zero_mul] at hzeta; exact zero_ne_one hzeta
  have hconjzeta : (starRingEnd ℂ) zeta = zeta⁻¹ := by
    have h := congrArg (zeta⁻¹ * ·) hzeta
    simp only [← mul_assoc, inv_mul_cancel₀ hzne, one_mul, mul_one] at h
    exact h
  have hconjzetainv : (starRingEnd ℂ) (zeta⁻¹) = zeta := by
    rw [map_inv₀, hconjzeta, inv_inv]
  unfold g
  simp only [map_sub, map_neg, map_mul, map_one, Complex.conj_conj, hconjzeta, hconjzetainv]
  field_simp
  ring

/-- Pure translation by `v`. -/
def translate (v z : ℂ) : ℂ := z + v

/-- Rotation with linear coefficient `μ` (a unit: `|μ|=1` in the geometric setting,
though the algebra below needs only `μ ≠ 0`). -/
def rotate (mu z : ℂ) : ℂ := mu * z

/-- **`lem:glide-square-restate`, the conjugation half.**
Conjugating the translation by `v` by the rotation `r^k` -- linear coefficient `μ`
(`μ ≠ 0`), applied via `r^{-k} τ r^{k}` -- gives the translation by `μ⁻¹ v`:
"conjugating a translation with vector `v` by the rotation `r^k` (linear part
`μ = t^k`) multiplies `v` by `t^{-k}`." Applying this with `μ = ζ^k` and
`v = 2m(ζ⁻¹-1)`, and telescoping over `m`-fold products (which commute, since
translations commute, `translate_comm`/`translate_comp` below), realizes
`2m ζ^{-k}(ζ^{-1}-1)` for every `k, m`, giving the inclusion
`2(t^{-1}-1) Z[t^{±1}] ⊆ T` stated in the lemma. -/
theorem rotate_conj_translate (mu v : ℂ) (hmu : mu ≠ 0) (z : ℂ) :
    rotate mu⁻¹ (translate v (rotate mu z)) = translate (mu⁻¹ * v) z := by
  unfold rotate translate
  field_simp

/-- Translations commute (needed for the "products of these realize ..." step: a
product of several conjugated glide-squares is again a translation, by the sum of the
individual vectors, regardless of order). -/
theorem translate_comm (u v z : ℂ) :
    translate u (translate v z) = translate v (translate u z) := by
  unfold translate; ring

/-- Composite of two translations is the translation by the sum. -/
theorem translate_comp (u v z : ℂ) : translate u (translate v z) = translate (u + v) z := by
  unfold translate; ring

end GlideSquare

/-! ## `lem:rho-abs` -/

namespace RhoAbs

/-- The semidirect product `Q ⋉ M` for a group `Q` acting on an additive commutative
group `M` (the translation module) via `act : Q → M → M` (written `q • m`). Matches
the standard formula `(q₁,m₁)*(q₂,m₂) = (q₁q₂, m₁ + q₁•m₂)` used to define
`ρ_abs : W → Q ⋉ M` in the paper. Kept as a plain product type with an explicit
multiplication (not routed through Mathlib's `SemidirectProduct`) so the two defining
computations below stay a direct unfold-and-simp, mirroring the paper's own proof
("The defining relations of `W` are checked directly"). -/
structure Semidirect (Q M : Type*) where
  q : Q
  m : M

variable {Q M : Type*} [Group Q] [AddCommGroup M]

-- `act : Q → M → M` is the `Q`-action on `M`; the two properties used below are that
-- it is additive in its second argument and kills `0`. We only ever evaluate `act` at
-- the single named element `Y : Q`, so no bundled `AddMonoidHom`/`DistribMulAction`
-- structure is needed.
variable (act : Q → M → M)

/-- Multiplication on `Semidirect Q M`. -/
def smul (a b : Semidirect Q M) : Semidirect Q M := ⟨a.q * b.q, a.m + act a.q b.m⟩

/-- The image of a generator with trivial translation part. -/
def mk0 (x : Q) : Semidirect Q M := ⟨x, 0⟩

/-- The image of the third generator, carrying the Crowell generator `h`. -/
def mkH (y : Q) (h : M) : Semidirect Q M := ⟨y, h⟩

/-- **`lem:rho-abs`, the well-definedness check.**
Given a group `Q`, an additive group `M`, an action `act` of `Q` on `M` that is
additive in its second argument (`hact_add`) and kills `0` (`hact_zero`), and elements
`X, X', Y : Q` with `X² = 1`, `X'² = 1`, `Y² = 1`, `(XX')² = 1` (the images of the
four relators of `W`, with `c := XX'`), and `h : M` with `act Y h = -h` (i.e.
`(Y+1)•h = 0` in `M`), the map `ρ_abs : R₀ ↦ (X,0), R₁ ↦ (X',0), R₂ ↦ (Y,h)` satisfies
all four defining relators of `W`: `ρ_abs(R₀)² = 1`, `ρ_abs(R₁)² = 1`,
`ρ_abs(R₂)² = 1`, and `(ρ_abs(R₀) ρ_abs(R₁))² = 1`. This is exactly the paper's proof,
unfolded. -/
theorem rho_abs_well_defined
    (hact_add : ∀ (q : Q) (m₁ m₂ : M), act q (m₁ + m₂) = act q m₁ + act q m₂)
    (hact_zero : ∀ q : Q, act q (0 : M) = 0)
    (X Xp Y : Q) (h : M)
    (hX : X ^ 2 = 1) (hXp : Xp ^ 2 = 1) (hY : Y ^ 2 = 1) (hc : (X * Xp) ^ 2 = 1)
    (hh : act Y h = -h) :
    smul act (mk0 X) (mk0 X) = (⟨1, 0⟩ : Semidirect Q M) ∧
    smul act (mk0 Xp) (mk0 Xp) = (⟨1, 0⟩ : Semidirect Q M) ∧
    smul act (mkH Y h) (mkH Y h) = (⟨1, 0⟩ : Semidirect Q M) ∧
    smul act (smul act (mk0 X) (mk0 Xp)) (smul act (mk0 X) (mk0 Xp))
      = (⟨1, 0⟩ : Semidirect Q M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold smul mk0
    have : X * X = 1 := by have := hX; rwa [sq] at this
    simp [this, hact_zero]
  · unfold smul mk0
    have : Xp * Xp = 1 := by have := hXp; rwa [sq] at this
    simp [this, hact_zero]
  · unfold smul mkH
    have hY2 : Y * Y = 1 := by rwa [sq] at hY
    simp [hY2, hact_add, hh]
  · unfold smul mk0
    have : (X * Xp) * (X * Xp) = 1 := by have := hc; rwa [sq] at this
    simp [this, hact_zero]

end RhoAbs

end Paper1TierA

-- Certification (Rule 5): every axiom these results rest on.
#print axioms Paper1TierA.Dilation.dilate_conj_reflect
#print axioms Paper1TierA.Dilation.ker_eq_of_conj
#print axioms Paper1TierA.GlideSquare.g_sq
#print axioms Paper1TierA.GlideSquare.rotate_conj_translate
#print axioms Paper1TierA.GlideSquare.translate_comm
#print axioms Paper1TierA.GlideSquare.translate_comp
#print axioms Paper1TierA.RhoAbs.rho_abs_well_defined

/-
### `lem:swap` -- attempted and abandoned

The paper's proof of `lem:swap` (`paper1.tex`, around line 3209) turns on a specific
finite combinatorial fact about the *typed* pairing at a site: each end is either an
arrival or a departure, carries a "side," and the pairing cost `pc` of an
arrival/departure pair is `0` for a "bounce" (same physical side, opposite algebraic
sign across the pair) and `2` for a "sign-flip bounce." A merging 2-swap replaces the
two intra-component pairs by the two inter-component ones, and the paper's proof
argues this changes the site's total cost by exactly `+2` -- an *asymmetric* change
(one new pair costs `0`, the other `2`), not the symmetric `0`-or-`+4` change that a
single "same side / different side" `Bool` predicate on ends necessarily produces.

Concretely: model each end's side as a single `Bool` and try `pc x y := if x = y then
0 else 2` (or the complementary convention). Under either convention, imposing the
paper's stated hypotheses (`γ`'s own pair is a bounce, the open walk's own pair at the
bridged edge is a bounce, the two components differ) forces the merged pair costs to
be **equal to each other** by the symmetry of `pc`, so the total change is always `0`
or `±4`, never the claimed `+2`. (Checked directly: with `pc x y := if x = y then 0
else 2`, `a = b`, `a' = b'`, `a ≠ a'` forces `pc a b' = pc a' b`, both `2`, giving a
total of `4`, not `2`.) This is not a proof bug -- it shows a bare `Bool` "side" is not
enough information to reproduce the paper's asymmetric law; the arrival/departure
distinction has to be carried as genuinely separate data, exactly as the *existing*
`EndData.lean` / `WalkGraph.lean` / `PairingMatrix.lean` / `CostMerge.lean` machinery
does (over 1800 lines total) for the structurally analogous merge step of paper2's
`(M3')` apparatus (see `CostMerge.lean`'s `pairCost`/`cross_dearer`, proved by
`decide` over the *typed* four-end configuration, not a single `Bool`).

Formalizing `lem:swap` properly therefore means instantiating (or generalizing) that
existing typed apparatus for paper1's own `pc ∈ {0,2}` convention -- real work
integrating with ~4 existing files, not the "direct `decide` over a
`Fin 16`-indexed case split" the triage note suggested (a plain 4-`Bool` split
provably cannot carry the claim). Left undone this session; the honest path forward
is to check whether `CostMerge.cross_dearer` already covers this after a change of
convention (`pc = 2 - pairCost`, roughly), rather than building a new site-pairing
model from scratch.
-/
