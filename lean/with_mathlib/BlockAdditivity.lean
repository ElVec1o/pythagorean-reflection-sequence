/-
Block additivity for `W m = D_m * C_2` (ROOM/block-additivity, field-mode session).

Engine: a syllable cost function `c0` on the dihedral factor that is 0 at 1 and
1-Lipschitz under left multiplication by the two apex reflections induces a
function `phi : W m -> Nat` with `phi (ev m v) <= v.length` for EVERY letter
word `v`.  Hence any word whose own length is realised by `phi` is geodesic.
-/
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Bridge

namespace BlockAdditivity

open Monoid CoxeterTorsion RotationRelations

variable {m : ℕ}

/-- Cost of a single syllable: `c0` on the dihedral factor, and `1` for a
nontrivial element of the `C_2` factor. -/
def cost (c0 : factor m 0 → ℕ) (p : (i : Fin 2) × factor m i) : ℕ :=
  Fin.cases (motive := fun i => factor m i → ℕ) c0 (fun _ x => if x = 1 then 0 else 1) p.1 p.2

@[simp] theorem cost_zero (c0 : factor m 0 → ℕ) (x : factor m 0) :
    cost c0 ⟨0, x⟩ = c0 x := rfl

@[simp] theorem cost_one_idx (c0 : factor m 0 → ℕ) (x : factor m 1) :
    cost c0 ⟨1, x⟩ = if x = 1 then 0 else 1 := rfl

theorem cost_le_one_of_idx_one (c0 : factor m 0 → ℕ) (x : factor m 1) :
    cost c0 ⟨1, x⟩ ≤ 1 := by
  rw [cost_one_idx]; split <;> omega

theorem cost_of_one (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0) :
    ∀ i : Fin 2, cost c0 ⟨i, (1 : factor m i)⟩ = 0 := by
  intro i
  fin_cases i
  · exact hc0
  · simp

/-- Total cost of a reduced word. -/
def sumCost (c0 : factor m 0 → ℕ) (w : CoprodI.Word (factor m)) : ℕ :=
  (w.toList.map (cost c0)).sum

theorem sumCost_rcons (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0) {i : Fin 2}
    (p : CoprodI.Word.Pair (factor m) i) :
    sumCost c0 (CoprodI.Word.rcons p) = cost c0 ⟨i, p.head⟩ + sumCost c0 p.tail := by
  unfold CoprodI.Word.rcons
  split_ifs with h
  · rw [h, cost_of_one c0 hc0 i, Nat.zero_add]
  · simp [sumCost, CoprodI.Word.cons]

/-- One-step Lipschitz bound: multiplying on the left by a factor element whose
own cost is 1-Lipschitz increases the total cost by at most one. -/
theorem sumCost_smul_le (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0) {i : Fin 2}
    (x : factor m i) (hx : ∀ y : factor m i, cost c0 ⟨i, x * y⟩ ≤ cost c0 ⟨i, y⟩ + 1)
    (w : CoprodI.Word (factor m)) :
    sumCost c0 (CoprodI.of x • w) ≤ sumCost c0 w + 1 := by
  have hw : w = CoprodI.Word.rcons (CoprodI.Word.equivPair i w) :=
    ((CoprodI.Word.equivPair i).symm_apply_apply w).symm
  rw [CoprodI.Word.of_smul_def, sumCost_rcons c0 hc0]
  dsimp only
  conv_rhs => rw [hw, sumCost_rcons c0 hc0]
  have := hx (CoprodI.Word.equivPair i w).head
  omega

/-- The induced length lower bound on `W m`. -/
noncomputable def phi (c0 : factor m 0 → ℕ) (g : W m) : ℕ :=
  sumCost c0 (CoprodI.Word.equiv g)

theorem phi_one (c0 : factor m 0 → ℕ) : phi c0 (1 : W m) = 0 := by
  have h : CoprodI.Word.equiv (1 : W m) = CoprodI.Word.empty := by
    have := CoprodI.Word.equiv.apply_symm_apply (CoprodI.Word.empty (M := factor m))
    rwa [show CoprodI.Word.equiv.symm (CoprodI.Word.empty (M := factor m)) = 1 from
      CoprodI.Word.prod_empty] at this
  rw [phi, h]
  simp [sumCost, CoprodI.Word.empty]

theorem phi_of_mul_le (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0) {i : Fin 2}
    (x : factor m i) (hx : ∀ y : factor m i, cost c0 ⟨i, x * y⟩ ≤ cost c0 ⟨i, y⟩ + 1)
    (g : W m) : phi c0 (CoprodI.of x * g) ≤ phi c0 g + 1 := by
  have he : CoprodI.Word.equiv (CoprodI.of x * g)
      = CoprodI.of x • CoprodI.Word.equiv g := by
    show (CoprodI.of x * g) • (CoprodI.Word.empty (M := factor m))
        = CoprodI.of x • (g • (CoprodI.Word.empty (M := factor m)))
    rw [mul_smul]
  rw [phi, he]
  exact sumCost_smul_le c0 hc0 x hx _

/-! ### The three generators -/

theorem gen_zero_of : gen m 0 = CoprodI.of (M := factor m) (i := 0) (DihedralGroup.sr 1) := rfl
theorem gen_one_of : gen m 1 = CoprodI.of (M := factor m) (i := 0) (DihedralGroup.sr 0) := rfl
theorem gen_two_of (l : Letter) (h0 : l ≠ 0) (h1 : l ≠ 1) :
    gen m l = CoprodI.of (M := factor m) (i := 1) (DihedralGroup.sr 0) := by
  simp only [gen, if_neg h0, if_neg h1, t]

/-- **The engine.**  If `c0` vanishes at `1` and is 1-Lipschitz under left
multiplication by the two apex reflections `sr 1` and `sr 0`, then `phi c0` is a
lower bound for the `{x_0,x_1,x_2}`-word length in `W m`. -/
theorem phi_le_length (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0)
    (hL0 : ∀ y : factor m 0, c0 (DihedralGroup.sr 1 * y) ≤ c0 y + 1)
    (hL1 : ∀ y : factor m 0, c0 (DihedralGroup.sr 0 * y) ≤ c0 y + 1)
    (v : List Letter) : phi c0 (ev m v) ≤ v.length := by
  induction v with
  | nil => simp [ev_nil, phi_one]
  | cons l v ih =>
      rw [ev_cons, List.length_cons]
      have key : phi c0 (gen m l * ev m v) ≤ phi c0 (ev m v) + 1 := by
        by_cases h0 : l = 0
        · subst h0
          rw [gen_zero_of]
          exact phi_of_mul_le c0 hc0 _ (fun y => hL0 y) _
        · by_cases h1 : l = 1
          · subst h1
            rw [gen_one_of]
            exact phi_of_mul_le c0 hc0 _ (fun y => hL1 y) _
          · rw [gen_two_of l h0 h1]
            refine phi_of_mul_le c0 hc0 _ (fun y => ?_) _
            exact le_trans (cost_le_one_of_idx_one c0 _) (by omega)
      omega

/-- **Geodesicity criterion.**  A word whose own length is attained by `phi` is
geodesic: no word representing the same element of `W m` is shorter. -/
theorem geodesic_of_phi_eq (c0 : factor m 0 → ℕ) (hc0 : c0 1 = 0)
    (hL0 : ∀ y : factor m 0, c0 (DihedralGroup.sr 1 * y) ≤ c0 y + 1)
    (hL1 : ∀ y : factor m 0, c0 (DihedralGroup.sr 0 * y) ≤ c0 y + 1)
    {v : List Letter} (hv : phi c0 (ev m v) = v.length)
    (v' : List Letter) (hvv : ev m v' = ev m v) : v.length ≤ v'.length := by
  have := phi_le_length c0 hc0 hL0 hL1 v'
  rw [hvv, hv] at this
  exact this


/-- `phi` is computed by any reduced word whose product is `g`. -/
theorem phi_eq_of_prod (c0 : factor m 0 → ℕ) {Wd : CoprodI.Word (factor m)} {g : W m}
    (h : CoprodI.Word.prod Wd = g) : phi c0 g = sumCost c0 Wd := by
  have : CoprodI.Word.equiv g = Wd := by
    rw [← h]
    exact CoprodI.Word.equiv.apply_symm_apply Wd
  rw [phi, this]

/-! ### The smallest instance of the crux (`m = 3`, `k = 1`, both blocks `x_0 x_1`)

`c3` is the true `{x_0,x_1}`-word length on `D_3` (checked by exhaustive BFS
outside Lean, and its defining properties are checked by `decide` inside). -/

/-- The `{sr 1, sr 0}`-word length on `D_3`. -/
def c3 : factor 3 0 → ℕ
  | DihedralGroup.r k => if k = 0 then 0 else 2
  | DihedralGroup.sr k => if k = 2 then 3 else 1

theorem c3_one : c3 1 = 0 := by decide

theorem c3_L0 : ∀ y : factor 3 0, c3 (DihedralGroup.sr 1 * y) ≤ c3 y + 1 := by decide

theorem c3_L1 : ∀ y : factor 3 0, c3 (DihedralGroup.sr 0 * y) ≤ c3 y + 1 := by decide

/-- The normal form of `x_0 x_1 x_2 x_0 x_1` in `W 3`: `r^2 · x_2 · r^2`. -/
def wd3 : CoprodI.Word (factor 3) where
  toList := [⟨0, DihedralGroup.r 2⟩, ⟨1, DihedralGroup.sr 0⟩, ⟨0, DihedralGroup.r 2⟩]
  ne_one := by decide
  chain_ne := by decide

theorem wd3_prod : CoprodI.Word.prod wd3 = ev 3 [0, 1, 2, 0, 1] := by
  have h : (CoprodI.of (M := factor 3) (i := 0) (DihedralGroup.sr 1) *
      CoprodI.of (M := factor 3) (i := 0) (DihedralGroup.sr 0))
      = CoprodI.of (M := factor 3) (i := 0) (DihedralGroup.r 2) := by
    rw [← map_mul]
    congr 1
  simp only [CoprodI.Word.prod, wd3, ev, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, gen_zero_of, gen_one_of, gen_two_of (2 : Letter) (by decide) (by decide),
    mul_one, ← mul_assoc]
  rw [mul_assoc _ (CoprodI.of (M := factor 3) (i := 0) (DihedralGroup.sr 1))
    (CoprodI.of (M := factor 3) (i := 0) (DihedralGroup.sr 0)), h]

theorem phi_wd3 : phi c3 (ev 3 [0, 1, 2, 0, 1]) = 5 := by
  rw [phi_eq_of_prod c3 wd3_prod]
  decide

/-- **Smallest instance, VERIFIED.**  `x_0 x_1 x_2 x_0 x_1` is geodesic in `W 3`:
no `{x_0,x_1,x_2}`-word representing the same element is shorter than 5. -/
theorem smallest_instance (v : List Letter) (hv : ev 3 v = ev 3 [0, 1, 2, 0, 1]) :
    5 ≤ v.length := by
  have := geodesic_of_phi_eq c3 c3_one c3_L0 c3_L1 (v := [0, 1, 2, 0, 1])
    (by rw [phi_wd3]; rfl) v hv
  simpa using this

end BlockAdditivity

#print axioms BlockAdditivity.phi_le_length
#print axioms BlockAdditivity.geodesic_of_phi_eq
#print axioms BlockAdditivity.phi_eq_of_prod
#print axioms BlockAdditivity.smallest_instance
