/-
General D_m word length `dl`, defined as the infimum over `evD`-representing `Bit`-words,
built to satisfy exactly the two hypotheses `BlockAdditivity.block_additivity` needs:
`dl 1 = 0` and `dl (s * y) <= dl y + 1` for `s ∈ {sr 1, sr 0}`.

The key simplification over a closed-form definition: since `dl` is a literal infimum over
actual representing words, the Lipschitz property is nearly free (prepend a bit to a witness),
not a case-by-case ZMod arithmetic argument.
-/
import DihedralGeodesic

namespace CoxeterTorsion

open Monoid

theorem evD_nil (m : ℕ) : evD m [] = 1 := by
  simp [evD, trace]

/-- Every rotation `r n` (`n : ℕ`, cast to `ZMod m`) is `evD` of some word: induction on `n`,
stepping by two bits `[false, true]` each time (`sr0 * (sr1 * r n) = sr0 * S(n+1) = r(n+1)`,
via `sr_mul_r`/`sr_mul_sr` — matches `Bridge.lean`'s conventions). -/
theorem evD_rot (m : ℕ) : ∀ n : ℕ, ∃ bs : List Bit, evD m bs = DihedralGroup.r (n : ZMod m) := by
  intro n
  induction n with
  | zero => exact ⟨[], by simp [evD_nil]⟩
  | succ n ih =>
      obtain ⟨bs, hbs⟩ := ih
      refine ⟨false :: true :: bs, ?_⟩
      simp only [evD_cons, if_true, if_false, Bool.false_eq_true, Bool.true_eq_false]
      rw [hbs, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
      push_cast
      ring_nf

/-- Every element of `DihedralGroup m` is `evD` of some `Bit`-word: `{sr 0, sr 1}` generate. -/
theorem evD_surjective (m : ℕ) [NeZero m] (y : DihedralGroup m) :
    ∃ bs : List Bit, evD m bs = y := by
  rcases y with k | k
  · obtain ⟨bs, hbs⟩ := evD_rot m k.val
    exact ⟨bs, by rwa [ZMod.natCast_val, ZMod.cast_id] at hbs⟩
  · obtain ⟨bs, hbs⟩ := evD_rot m k.val
    refine ⟨false :: bs, ?_⟩
    simp only [evD_cons, if_false, Bool.false_eq_true]
    rw [hbs, DihedralGroup.sr_mul_r]
    congr 1
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring

/-- The `D_m` word length w.r.t. `{sr 0, sr 1}`, as the infimum over representing words. -/
noncomputable def dl (m : ℕ) (y : DihedralGroup m) : ℕ :=
  sInf {n | ∃ bs : List Bit, bs.length = n ∧ evD m bs = y}

theorem dl_spec (m : ℕ) [NeZero m] (y : DihedralGroup m) :
    ∃ bs : List Bit, bs.length = dl m y ∧ evD m bs = y := by
  have hne : {n | ∃ bs : List Bit, bs.length = n ∧ evD m bs = y}.Nonempty := by
    obtain ⟨bs, hbs⟩ := evD_surjective m y
    exact ⟨bs.length, bs, rfl, hbs⟩
  exact Nat.sInf_mem hne

theorem dl_one (m : ℕ) : dl m (1 : DihedralGroup m) = 0 := by
  have h0 : (0 : ℕ) ∈ {n | ∃ bs : List Bit, bs.length = n ∧ evD m bs = 1} :=
    ⟨[], rfl, evD_nil m⟩
  exact Nat.le_zero.mp (Nat.sInf_le h0)

theorem dl_le_of_evD (m : ℕ) {y : DihedralGroup m} {bs : List Bit} (h : evD m bs = y) :
    dl m y ≤ bs.length :=
  Nat.sInf_le ⟨bs, rfl, h⟩

/-- **The Lipschitz property**, for either generator, in one lemma. -/
theorem dl_mul_le (m : ℕ) [NeZero m] (b : Bit) (y : DihedralGroup m) :
    dl m ((if b then DihedralGroup.sr (1 : ZMod m) else DihedralGroup.sr (0 : ZMod m)) * y)
      ≤ dl m y + 1 := by
  obtain ⟨bs, hlen, hbs⟩ := dl_spec m y
  have : evD m (b :: bs) = (if b then DihedralGroup.sr 1 else DihedralGroup.sr 0) * y := by
    rw [evD_cons, hbs]
  have hle := dl_le_of_evD m this
  simpa [hlen] using hle

theorem dl_L0 (m : ℕ) [NeZero m] (y : DihedralGroup m) :
    dl m (DihedralGroup.sr 1 * y) ≤ dl m y + 1 := dl_mul_le m true y

theorem dl_L1 (m : ℕ) [NeZero m] (y : DihedralGroup m) :
    dl m (DihedralGroup.sr 0 * y) ≤ dl m y + 1 := dl_mul_le m false y

end CoxeterTorsion

#print axioms CoxeterTorsion.dl_one
#print axioms CoxeterTorsion.dl_L0
#print axioms CoxeterTorsion.dl_L1
