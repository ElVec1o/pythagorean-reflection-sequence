/-
Geodesic length of a rotation `plain k` in the dihedral factor of `W m`, for `k <= m/2`.

This is the Lean formalization of the geometric-translation range claim used just before
`cor:onset` in `paper4.tex` ("this holds in the range `c <= m/2`"): among words in the two
letters `{gen m 0, gen m 1}`, no word of length strictly less than `2k` can evaluate to the same
element as `plain k` (`Bridge.ev_plain : ev m (plain k) = R m k`), provided `k <= m/2`.

Strategy: track the *unreduced integer* rotation/reflection index of a word (not its value mod
`m`), by structural recursion mirroring `S_mul_S`/`S_mul_R`/`R_mul_S`/`R_mul_R`. Any word of
length `L` has integer index of absolute value `<= L / 2` (Nat division), and lands in the
"rotation" class iff `L` is even. A word reaching `R m (k : ZMod m)` with `k <= m / 2` and
length `< 2 * k` would give an integer `c` with `|c| < k` and `c ≡ k [ZMOD m]`; since
`|c - k| < 2 * k <= m`, this forces `c = k`, contradiction.
-/
import Bridge

open Monoid RotationRelations

namespace CoxeterTorsion

/-- The two letters used by `gen m 0` and `gen m 1`, tracked without reference to `m`. -/
abbrev Bit := Bool

/-- The unreduced integer trace of a word: `(c, true)` means "currently at rotation index `c`",
`(c, false)` means "currently at reflection index `c`", mirroring `R`/`S` before reducing mod
`m`. Built by right fold, matching `ev`'s `gen l * ev tail` recursion: `step b` is prepended. -/
def step (b : Bit) : ℤ × Bool → ℤ × Bool
  | (c, true)  => if b then (c + 1, false) else (c, false)
  | (c, false) => if b then (c - 1, true)  else (c, true)

/-- The integer trace of a list of bits, starting from the identity `(0, true)` = `R 0`. -/
def trace : List Bit → ℤ × Bool
  | [] => (0, true)
  | b :: w => step b (trace w)

@[simp] theorem trace_nil : trace [] = (0, true) := rfl

@[simp] theorem trace_cons (b : Bit) (w : List Bit) :
    trace (b :: w) = step b (trace w) := rfl

/-- The trace's rotation/reflection tag is the parity of the length: rotation (`true`) iff the
word has even length. -/
theorem trace_tag_eq (w : List Bit) : (trace w).2 = (w.length % 2 == 0) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      rcases htag : trace w with ⟨c, tag⟩
      rw [htag] at ih
      simp only [trace_cons, htag, step]
      cases tag <;> cases b <;> simp_all [List.length_cons, Nat.add_mod] <;> omega

/-- The key bound, by plain structural induction on `w`, carrying the witnessing `j` as an
existential produced fresh at each step (so `omega` never has to reason about division — each
step just increments or keeps `j`, matching the length increasing by exactly `1`). The recursion
is asymmetric: from a "rotation" state the index can only stay or increase, from a "reflection"
state it can only stay or decrease, so the two tags carry different, mutually-dependent bounds:
rotation (even length `2j`) is symmetric, `-j ≤ c ≤ j`; reflection (odd length `2j+1`) is not,
`-j ≤ c ≤ j+1`. -/
theorem trace_bound (w : List Bit) :
    ((trace w).2 = true → ∃ j : ℕ, w.length = 2 * j ∧
      -(j : ℤ) ≤ (trace w).1 ∧ (trace w).1 ≤ (j : ℤ)) ∧
    ((trace w).2 = false → ∃ j : ℕ, w.length = 2 * j + 1 ∧
      -(j : ℤ) ≤ (trace w).1 ∧ (trace w).1 ≤ (j : ℤ) + 1) := by
  induction w with
  | nil => refine ⟨fun _ => ⟨0, by simp⟩, fun h => absurd h (by simp [trace])⟩
  | cons b w ih =>
      obtain ⟨ihT, ihF⟩ := ih
      rcases htag : trace w with ⟨c, tag⟩
      rw [htag] at ihT ihF
      constructor
      · intro h
        cases tag with
        | true => cases b <;> simp_all [step]  -- rotation always steps to reflection: contra
        | false =>
            obtain ⟨j0, hlen0, hlo0, hhi0⟩ := ihF rfl
            have hlen' : (b :: w).length = 2 * (j0 + 1) := by
              simp only [List.length_cons, hlen0]; ring
            refine ⟨j0 + 1, hlen', ?_, ?_⟩ <;>
              · simp only [trace_cons, htag, step] at h ⊢
                cases b <;> simp_all <;> omega
      · intro h
        cases tag with
        | false => cases b <;> simp_all [step]  -- reflection always steps to rotation: contra
        | true =>
            obtain ⟨j0, hlen0, hlo0, hhi0⟩ := ihT rfl
            have hlen' : (b :: w).length = 2 * j0 + 1 := by
              simp only [List.length_cons, hlen0]
            refine ⟨j0, hlen', ?_, ?_⟩ <;>
              · simp only [trace_cons, htag, step] at h ⊢
                cases b <;> simp_all <;> omega

/-- The rotation-only case, cleanly stated: if a word evaluates (in the integer trace) to a
rotation, its index has absolute value at most half its length, `j`. -/
theorem trace_abs_le_of_rotation {w : List Bit} (h : (trace w).2 = true) :
    ∃ j : ℕ, w.length = 2 * j ∧ (trace w).1.natAbs ≤ j := by
  obtain ⟨j, hlen, hlo, hhi⟩ := (trace_bound w).1 h
  exact ⟨j, hlen, by omega⟩

#print axioms trace_tag_eq
#print axioms trace_bound
#print axioms trace_abs_le_of_rotation

/-! ### Connecting the trace to `DihedralGroup m`

`Bit`-word evaluation directly in `DihedralGroup m`, matching `gen m 0 = S m 1`,
`gen m 1 = S m 0` (`Bridge.gen_zero`/`gen_one`) but staying inside the dihedral factor, so no
`ev`/`W m`/`emb` machinery is needed for the core geodesic fact. -/

/-- The element of `DihedralGroup m` reached by a `Bit`-word, matching `trace`'s tag/index. -/
def evD (m : ℕ) (bs : List Bit) : DihedralGroup m :=
  if (trace bs).2 then DihedralGroup.r ((trace bs).1 : ZMod m)
  else DihedralGroup.sr ((trace bs).1 : ZMod m)

/-- `evD` really is left-multiplication by the corresponding generator, matching `ev`'s
`gen l * ev tail` recursion (`bit = true` ↔ letter `0` ↔ `sr 1`; `bit = false` ↔ letter `1` ↔
`sr 0`, per `Bridge.gen_zero`/`gen_one`). -/
theorem evD_cons (m : ℕ) (b : Bit) (bs : List Bit) :
    evD m (b :: bs) = (if b then DihedralGroup.sr 1 else DihedralGroup.sr 0) * evD m bs := by
  unfold evD
  rcases htag : trace bs with ⟨c, tag⟩
  simp only [trace_cons, htag, step]
  cases tag <;> cases b <;>
    simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> push_cast <;> ring_nf

/-- **The dihedral geodesic bound.** If `2 * k ≤ m`, no `Bit`-word of length `< 2 * k` evaluates
(in `DihedralGroup m`) to the rotation `r^k`. Equivalently: `plain k`'s `2k`-letter alternating
word is the *shortest* possible representation of `r^k` among `{sr 0, sr 1}`-words, exactly the
geodesic range claimed in `paper4.tex` before `cor:onset`. -/
theorem evD_ne_rotation_of_short {m k : ℕ} (hmk : 2 * k ≤ m) {bs : List Bit}
    (hlen : bs.length < 2 * k) : evD m bs ≠ DihedralGroup.r ((k : ℕ) : ZMod m) := by
  have hm : 0 < m := by omega
  unfold evD
  rcases htag : trace bs with ⟨c, tag⟩
  simp only [htag]
  split_ifs with h
  · -- rotation case: the integer bound forces c = k, but |c| < k contradicts it
    intro heq
    have h' : (trace bs).2 = true := by rw [htag]; exact h
    obtain ⟨j, hlenj, hc⟩ := trace_abs_le_of_rotation h'
    rw [htag] at hc
    have hjk : j < k := by omega
    have hcong : ((k : ℤ) : ZMod m) = (c : ZMod m) := by
      have heq' : DihedralGroup.r (((k:ℕ):ℤ) : ZMod m) = DihedralGroup.r (c : ZMod m) := by
        simpa using heq.symm
      have hri := DihedralGroup.r.injEq (((k:ℕ):ℤ) : ZMod m) (c : ZMod m)
      rwa [hri] at heq'
    have hdvd : (m : ℤ) ∣ ((c : ℤ) - (k : ℤ)) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact hcong
    have habs : |(c : ℤ) - (k : ℤ)| < (m : ℤ) := by
      rw [abs_lt]; omega
    have hz : (c : ℤ) - (k : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  · -- reflection ≠ rotation: different constructors
    intro heq
    exact absurd heq (by simp)

#print axioms evD_cons
#print axioms evD_ne_rotation_of_short

/-! ### Wrapping through to `W m` and `ev`

The thin step connecting the dihedral-level bound to `Bridge.lean`'s actual objects: `emb` is
injective (a direct instance of `CoprodI.of_injective`), so the bound transfers to `ev`. -/

/-- `Bit true` is letter `0`, `Bit false` is letter `1` — matching `gen_zero`/`gen_one`
(`gen m 0 = S m 1`, `gen m 1 = S m 0`) against `evD`'s `step` (`b = true` uses `sr 1`). -/
def toLetter (b : Bit) : Letter := if b then 0 else 1

theorem emb_injective (m : ℕ) : Function.Injective (emb m) := CoprodI.of_injective 0

/-- `ev` on a `{0,1}`-only word agrees with `evD` pushed through `emb`. -/
theorem ev_toLetter (m : ℕ) (bs : List Bit) :
    ev m (bs.map toLetter) = emb m (evD m bs) := by
  induction bs with
  | nil => simp [ev, evD, trace, R]
  | cons b bs ih =>
      rw [List.map_cons, ev_cons, ih, evD_cons, map_mul]
      cases b <;> simp [toLetter, gen_zero, gen_one, S]

/-- **The geodesic bound, at the level of `W m` and `ev`.** If `2 * k ≤ m`, no `{0,1}`-letter
word of length `< 2 * k` evaluates (via `ev`) to the rotation `R m k` — exactly the range
`c ≤ m/2` used in `paper4.tex` just before `cor:onset`, now for the actual object `ev`/`R`
rather than the auxiliary `evD`. -/
theorem ev_ne_rotation_of_short {m k : ℕ} (hmk : 2 * k ≤ m) {bs : List Bit}
    (hlen : bs.length < 2 * k) : ev m (bs.map toLetter) ≠ R m ((k : ℕ) : ZMod m) := by
  rw [ev_toLetter]
  intro heq
  exact evD_ne_rotation_of_short hmk hlen (emb_injective m heq)

#print axioms ev_toLetter
#print axioms ev_ne_rotation_of_short

end CoxeterTorsion
