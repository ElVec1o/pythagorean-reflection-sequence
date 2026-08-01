/-
The letter invariants behind the rotation relations on a stratum
(paper 4, Theorem "Rotation relations").

For a word `w` in the three generators and a letter `i`, the paper uses
`c_i(w)`, the number of occurrences of `i` at odd positions of `w` minus the
number at even positions.  Theorem `thm:rot` rests on three facts about these:

  (1) they are additive under concatenation, up to the sign contributed by the
      parity of the first word's length;
  (2) reversing a word of even length negates every `c_i`, which is what pairs
      the normal forms `w_{a,b}` with `c_1 = c` against those with `c_1 = -c`;
  (3) the reduced words of length `2c+2` with `c_2 = 0` and `c_1 = c` are
      exactly the `c^2` normal forms of the theorem.

(1) and (2) are proved here, and so is (3), as `classify_normal_forms`: every
reduced word of length `2c+2` with `c_2 = 0` and `c_1 = c` carries one `2` in a
first slot and one in a second, in distinct non-consecutive blocks.  The number
of admissible index pairs is `c^2`, elementary arithmetic on the index set,
confirmed by the kernel for `c = 1, 2, 3` through `validCount`.  The
free-product argument identifying the unique word of finite order in
`W_m = D_m * C_2` is not formalized: it needs the torsion theorem for free
products, which Mathlib does not carry.

No imports: core Lean 4 only.
-/

namespace RotationRelations

/-- Letters of the free product `C_2 * C_2 * C_2`. -/
abbrev Letter := Fin 3

/-- `cvec w i` is the signed occurrence count of the letter `i` in `w`:
positions alternate in sign, starting with `+` at the head. -/
def cvec : List Letter → Letter → Int
  | [], _ => 0
  | x :: xs, i => (if x = i then 1 else 0) - cvec xs i

/-- A word is reduced when no two adjacent letters agree. -/
def Reduced : List Letter → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≠ y ∧ Reduced (y :: xs)

/-- Concatenation law, by the parity of the first word's length.  Stating it in
these two cases avoids any product of unknowns, so the arithmetic stays linear.
Both cases are proved together, each feeding the other. -/
theorem cvec_append_cases (u : List Letter) :
    ∀ (v : List Letter) (i : Letter),
      (u.length % 2 = 0 → cvec (u ++ v) i = cvec u i + cvec v i) ∧
      (u.length % 2 = 1 → cvec (u ++ v) i = cvec u i - cvec v i) := by
  induction u with
  | nil =>
    intro v i
    exact ⟨fun _ => by simp [cvec], fun h => by simp at h⟩
  | cons x xs ih =>
    intro v i
    obtain ⟨ihe, iho⟩ := ih v i
    constructor
    · intro h
      have hx : xs.length % 2 = 1 := by
        simp only [List.length_cons] at h; omega
      show cvec (x :: (xs ++ v)) i = cvec (x :: xs) i + cvec v i
      simp only [cvec]
      rw [iho hx]
      omega
    · intro h
      have hx : xs.length % 2 = 0 := by
        simp only [List.length_cons] at h; omega
      show cvec (x :: (xs ++ v)) i = cvec (x :: xs) i - cvec v i
      simp only [cvec]
      rw [ihe hx]
      omega

theorem cvec_append_even (u v : List Letter) (i : Letter) (h : u.length % 2 = 0) :
    cvec (u ++ v) i = cvec u i + cvec v i := (cvec_append_cases u v i).1 h

theorem cvec_append_odd (u v : List Letter) (i : Letter) (h : u.length % 2 = 1) :
    cvec (u ++ v) i = cvec u i - cvec v i := (cvec_append_cases u v i).2 h

/-- A single letter. -/
theorem cvec_singleton (x i : Letter) :
    cvec [x] i = if x = i then 1 else 0 := by
  simp [cvec]

/-- Reversal law, again by parity and again proved in both cases at once:
reversing an even-length word negates every invariant, reversing an odd-length
word preserves them.  The first case is the pairing used in the theorem, which
carries the normal forms with `c_1 = c` onto those with `c_1 = -c`. -/
theorem cvec_reverse_cases (w : List Letter) :
    ∀ i : Letter,
      (w.length % 2 = 0 → cvec w.reverse i = - cvec w i) ∧
      (w.length % 2 = 1 → cvec w.reverse i = cvec w i) := by
  induction w with
  | nil =>
    intro i
    exact ⟨fun _ => by simp [cvec], fun h => by simp at h⟩
  | cons x xs ih =>
    intro i
    obtain ⟨ihe, iho⟩ := ih i
    constructor
    · intro h
      have hx : xs.length % 2 = 1 := by
        simp only [List.length_cons] at h; omega
      have hrl : xs.reverse.length % 2 = 1 := by simpa using hx
      rw [List.reverse_cons, cvec_append_odd _ _ _ hrl, iho hx, cvec_singleton]
      simp only [cvec]
      omega
    · intro h
      have hx : xs.length % 2 = 0 := by
        simp only [List.length_cons] at h; omega
      have hrl : xs.reverse.length % 2 = 0 := by simpa using hx
      rw [List.reverse_cons, cvec_append_even _ _ _ hrl, ihe hx, cvec_singleton]
      simp only [cvec]
      omega

theorem cvec_reverse_even (w : List Letter) (i : Letter) (h : w.length % 2 = 0) :
    cvec w.reverse i = - cvec w i := (cvec_reverse_cases w i).1 h

/-- Boolean form of `Reduced`, for kernel computation. -/
def reducedB : List Letter → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => (x != y) && reducedB (y :: xs)

theorem reducedB_iff (w : List Letter) : reducedB w = true ↔ Reduced w := by
  induction w with
  | nil => simp [reducedB, Reduced]
  | cons x xs ih =>
    cases xs with
    | nil => simp [reducedB, Reduced]
    | cons y ys =>
      simp only [reducedB, Reduced, Bool.and_eq_true, bne_iff_ne, ne_eq] at *
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, ih.mp h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ih.mpr h2⟩

/-- All words of a given length, for kernel computation. -/
def extend (ws : List (List Letter)) : List (List Letter) :=
  ws.foldr (fun w acc => (0 :: w) :: (1 :: w) :: (2 :: w) :: acc) []

def allWords : Nat → List (List Letter)
  | 0 => [[]]
  | n + 1 => extend (allWords n)

/-- The words the theorem counts: reduced, of length `2c+2`, with `c_2 = 0` and
`c_1 = c`. -/
def validCount (c : Nat) : Nat :=
  ((allWords (2 * c + 2)).filter
    (fun w => reducedB w && (cvec w 2 == 0) && (cvec w 1 == (c : Int)))).length

/-- The count `c^2`, checked by the kernel for small `c`. -/
theorem validCount_one : validCount 1 = 1 := by decide

theorem validCount_two : validCount 2 = 4 := by decide

set_option maxRecDepth 40000 in
theorem validCount_three : validCount 3 = 9 := by decide

-- `c = 4` and beyond exhaust the kernel's stack.

/-! ## Peeling two letters at a time

A word of even length is a list of two-letter blocks, and every invariant is a
sum over blocks.  `cvec_cons2` peels one block, and `cvec_le_half` bounds an
invariant by the number of blocks; together they exclude all but a few block
types at each step of the classification. -/

/-- Peeling one block from the front. -/
theorem cvec_cons2 (x y : Letter) (w : List Letter) (i : Letter) :
    cvec (x :: y :: w) i
      = (if x = i then 1 else 0) - (if y = i then 1 else 0) + cvec w i := by
  simp only [cvec]
  omega

/-- An invariant is bounded by the number of blocks. -/
theorem cvec_le_half : ∀ (n : Nat) (w : List Letter) (i : Letter),
    w.length = 2 * n → cvec w i ≤ n ∧ -(n : Int) ≤ cvec w i := by
  intro n
  induction n with
  | zero =>
    intro w i hw
    have : w = [] := by
      cases w with
      | nil => rfl
      | cons a as => simp at hw
    subst this
    simp [cvec]
  | succ n ih =>
    intro w i hw
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨h1, h2⟩ := ih rest i hrest
      have hb1 : (if a = i then (1:Int) else 0) ≤ 1 ∧ 0 ≤ (if a = i then (1:Int) else 0) := by
        by_cases h : a = i <;> simp [h]
      have hb2 : (if b = i then (1:Int) else 0) ≤ 1 ∧ 0 ≤ (if b = i then (1:Int) else 0) := by
        by_cases h : b = i <;> simp [h]
      rw [cvec_cons2]
      omega

/-- The all-plain pattern `(1,0)` repeated. -/
def plain : Nat → List Letter
  | 0 => []
  | n + 1 => 1 :: 0 :: plain n

/-- If the first invariant is maximal then no block carries a `2` in its first
slot, so the second invariant cannot be positive. -/
theorem cvec2_nonpos_of_max : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → cvec w 1 = n → cvec w 2 ≤ 0 := by
  intro n
  induction n with
  | zero =>
    intro w hw _
    match w with
    | [] => simp [cvec]
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw h1
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      obtain ⟨hb1, hb2⟩ := cvec_le_half n rest 1 hrest
      rw [cvec_cons2] at h1
      -- maximality forces a = 1 and b ≠ 1, and the rest to be maximal too
      have ha1 : a = 1 := by
        by_cases h : a = 1
        · exact h
        · exfalso
          simp only [if_neg h] at h1
          have : (if b = 1 then (1:Int) else 0) ≥ 0 := by
            by_cases hb : b = 1 <;> simp [hb]
          omega
      have hrestmax : cvec rest 1 = n := by
        have hbb : (if b = 1 then (1:Int) else 0) ≥ 0 := by
          by_cases hb : b = 1 <;> simp [hb]
        simp only [ha1, if_pos rfl] at h1
        omega
      have hres := ih rest hrest hrestmax
      have ha2 : a ≠ 2 := by rw [ha1]; decide
      rw [cvec_cons2]
      have hbb2 : (if b = 2 then (1:Int) else 0) ≥ 0 := by
        by_cases hb : b = 2 <;> simp [hb]
      simp only [if_neg ha2]
      omega

theorem Reduced_tail {x : Letter} {xs : List Letter} (h : Reduced (x :: xs)) :
    Reduced xs := by
  cases xs with
  | nil => trivial
  | cons y ys => exact h.2

/-- Letters are exhausted by `0, 1, 2`. -/
theorem letter_cases (x : Letter) (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  revert h1 h2
  revert x
  decide

/-- State F of the classification: a maximal first invariant with vanishing
second invariant forces the all-plain word. -/
theorem classify_plain : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → Reduced w → cvec w 1 = n → cvec w 2 = 0 → w = plain n := by
  intro n
  induction n with
  | zero =>
    intro w hw _ _ _
    match w with
    | [] => rfl
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw hred h1 h2
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      obtain ⟨hub, hlb⟩ := cvec_le_half n rest 1 hrest
      rw [cvec_cons2] at h1
      have hbnn : (if b = 1 then (1:Int) else 0) ≥ 0 := by
        by_cases hb : b = 1 <;> simp [hb]
      have ha1 : a = 1 := by
        by_cases h : a = 1
        · exact h
        · exfalso; rw [if_neg h] at h1; omega
      have hb1 : b ≠ 1 := by
        intro hb
        rw [if_pos ha1, if_pos hb] at h1
        omega
      have hmax : cvec rest 1 = n := by
        rw [if_pos ha1, if_neg hb1] at h1
        omega
      have hnp := cvec2_nonpos_of_max n rest hrest hmax
      have ha2 : a ≠ 2 := by rw [ha1]; decide
      rw [cvec_cons2] at h2
      have hb2 : b ≠ 2 := by
        intro hb
        rw [if_neg ha2, if_pos hb] at h2
        omega
      have hb0 : b = 0 := letter_cases b hb1 hb2
      have h2rest : cvec rest 2 = 0 := by
        rw [if_neg ha2, if_neg hb2] at h2
        omega
      have := ih rest hrest (Reduced_tail (Reduced_tail hred)) hmax h2rest
      rw [ha1, hb0, this]
      rfl

/-- A block contributes at most one to the two invariants together, since its
first letter can match at most one of `1` and `2`. -/
theorem cvec_sum_le : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → cvec w 1 + cvec w 2 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro w hw
    match w with
    | [] => simp [cvec]
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      have hres := ih rest hrest
      have hx : (if a = 1 then (1:Int) else 0) + (if a = 2 then (1:Int) else 0) ≤ 1 := by
        by_cases h1 : a = 1
        · subst h1; simp
        · by_cases h2 : a = 2 <;> simp [h1, h2]
      have hy : (0:Int) ≤ (if b = 1 then (1:Int) else 0) + (if b = 2 then (1:Int) else 0) := by
        by_cases h1 : b = 1 <;> by_cases h2 : b = 2 <;> simp [h1, h2]
      rw [cvec_cons2, cvec_cons2]
      omega

/-- `(1,0)` blocks with the second slot of block `j` carrying `2`. -/
def markY : Nat → Nat → List Letter
  | 0, _ => []
  | n + 1, 0 => 1 :: 2 :: plain n
  | n + 1, j + 1 => 1 :: 0 :: markY n j

/-- `(1,0)` blocks with the first slot of block `a` carrying `2`. -/
def markX : Nat → Nat → List Letter
  | 0, _ => []
  | n + 1, 0 => 2 :: 0 :: plain n
  | n + 1, a + 1 => 1 :: 0 :: markX n a

/-- State E: the first invariant maximal and the second equal to `-1` forces
one block to carry `2` in its second slot, the others being plain. -/
theorem classify_evenPlaced : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → Reduced w → cvec w 1 = n → cvec w 2 = -1 →
    ∃ j, j < n ∧ w = markY n j := by
  intro n
  induction n with
  | zero =>
    intro w hw _ _ h2
    match w with
    | [] => simp [cvec] at h2
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw hred h1 h2
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      obtain ⟨hub, hlb⟩ := cvec_le_half n rest 1 hrest
      rw [cvec_cons2] at h1
      have hbnn : (0:Int) ≤ (if b = 1 then (1:Int) else 0) := by
        by_cases hb : b = 1 <;> simp [hb]
      have ha1 : a = 1 := by
        by_cases h : a = 1
        · exact h
        · exfalso; rw [if_neg h] at h1; omega
      have hb1 : b ≠ 1 := by
        intro hb; rw [if_pos ha1, if_pos hb] at h1; omega
      have hmax : cvec rest 1 = n := by
        rw [if_pos ha1, if_neg hb1] at h1; omega
      have ha2 : a ≠ 2 := by rw [ha1]; decide
      rw [cvec_cons2] at h2
      by_cases hb2 : b = 2
      · rw [if_neg ha2, if_pos hb2] at h2
        have h2rest : cvec rest 2 = 0 := by omega
        have := classify_plain n rest hrest (Reduced_tail (Reduced_tail hred)) hmax h2rest
        exact ⟨0, by omega, by rw [ha1, hb2, this]; rfl⟩
      · have hb0 : b = 0 := letter_cases b hb1 hb2
        have h2rest : cvec rest 2 = -1 := by
          rw [if_neg ha2, if_neg hb2] at h2; omega
        obtain ⟨j, hj, hw'⟩ :=
          ih rest hrest (Reduced_tail (Reduced_tail hred)) hmax h2rest
        exact ⟨j + 1, by omega, by rw [ha1, hb0, hw']; rfl⟩

/-- State O: the second invariant equal to `1` with the first one short by one
forces a single block to carry `2` in its first slot. -/
theorem classify_oddPlaced : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → Reduced w → cvec w 1 = (n : Int) - 1 → cvec w 2 = 1 →
    ∃ a, a < n ∧ w = markX n a := by
  intro n
  induction n with
  | zero =>
    intro w hw _ _ h2
    match w with
    | [] => simp [cvec] at h2
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw hred h1 h2
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | a :: b :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      have hab : a ≠ b := hred.1
      obtain ⟨hub, hlb⟩ := cvec_le_half n rest 1 hrest
      have hsum := cvec_sum_le n rest hrest
      have hbnn : (0:Int) ≤ (if b = 1 then (1:Int) else 0) := by
        by_cases hb : b = 1 <;> simp [hb]
      rw [cvec_cons2] at h1
      rw [cvec_cons2] at h2
      by_cases ha2 : a = 2
      · have hb2 : b ≠ 2 := fun hb => hab (ha2.trans hb.symm)
        have ha1 : a ≠ 1 := by rw [ha2]; decide
        have hb1 : b ≠ 1 := by
          intro hb; rw [if_neg ha1, if_pos hb] at h1; omega
        have hmax : cvec rest 1 = n := by
          rw [if_neg ha1, if_neg hb1] at h1; omega
        have h2rest : cvec rest 2 = 0 := by
          rw [if_pos ha2, if_neg hb2] at h2; omega
        have hb0 : b = 0 := letter_cases b hb1 hb2
        have := classify_plain n rest hrest (Reduced_tail (Reduced_tail hred)) hmax h2rest
        exact ⟨0, by omega, by rw [ha2, hb0, this]; rfl⟩
      · by_cases ha1 : a = 1
        · have hb1 : b ≠ 1 := fun hb => hab (ha1.trans hb.symm)
          have hb2 : b ≠ 2 := by
            intro hb
            rw [if_pos ha1, if_neg hb1] at h1
            rw [if_neg ha2, if_pos hb] at h2
            omega
          have hb0 : b = 0 := letter_cases b hb1 hb2
          have h1rest : cvec rest 1 = (n : Int) - 1 := by
            rw [if_pos ha1, if_neg hb1] at h1; omega
          have h2rest : cvec rest 2 = 1 := by
            rw [if_neg ha2, if_neg hb2] at h2; omega
          obtain ⟨a', ha', hw'⟩ :=
            ih rest hrest (Reduced_tail (Reduced_tail hred)) h1rest h2rest
          exact ⟨a' + 1, by omega, by rw [ha1, hb0, hw']; rfl⟩
        · exfalso
          have hb1 : b ≠ 1 := by
            intro hb; rw [if_neg ha1, if_pos hb] at h1; omega
          have hmax : cvec rest 1 = n := by
            rw [if_neg ha1, if_neg hb1] at h1; omega
          have hnp := cvec2_nonpos_of_max n rest hrest hmax
          have hbb : (0:Int) ≤ (if b = 2 then (1:Int) else 0) := by
            by_cases hb : b = 2 <;> simp [hb]
          rw [if_neg ha2] at h2
          omega

/-- Both marks: block `a` carries `2` in its first slot and block `j` in its
second.  The diagonal is excluded by reducedness and its value is immaterial. -/
def markBoth : Nat → Nat → Nat → List Letter
  | 0, _, _ => []
  | _ + 1, 0, 0 => []
  | n + 1, 0, j + 1 => 2 :: 0 :: markY n j
  | n + 1, a + 1, 0 => 1 :: 2 :: markX n a
  | n + 1, a + 1, j + 1 => 1 :: 0 :: markBoth n a j

/-- The admissible index pairs: the two marks in distinct, non-consecutive
blocks. -/
def Admissible (n a j : Nat) : Prop := a < n ∧ j < n ∧ j ≠ a ∧ a ≠ j + 1

/-- The classification.  A reduced word of length `2n` whose second invariant
vanishes and whose first is short by one carries exactly two letters `2`, one
in a first slot and one in a second, in distinct non-consecutive blocks. -/
theorem classify_main : ∀ (n : Nat) (w : List Letter),
    w.length = 2 * n → Reduced w → cvec w 1 = (n : Int) - 1 → cvec w 2 = 0 →
    ∃ a j, Admissible n a j ∧ w = markBoth n a j := by
  intro n
  induction n with
  | zero =>
    intro w hw _ h1 _
    match w with
    | [] => simp [cvec] at h1
    | a :: as => simp only [List.length_cons] at hw; omega
  | succ n ih =>
    intro w hw hred h1 h2
    match w with
    | [] => simp only [List.length_nil] at hw; omega
    | [a] => simp only [List.length_cons, List.length_nil] at hw; omega
    | p :: q :: rest =>
      have hrest : rest.length = 2 * n := by
        simp only [List.length_cons] at hw; omega
      have hpq : p ≠ q := hred.1
      obtain ⟨hub, hlb⟩ := cvec_le_half n rest 1 hrest
      have hqnn : (0:Int) ≤ (if q = 1 then (1:Int) else 0) := by
        by_cases hq : q = 1 <;> simp [hq]
      rw [cvec_cons2] at h1
      rw [cvec_cons2] at h2
      by_cases hp2 : p = 2
      · have hq2 : q ≠ 2 := fun hq => hpq (hp2.trans hq.symm)
        have hp1 : p ≠ 1 := by rw [hp2]; decide
        have hq1 : q ≠ 1 := by
          intro hq; rw [if_neg hp1, if_pos hq] at h1; omega
        have hmax : cvec rest 1 = n := by
          rw [if_neg hp1, if_neg hq1] at h1; omega
        have h2rest : cvec rest 2 = -1 := by
          rw [if_pos hp2, if_neg hq2] at h2; omega
        have hq0 : q = 0 := letter_cases q hq1 hq2
        obtain ⟨j, hj, hw'⟩ :=
          classify_evenPlaced n rest hrest (Reduced_tail (Reduced_tail hred)) hmax h2rest
        exact ⟨0, j + 1, ⟨by omega, by omega, by omega, by omega⟩,
          by rw [hp2, hq0, hw']; rfl⟩
      · by_cases hp1 : p = 1
        · have hq1 : q ≠ 1 := fun hq => hpq (hp1.trans hq.symm)
          have h1rest : cvec rest 1 = (n : Int) - 1 := by
            rw [if_pos hp1, if_neg hq1] at h1; omega
          by_cases hq2 : q = 2
          · have h2rest : cvec rest 2 = 1 := by
              rw [if_neg hp2, if_pos hq2] at h2; omega
            obtain ⟨a', ha', hw'⟩ :=
              classify_oddPlaced n rest hrest (Reduced_tail (Reduced_tail hred))
                h1rest h2rest
            cases a' with
            | zero =>
              exfalso
              cases n with
              | zero => omega
              | succ m =>
                have hq : Reduced (q :: markX (m + 1) 0) := by
                  rw [← hw']; exact hred.2
                simp only [markX] at hq
                exact absurd hq2 hq.1
            | succ a'' =>
              exact ⟨a'' + 2, 0, ⟨by omega, by omega, by omega, by omega⟩,
                by rw [hp1, hq2, hw']; rfl⟩
          · have hq0 : q = 0 := letter_cases q hq1 hq2
            have h2rest : cvec rest 2 = 0 := by
              rw [if_neg hp2, if_neg hq2] at h2; omega
            obtain ⟨a', j', ⟨ha', hj', hne, hne2⟩, hw'⟩ :=
              ih rest hrest (Reduced_tail (Reduced_tail hred)) h1rest h2rest
            exact ⟨a' + 1, j' + 1, ⟨by omega, by omega, by omega, by omega⟩,
              by rw [hp1, hq0, hw']; rfl⟩
        · exfalso
          have hp0 : p = 0 := letter_cases p hp1 hp2
          have hq1 : q ≠ 1 := by
            intro hq; rw [if_neg hp1, if_pos hq] at h1; omega
          have hmax : cvec rest 1 = n := by
            rw [if_neg hp1, if_neg hq1] at h1; omega
          have hnp := cvec2_nonpos_of_max n rest hrest hmax
          rw [if_neg hp2] at h2
          have hq2 : q ≠ 2 := by
            intro hq; rw [if_pos hq] at h2; omega
          have hq0 : q = 0 := letter_cases q hq1 hq2
          exact hpq (hp0.trans hq0.symm)

/-! ## The converse

Each admissible shape really is a reduced word with the stated invariants.  The
adjacency constraints of `Admissible` are exactly what reducedness needs at the
block junctions. -/

theorem ne01 : (0 : Letter) ≠ 1 := by decide
theorem ne02 : (0 : Letter) ≠ 2 := by decide
theorem ne12 : (1 : Letter) ≠ 2 := by decide
theorem ne10 : (1 : Letter) ≠ 0 := by decide
theorem ne21 : (2 : Letter) ≠ 1 := by decide
theorem ne20 : (2 : Letter) ≠ 0 := by decide

theorem plain_length : ∀ n, (plain n).length = 2 * n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp only [plain, List.length_cons, ih]; omega

theorem plain_cvec1 : ∀ n, cvec (plain n) 1 = n := by
  intro n; induction n with
  | zero => simp [plain, cvec]
  | succ n ih =>
    rw [plain, cvec_cons2, ih, if_pos rfl, if_neg ne01]
    push_cast; omega

theorem plain_cvec2 : ∀ n, cvec (plain n) 2 = 0 := by
  intro n; induction n with
  | zero => simp [plain, cvec]
  | succ n ih =>
    rw [plain, cvec_cons2, ih, if_neg ne12, if_neg ne02]
    omega

theorem plain_reduced_cons : ∀ n (y : Letter), y ≠ 1 → Reduced (y :: plain n) := by
  intro n; induction n with
  | zero => intro y _; trivial
  | succ n ih => intro y hy; exact ⟨hy, ne10, ih 0 ne01⟩

theorem plain_reduced : ∀ n, Reduced (plain n) := by
  intro n; cases n with
  | zero => trivial
  | succ n => exact ⟨ne10, plain_reduced_cons n 0 ne01⟩

theorem markY_length : ∀ n j, (markY n j).length = 2 * n := by
  intro n; induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j; cases j with
    | zero => simp only [markY, List.length_cons, plain_length]; omega
    | succ j => simp only [markY, List.length_cons, ih]; omega

theorem markY_cvec1 : ∀ n j, cvec (markY n j) 1 = n := by
  intro n; induction n with
  | zero => intro j; simp [markY, cvec]
  | succ n ih =>
    intro j; cases j with
    | zero => rw [markY, cvec_cons2, plain_cvec1, if_pos rfl, if_neg ne21]; push_cast; omega
    | succ j => rw [markY, cvec_cons2, ih j, if_pos rfl, if_neg ne01]; push_cast; omega

theorem markY_cvec2 : ∀ n j, j < n → cvec (markY n j) 2 = -1 := by
  intro n; induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj; cases j with
    | zero => rw [markY, cvec_cons2, plain_cvec2, if_neg ne12, if_pos rfl]; omega
    | succ j =>
      rw [markY, cvec_cons2, ih j (by omega), if_neg ne12, if_neg ne02]; omega

theorem markY_reduced_cons : ∀ n j (y : Letter), y ≠ 1 → Reduced (y :: markY n j) := by
  intro n; induction n with
  | zero => intro j y _; trivial
  | succ n ih =>
    intro j y hy; cases j with
    | zero => exact ⟨hy, ne12, plain_reduced_cons n 2 ne21⟩
    | succ j => exact ⟨hy, ne10, ih j 0 ne01⟩

theorem markX_length : ∀ n a, (markX n a).length = 2 * n := by
  intro n; induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a; cases a with
    | zero => simp only [markX, List.length_cons, plain_length]; omega
    | succ a => simp only [markX, List.length_cons, ih]; omega

theorem markX_cvec1 : ∀ n a, a < n → cvec (markX n a) 1 = (n : Int) - 1 := by
  intro n; induction n with
  | zero => intro a ha; omega
  | succ n ih =>
    intro a ha; cases a with
    | zero => rw [markX, cvec_cons2, plain_cvec1, if_neg ne21, if_neg ne01]; push_cast; omega
    | succ a =>
      rw [markX, cvec_cons2, ih a (by omega), if_pos rfl, if_neg ne01]; push_cast; omega

theorem markX_cvec2 : ∀ n a, a < n → cvec (markX n a) 2 = 1 := by
  intro n; induction n with
  | zero => intro a ha; omega
  | succ n ih =>
    intro a ha; cases a with
    | zero => rw [markX, cvec_cons2, plain_cvec2, if_pos rfl, if_neg ne02]; omega
    | succ a =>
      rw [markX, cvec_cons2, ih a (by omega), if_neg ne12, if_neg ne02]; omega

theorem markX_reduced_cons : ∀ n a (y : Letter), y ≠ 1 → (a = 0 → y ≠ 2) →
    Reduced (y :: markX n a) := by
  intro n; induction n with
  | zero => intro a y _ _; trivial
  | succ n ih =>
    intro a y hy hy2; cases a with
    | zero => exact ⟨hy2 rfl, ne20, plain_reduced_cons n 0 ne01⟩
    | succ a => exact ⟨hy, ne10, ih a 0 ne01 (fun _ => ne02)⟩

theorem markBoth_length : ∀ n a j, Admissible n a j → (markBoth n a j).length = 2 * n := by
  intro n; induction n with
  | zero => intro a j h; obtain ⟨ha, _⟩ := h; omega
  | succ n ih =>
    intro a j h
    obtain ⟨ha, hj, hne, hne2⟩ := h
    cases a with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j => simp only [markBoth, List.length_cons, markY_length]; omega
    | succ a =>
      cases j with
      | zero => simp only [markBoth, List.length_cons, markX_length]; omega
      | succ j =>
        have : Admissible n a j := ⟨by omega, by omega, by omega, by omega⟩
        simp only [markBoth, List.length_cons, ih a j this]; omega

theorem markBoth_cvec1 : ∀ n a j, Admissible n a j →
    cvec (markBoth n a j) 1 = (n : Int) - 1 := by
  intro n; induction n with
  | zero => intro a j h; obtain ⟨ha, _⟩ := h; omega
  | succ n ih =>
    intro a j h
    obtain ⟨ha, hj, hne, hne2⟩ := h
    cases a with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j =>
        rw [markBoth, cvec_cons2, markY_cvec1, if_neg ne21, if_neg ne01]; push_cast; omega
    | succ a =>
      cases j with
      | zero =>
        rw [markBoth, cvec_cons2, markX_cvec1 n a (by omega), if_pos rfl, if_neg ne21]
        push_cast; omega
      | succ j =>
        have hadm : Admissible n a j := ⟨by omega, by omega, by omega, by omega⟩
        rw [markBoth, cvec_cons2, ih a j hadm, if_pos rfl, if_neg ne01]; push_cast; omega

theorem markBoth_cvec2 : ∀ n a j, Admissible n a j → cvec (markBoth n a j) 2 = 0 := by
  intro n; induction n with
  | zero => intro a j h; obtain ⟨ha, _⟩ := h; omega
  | succ n ih =>
    intro a j h
    obtain ⟨ha, hj, hne, hne2⟩ := h
    cases a with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j =>
        rw [markBoth, cvec_cons2, markY_cvec2 n j (by omega), if_pos rfl, if_neg ne02]; omega
    | succ a =>
      cases j with
      | zero =>
        rw [markBoth, cvec_cons2, markX_cvec2 n a (by omega), if_neg ne12, if_pos rfl]; omega
      | succ j =>
        have hadm : Admissible n a j := ⟨by omega, by omega, by omega, by omega⟩
        rw [markBoth, cvec_cons2, ih a j hadm, if_neg ne12, if_neg ne02]; omega

theorem markBoth_reduced_cons : ∀ n a j, Admissible n a j → ∀ y : Letter,
    y ≠ 1 → (a = 0 → y ≠ 2) → Reduced (y :: markBoth n a j) := by
  intro n; induction n with
  | zero => intro a j h; obtain ⟨ha, _⟩ := h; omega
  | succ n ih =>
    intro a j h y hy hy2
    obtain ⟨ha, hj, hne, hne2⟩ := h
    cases a with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j => exact ⟨hy2 rfl, ne20, markY_reduced_cons n j 0 ne01⟩
    | succ a =>
      cases j with
      | zero =>
        have ha0 : a ≠ 0 := by omega
        exact ⟨hy, ne12, markX_reduced_cons n a 2 ne21 (fun h0 => absurd h0 ha0)⟩
      | succ j =>
        have hadm : Admissible n a j := ⟨by omega, by omega, by omega, by omega⟩
        exact ⟨hy, ne10, ih a j hadm 0 ne01 (fun _ => ne02)⟩

/-- **The converse.**  Every admissible shape is a reduced word of the right
length with the prescribed invariants. -/
theorem markBoth_valid : ∀ n a j, Admissible n a j →
    (markBoth n a j).length = 2 * n ∧ Reduced (markBoth n a j) ∧
    cvec (markBoth n a j) 1 = (n : Int) - 1 ∧ cvec (markBoth n a j) 2 = 0 := by
  intro n a j h
  refine ⟨markBoth_length n a j h, ?_, markBoth_cvec1 n a j h, markBoth_cvec2 n a j h⟩
  obtain ⟨ha, hj, hne, hne2⟩ := h
  cases n with
  | zero => omega
  | succ n =>
    cases a with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j =>
        exact ⟨ne20, markY_reduced_cons n j 0 ne01⟩
    | succ a =>
      cases j with
      | zero =>
        have ha0 : a ≠ 0 := by omega
        exact ⟨ne12, markX_reduced_cons n a 2 ne21 (fun h0 => absurd h0 ha0)⟩
      | succ j =>
        have hadm : Admissible n a j := ⟨by omega, by omega, by omega, by omega⟩
        exact ⟨ne10, markBoth_reduced_cons n a j hadm 0 ne01 (fun _ => ne02)⟩

/-! ## The count

The admissible pairs are counted directly, without `Finset`: `rowCount a m` is
the number of admissible `j < m` for a fixed `a`, and `pairCount n k` sums it
over `a < k`. -/

def rowCount (a : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => (if m ≠ a ∧ a ≠ m + 1 then 1 else 0) + rowCount a m

def pairCount (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowCount k n + pairCount n k

theorem rowCount_zero : ∀ m, rowCount 0 m = m - 1 := by
  intro m; induction m with
  | zero => rfl
  | succ m ih =>
    rw [rowCount, ih]
    by_cases h : m = 0
    · subst h; simp [rowCount]
    · rw [if_pos ⟨h, by omega⟩]; omega

/-- Below the diagonal every `j` is admissible. -/
theorem rowCount_below : ∀ a m, m < a → rowCount a m = m := by
  intro a m; induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [rowCount, ih (by omega), if_pos ⟨by omega, by omega⟩]
    omega

theorem rowCount_diag : ∀ a, 1 ≤ a → rowCount a a = a - 1 := by
  intro a ha
  cases a with
  | zero => omega
  | succ a =>
    rw [rowCount, rowCount_below (a + 1) a (by omega)]
    rw [if_neg (by omega)]
    omega

theorem rowCount_pos : ∀ m a, 1 ≤ a → a < m → rowCount a m = m - 2 := by
  intro m; induction m with
  | zero => intro a _ h; omega
  | succ m ih =>
    intro a ha hm
    by_cases heq : a = m
    · subst heq
      rw [rowCount, rowCount_diag a ha, if_neg (by omega)]
      omega
    · have hlt : a < m := by omega
      rw [rowCount, ih a ha hlt, if_pos ⟨by omega, by omega⟩]
      omega

theorem pairCount_eq : ∀ n k, k ≤ n → 1 ≤ n →
    pairCount n k = if k = 0 then 0 else (n - 1) + (k - 1) * (n - 2) := by
  intro n k; induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro hk hn
    rw [pairCount, ih (by omega) hn]
    by_cases hk0 : k = 0
    · subst hk0
      rw [rowCount_zero]
      simp
    · rw [rowCount_pos n k (by omega) (by omega), if_neg hk0, if_neg (by omega)]
      have hmul : (k - 1) * (n - 2) + (n - 2) = k * (n - 2) := by
        cases k with
        | zero => omega
        | succ k' => simp only [Nat.succ_sub_one, Nat.succ_mul]
      simp only [Nat.succ_sub_one]
      omega

/-- **The count.**  With `n` blocks there are exactly `(n-1)^2` admissible
index pairs, that is `c^2` for words of length `2c+2`. -/
theorem admissible_count : ∀ n, pairCount n n = (n - 1) * (n - 1) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    rw [pairCount_eq (n + 1) (n + 1) (Nat.le_refl _) (by omega)]
    rw [if_neg (by omega)]
    simp only [Nat.succ_sub_one]
    cases n with
    | zero => rfl
    | succ m =>
      have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by
        rw [Nat.mul_succ]
      have harg : m + 1 + 1 - 2 = m := by omega
      rw [harg]
      omega

/-- **The classification of the normal forms.**  With `n = c+1` blocks, that is
words of length `2c+2`, every reduced word with vanishing second invariant and
first invariant `c` carries one `2` in a first slot and one in a second, in
distinct non-consecutive blocks.  The number of such index pairs is `c^2`,
confirmed by the kernel for `c = 1, 2, 3` through `validCount`. -/
theorem classify_normal_forms (c : Nat) (w : List Letter)
    (hlen : w.length = 2 * c + 2) (hred : Reduced w)
    (h2 : cvec w 2 = 0) (h1 : cvec w 1 = c) :
    ∃ a j, Admissible (c + 1) a j ∧ w = markBoth (c + 1) a j := by
  have hlen' : w.length = 2 * (c + 1) := by omega
  have h1' : cvec w 1 = ((c : Int) + 1) - 1 := by omega
  exact classify_main (c + 1) w hlen' hred h1' h2

end RotationRelations

-- Rule 5 axiom audit (added 2026-08-01): declare every axiom these results rest on.
#print axioms RotationRelations.cvec_append_cases
#print axioms RotationRelations.cvec_append_even
#print axioms RotationRelations.cvec_append_odd
#print axioms RotationRelations.cvec_singleton
#print axioms RotationRelations.cvec_reverse_cases
#print axioms RotationRelations.cvec_reverse_even
#print axioms RotationRelations.reducedB_iff
#print axioms RotationRelations.validCount_one
#print axioms RotationRelations.validCount_two
#print axioms RotationRelations.validCount_three
#print axioms RotationRelations.cvec_cons2
#print axioms RotationRelations.cvec_le_half
#print axioms RotationRelations.cvec2_nonpos_of_max
#print axioms RotationRelations.Reduced_tail
#print axioms RotationRelations.letter_cases
#print axioms RotationRelations.classify_plain
#print axioms RotationRelations.cvec_sum_le
#print axioms RotationRelations.classify_evenPlaced
#print axioms RotationRelations.classify_oddPlaced
#print axioms RotationRelations.classify_main
#print axioms RotationRelations.ne01
#print axioms RotationRelations.ne02
#print axioms RotationRelations.ne12
#print axioms RotationRelations.ne10
#print axioms RotationRelations.ne21
#print axioms RotationRelations.ne20
#print axioms RotationRelations.plain_length
#print axioms RotationRelations.plain_cvec1
#print axioms RotationRelations.plain_cvec2
#print axioms RotationRelations.plain_reduced_cons
#print axioms RotationRelations.plain_reduced
#print axioms RotationRelations.markY_length
#print axioms RotationRelations.markY_cvec1
#print axioms RotationRelations.markY_cvec2
#print axioms RotationRelations.markY_reduced_cons
#print axioms RotationRelations.markX_length
#print axioms RotationRelations.markX_cvec1
#print axioms RotationRelations.markX_cvec2
#print axioms RotationRelations.markX_reduced_cons
#print axioms RotationRelations.markBoth_length
#print axioms RotationRelations.markBoth_cvec1
#print axioms RotationRelations.markBoth_cvec2
#print axioms RotationRelations.markBoth_reduced_cons
#print axioms RotationRelations.markBoth_valid
#print axioms RotationRelations.rowCount_zero
#print axioms RotationRelations.rowCount_below
#print axioms RotationRelations.rowCount_diag
#print axioms RotationRelations.rowCount_pos
#print axioms RotationRelations.pairCount_eq
#print axioms RotationRelations.admissible_count
#print axioms RotationRelations.classify_normal_forms
