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

(1) and (2) are proved here, and (3) is verified by kernel computation for
`c = 1, 2, 3`, where the counts come out `1, 4, 9`.  The general form of (3)
is stated as `count_normal_forms` and left open, as is the free-product
argument identifying the unique word of finite order in `W_m = D_m * C_2`:
the latter needs the torsion theorem for free products, which Mathlib does not
carry either.

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

/-- The normal forms of the theorem: every odd position carries the letter `1`
except position `2a+1`, which carries `2`, and every even position carries `0`
except position `2b`, which carries `2`. -/
def normalForm (c a b : Nat) : List Letter :=
  (List.range (2 * c + 2)).map (fun k =>
    if k = 2 * a then 2
    else if k = 2 * b - 1 then 2
    else if k % 2 = 0 then 1 else 0)

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

-- `c = 4` and beyond exhaust the kernel's stack; the general statement is
-- `count_normal_forms` below, still open.

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

/-- **The count.**  For `1 ≤ c`, the reduced words of length `2c+2` with
`c_2 = 0` and `c_1 = c` are exactly the `normalForm c a b` with `0 ≤ a ≤ c`,
`1 ≤ b ≤ c+1` and `b ∉ {a, a+1}`, so there are `c^2` of them.  Not proved. -/
theorem count_normal_forms (c : Nat) (hc : 1 ≤ c) :
    ∃ S : List (Nat × Nat),
      S.length = c * c ∧
      (∀ p ∈ S, p.1 ≤ c ∧ 1 ≤ p.2 ∧ p.2 ≤ c + 1 ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1 + 1) ∧
      (∀ w : List Letter, w.length = 2 * c + 2 → Reduced w →
        cvec w 2 = 0 → cvec w 1 = c →
        ∃ p ∈ S, w = normalForm c p.1 p.2) := by
  sorry

end RotationRelations
