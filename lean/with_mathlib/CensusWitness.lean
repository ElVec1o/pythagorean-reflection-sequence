/-
The growth of a rational witness triangle, by compiled computation.

A reflection in a line of rational direction `(p, q)` through a rational point
has the rational matrix

    1/(p²+q²) * [[p²-q², 2pq], [2pq, q²-p²]],

so for a triangle with rational vertices every element of `G_τ` is an affine map
of `ℚ²` with rational entries, and equality of two of them is decidable. No
number field is needed; that is special to the generic case, the strata of angle
`π/m` needing `ℚ(2cos(π/m))`.

Breadth-first search on the three reflections therefore computes the spheres
`u_d = #{g : ℓ(g) = d}` exactly. `census_witness` records the result to depth 12
and is proved by `native_decide`, so unlike every other file here it trusts the
compiler: its axiom list carries a generated
`census_witness._native.native_decide.ax_1_1` beside the three standard axioms.

What this establishes, and what it does not. A coincidence that holds on a dense
open set of shapes holds at every shape by continuity, so the coincidences of a
generic shape are among those of this witness. The witness therefore has at
least as many coincidences, hence at most as many distinct elements: the counts
below are a *lower* bound for the generic growth, equivalently an upper bound on
the deficit. That gives `deficit ≤ 33` at radius 11 and `≤ 132` at radius 12,
which is half of part (ii) of the census theorem. The matching bound in the
other direction is part (i), the 33 universal identities, and that is not
formalized here.
-/
import Mathlib.Data.Rat.Defs
import Std.Data.HashSet

namespace CensusWitness

/-- An affine map of `ℚ²`, `(x,y) ↦ (a x + b y + e, c x + d y + f)`. -/
structure QAff where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  e : ℚ
  f : ℚ
deriving DecidableEq, Repr

/-- Composition: `comp F G` is `F` after `G`. -/
def QAff.comp (F G : QAff) : QAff where
  a := F.a * G.a + F.b * G.c
  b := F.a * G.b + F.b * G.d
  c := F.c * G.a + F.d * G.c
  d := F.c * G.b + F.d * G.d
  e := F.a * G.e + F.b * G.f + F.e
  f := F.c * G.e + F.d * G.f + F.f

def QAff.id : QAff := ⟨1, 0, 0, 1, 0, 0⟩

/-- A hashable key, so that the search can deduplicate. -/
def QAff.key (F : QAff) : List Int :=
  [F.a.num, F.a.den, F.b.num, F.b.den, F.c.num, F.c.den,
   F.d.num, F.d.den, F.e.num, F.e.den, F.f.num, F.f.den]

/-- The reflection in the line through `(px, py)` of direction `(p, q)`. -/
def mkRefl (p q px py : ℚ) : QAff :=
  let n := p * p + q * q
  let a := (p * p - q * q) / n
  let b := 2 * p * q / n
  { a := a, b := b, c := b, d := -a,
    e := px - (a * px + b * py),
    f := py - (b * px - a * py) }

/-! ### The witness triangle

Vertices `A = (0,0)`, `B = (1,0)`, `C = (1/3, 5/7)`; the three sides are `AB`,
`AC` and `BC`. -/

def cx : ℚ := 1 / 3
def cy : ℚ := 5 / 7

def r0 : QAff := mkRefl 1 0 0 0
def r1 : QAff := mkRefl cx cy 0 0
def r2 : QAff := mkRefl (cx - 1) cy 1 0

def gens : List QAff := [r0, r1, r2]

/-- Each generator is an involution, and none is the identity. -/
theorem gens_involutive :
    (r0.comp r0 = QAff.id) ∧ (r1.comp r1 = QAff.id) ∧ (r2.comp r2 = QAff.id) := by
  native_decide

theorem gens_ne_id : r0 ≠ QAff.id ∧ r1 ≠ QAff.id ∧ r2 ≠ QAff.id := by
  native_decide

/-! ### Breadth-first search -/

/-- Remove duplicates from a level, and record them as seen. -/
def absorb (seen : Std.HashSet (List Int)) :
    List QAff → Std.HashSet (List Int) × List QAff
  | [] => (seen, [])
  | g :: gs =>
      let k := g.key
      if seen.contains k then absorb seen gs
      else
        let (s, rest) := absorb (seen.insert k) gs
        (s, g :: rest)

/-- The sizes of the spheres of radius `1, 2, …, n`. -/
def levels (n : Nat) (seen : Std.HashSet (List Int)) (frontier : List QAff) :
    List Nat :=
  match n with
  | 0 => []
  | n + 1 =>
      let raw := frontier.flatMap fun g => gens.map fun s => s.comp g
      let (seen', next) := absorb seen raw
      next.length :: levels n seen' next

/-- The growth sequence of the witness, from radius `0`. -/
def sphere (n : Nat) : List Nat :=
  1 :: levels n (Std.HashSet.emptyWithCapacity.insert QAff.id.key) [QAff.id]

/-! ### The colliding pairs -/

/-- Reduced words of length `n`, as letter lists. -/
def rwords : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (rwords n).flatMap fun w =>
      (List.range 3).filterMap fun l =>
        match w with
        | [] => some (l :: w)
        | x :: _ => if x == l then none else some (l :: w)

/-- The map represented by a word. -/
def evalW (w : List Nat) : QAff :=
  w.foldr (fun l acc => (gens.getD l QAff.id).comp acc) QAff.id

/-- The words of length `n` grouped by image, keeping the classes of size > 1. -/
def collisions (n : Nat) : List (List (List Nat)) :=
  let tbl : Std.HashMap (List Int) (List (List Nat)) :=
    (rwords n).foldl (fun m w =>
      let k := (evalW w).key
      m.insert k (w :: m.getD k [])) ∅
  (tbl.toList.map (fun p => p.2)).filter (fun c => c.length > 1)

/-- At radius 11 there are `3·2^10` reduced words. -/
theorem rwords_eleven : (rwords 11).length = 3072 := by native_decide

/-- They collide in exactly 33 classes, each a pair: the 33 of the census
theorem. That the classes are pairs and not larger is what makes the deficit
equal to the number of classes. -/
theorem collisions_eleven :
    (collisions 11).length = 33 ∧ (collisions 11).all (fun c => c.length == 2) := by
  native_decide

/-! ### The result -/

/-- **The growth of the witness, to radius 12.** Compare the census theorem:
the sequence is free, `3·2^{d-1}`, up to radius 10, first deviates at radius 11,
and the two deviations are the `33` and the `132` of the paper. -/
theorem census_witness :
    sphere 12 = [1, 3, 6, 12, 24, 48, 96, 192, 384, 768, 1536, 3039, 6012] := by
  native_decide

/-- Free growth below the first deviation. -/
theorem free_below_eleven :
    ∀ d, d ≤ 10 → (sphere 12).getD d 0 = if d = 0 then 1 else 3 * 2 ^ (d - 1) := by
  rw [census_witness]
  decide

/-- The first deviation, at radius 11, has deficit 33. -/
theorem deficit_eleven : 3 * 2 ^ 10 - (sphere 12).getD 11 0 = 33 := by
  rw [census_witness]
  decide

/-- At radius 12 the deficit is 132. -/
theorem deficit_twelve : 3 * 2 ^ 11 - (sphere 12).getD 12 0 = 132 := by
  rw [census_witness]
  decide

end CensusWitness
