/-
The 33 identities of the census theorem, valid at every triangle.

`CensusWitness.lean` finds, at one rational shape, the 33 pairs of reduced words
of length 11 that collide. Whether those identities hold at *every* triangle
cannot be seen at a single shape, so here the same words are evaluated
symbolically: the third vertex is left as a pair of indeterminates `(X, Y)` and
the reflections become affine maps whose entries are polynomials in `ℤ[X, Y]`,
carried with a common polynomial denominator.

Two such maps are equal as maps exactly when their numerators agree after
cross-multiplying by the denominators, which is an identity in `ℤ[X, Y]` and so
is decidable. `universal_identities` checks it for all 33 pairs at once, and
therefore proves part (i) of the census theorem: the identities hold for every
nondegenerate triangle, not merely for the witness.

Like `CensusWitness.lean`, this file is proved by `native_decide` and so trusts
the compiler.
-/
import Mathlib.Data.Rat.Defs
import Std.Data.HashMap
import CensusWitness

namespace CensusUniversal

open CensusWitness

/-! ### Polynomials in two variables over `ℤ`

Sparse, kept in a canonical form: sorted by exponent pair, no zero coefficients.
That makes `BEq` decide equality. -/

abbrev Mono := Nat × Nat

/-- Lexicographic order on exponent pairs. -/
def monoLe (a b : Mono) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

abbrev P := List (Mono × Int)

/-- Collect equal monomials, drop zeros, sort. -/
def Pnorm (l : List (Mono × Int)) : P :=
  let m : Std.HashMap Mono Int :=
    l.foldl (fun m p => m.insert p.1 (p.2 + m.getD p.1 0)) ∅
  (m.toList.filter (fun p => p.2 != 0)).mergeSort (fun x y => monoLe x.1 y.1)

def PC (n : Int) : P := if n == 0 then [] else [((0, 0), n)]
def PX : P := [((1, 0), 1)]
def PY : P := [((0, 1), 1)]

def Padd (p q : P) : P := Pnorm (p ++ q)
def Pneg (p : P) : P := p.map fun a => (a.1, -a.2)
def Psub (p q : P) : P := Padd p (Pneg q)
def Pmul (p q : P) : P :=
  Pnorm (p.flatMap fun a => q.map fun b => ((a.1.1 + b.1.1, a.1.2 + b.1.2), a.2 * b.2))

/-! ### Affine maps with polynomial entries

`PAff` denotes the map `(x, y) ↦ (1/den) ((a x + b y + e), (c x + d y + f))`. -/

structure PAff where
  a : P
  b : P
  c : P
  d : P
  e : P
  f : P
  den : P

def PAff.id : PAff := ⟨PC 1, PC 0, PC 0, PC 1, PC 0, PC 0, PC 1⟩

/-- Composition: `comp F G` is `F` after `G`. Denominators multiply, and the
translation of `G` is carried through the linear part of `F`. -/
def PAff.comp (F G : PAff) : PAff where
  a := Padd (Pmul F.a G.a) (Pmul F.b G.c)
  b := Padd (Pmul F.a G.b) (Pmul F.b G.d)
  c := Padd (Pmul F.c G.a) (Pmul F.d G.c)
  d := Padd (Pmul F.c G.b) (Pmul F.d G.d)
  e := Padd (Padd (Pmul F.a G.e) (Pmul F.b G.f)) (Pmul G.den F.e)
  f := Padd (Padd (Pmul F.c G.e) (Pmul F.d G.f)) (Pmul G.den F.f)
  den := Pmul F.den G.den

/-- Equality of the maps: cross-multiply by the denominators. -/
def PAff.eqv (F G : PAff) : Bool :=
  (Pmul F.a G.den == Pmul G.a F.den) &&
  (Pmul F.b G.den == Pmul G.b F.den) &&
  (Pmul F.c G.den == Pmul G.c F.den) &&
  (Pmul F.d G.den == Pmul G.d F.den) &&
  (Pmul F.e G.den == Pmul G.e F.den) &&
  (Pmul F.f G.den == Pmul G.f F.den)

/-! ### The symbolic triangle

Vertices `A = (0,0)`, `B = (1,0)`, `C = (X, Y)` with `X`, `Y` indeterminate.
The reflection in the line through `p` of direction `(u, v)` has scaled matrix
`[[u²-v², 2uv], [2uv, v²-u²]]` over `u²+v²`, and scaled translation
`den · p - M p`. -/

def XX : P := Pmul PX PX
def YY : P := Pmul PY PY
def XY2 : P := Pmul (PC 2) (Pmul PX PY)

/-- Side `AB`: direction `(1,0)` through the origin. -/
def sr0 : PAff := ⟨PC 1, PC 0, PC 0, PC (-1), PC 0, PC 0, PC 1⟩

/-- Side `AC`: direction `(X, Y)` through the origin. -/
def sr1 : PAff :=
  ⟨Psub XX YY, XY2, XY2, Psub YY XX, PC 0, PC 0, Padd XX YY⟩

/-- Side `BC`: direction `(X-1, Y)` through `(1,0)`. -/
def W : P := Psub PX (PC 1)
def WW : P := Pmul W W
def WY2 : P := Pmul (PC 2) (Pmul W PY)

def sr2 : PAff :=
  ⟨Psub WW YY, WY2, WY2, Psub YY WW, Psub (Padd WW YY) (Psub WW YY), Pneg WY2,
    Padd WW YY⟩

def symGens : List PAff := [sr0, sr1, sr2]

/-- The map represented by a word, symbolically. -/
def symEval (w : List Nat) : PAff :=
  w.foldr (fun l acc => (symGens.getD l PAff.id).comp acc) PAff.id

/-! ### Checks -/

/-- Each symbolic reflection is an involution, at every shape. -/
theorem sym_involutive :
    (sr0.comp sr0).eqv PAff.id ∧ (sr1.comp sr1).eqv PAff.id ∧
      (sr2.comp sr2).eqv PAff.id := by
  native_decide

/-- The three reflections are pairwise distinct as symbolic maps, so the
triangle is not degenerate for a generic shape. -/
theorem sym_distinct :
    !(sr0.eqv sr1) ∧ !(sr0.eqv sr2) ∧ !(sr1.eqv sr2) := by
  native_decide

/-- A control: two reduced words that do not collide at the witness are not
identified symbolically either, so the check below is not vacuous. -/
theorem sym_control :
    !((symEval [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]).eqv
      (symEval [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1])) := by
  native_decide

/-- **Part (i) of the census theorem.** Every one of the 33 pairs found at the
witness is an identity in `ℤ[X, Y]`, hence holds at every triangle. -/
theorem universal_identities :
    (collisions 11).all (fun c => (symEval (c.getD 0 [])).eqv (symEval (c.getD 1 []))) := by
  native_decide

end CensusUniversal
