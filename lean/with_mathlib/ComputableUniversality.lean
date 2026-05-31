/-
  ComputableUniversality.lean
  ===========================

  A fully computable symbolic universality check at depth 10.

  We implement our own computable bivariate polynomial type CPoly
  (no MvPolynomial dependence) so that `native_decide` can evaluate
  symbolic affine isometries and count distinct values across all
  233 canonical length-10 Coxeter words.

  Target theorem: there are EXACTLY 225 distinct symbolic affine
  isometries among the canonical length-10 Coxeter words.  This
  proves the depth-10 piece of the universality theorem (no specific
  triangle can produce more than 225 distinct affine images at
  word-length 10).
-/

import SymbolicUniversality

namespace ComputableUniversality

/-! ## Computable bivariate polynomial over ℚ -/

/-- A bivariate polynomial in (a, b) over ℚ, represented as a list
    of `((degA, degB), coeff)` tuples.  Normal form: sorted by
    `(degA, degB)` lexicographically, no duplicate monomials, no zero
    coefficients. -/
structure CPoly where
  terms : List ((Nat × Nat) × Rat)
deriving DecidableEq, Repr

namespace CPoly

def zero : CPoly := ⟨[]⟩
def one : CPoly := ⟨[((0, 0), 1)]⟩

/-- The indeterminate `a`. -/
def aV : CPoly := ⟨[((1, 0), 1)]⟩

/-- The indeterminate `b`. -/
def bV : CPoly := ⟨[((0, 1), 1)]⟩

/-- Lexicographic comparison of `(Nat × Nat)`. -/
def lexLt (p q : Nat × Nat) : Bool :=
  p.1 < q.1 ∨ (p.1 == q.1 ∧ p.2 < q.2)

/-- Insert a single term `(deg, c)` into a sorted, normalized term list. -/
def insertTerm : ((Nat × Nat) × Rat) → List ((Nat × Nat) × Rat) → List ((Nat × Nat) × Rat)
  | (d, c), [] => if c == 0 then [] else [(d, c)]
  | (d, c), (d', c') :: rest =>
      if d = d' then
        let c'' := c + c'
        if c'' == 0 then rest
        else (d, c'') :: rest
      else if lexLt d d' then
        if c == 0 then (d', c') :: rest
        else (d, c) :: (d', c') :: rest
      else
        (d', c') :: insertTerm (d, c) rest

/-- Normalize a list of terms by sorting and merging. -/
def normalize (ts : List ((Nat × Nat) × Rat)) : List ((Nat × Nat) × Rat) :=
  ts.foldr insertTerm []

/-- Polynomial addition. -/
def add (p q : CPoly) : CPoly := ⟨normalize (p.terms ++ q.terms)⟩

/-- Polynomial scalar negation. -/
def neg (p : CPoly) : CPoly :=
  ⟨p.terms.map fun (d, c) => (d, -c)⟩

/-- Polynomial subtraction. -/
def sub (p q : CPoly) : CPoly := add p (neg q)

/-- Polynomial multiplication. -/
def mul (p q : CPoly) : CPoly :=
  let allProducts : List ((Nat × Nat) × Rat) := p.terms.flatMap fun (dp, cp) =>
    q.terms.map fun (dq, cq) =>
      ((dp.1 + dq.1, dp.2 + dq.2), cp * cq)
  ⟨normalize allProducts⟩

instance : Add CPoly := ⟨add⟩
instance : Mul CPoly := ⟨mul⟩
instance : Sub CPoly := ⟨sub⟩
instance : Neg CPoly := ⟨neg⟩
instance : Zero CPoly := ⟨zero⟩
instance : One CPoly := ⟨one⟩

/-- Construct a constant polynomial from a `Rat`. -/
def const (c : Rat) : CPoly := if c == 0 then zero else ⟨[((0, 0), c)]⟩

end CPoly

/-! ## Computable affine isometries over Q[a, b] / (common denominator)

  We track an `Aff` as 6 numerator polynomials plus a denominator
  polynomial.  Composition multiplies denominators. -/

structure CAff where
  p : CPoly
  q : CPoly
  r : CPoly
  s : CPoly
  tx : CPoly
  ty : CPoly
  d : CPoly
deriving DecidableEq, Repr

namespace CAff

def one : CAff :=
  { p := CPoly.one, q := CPoly.zero, r := CPoly.zero, s := CPoly.one
    tx := CPoly.zero, ty := CPoly.zero, d := CPoly.one }

def comp (M N : CAff) : CAff :=
  { p  := M.p * N.p + M.q * N.r
    q  := M.p * N.q + M.q * N.s
    r  := M.r * N.p + M.s * N.r
    s  := M.r * N.q + M.s * N.s
    tx := M.p * N.tx + M.q * N.ty + M.tx * N.d
    ty := M.r * N.tx + M.s * N.ty + M.ty * N.d
    d  := M.d * N.d }

end CAff

/-! ## The three reflections for an arbitrary right triangle with legs (a, b) -/

/-- D = a² + b² -/
def D : CPoly := CPoly.aV * CPoly.aV + CPoly.bV * CPoly.bV

def R0 : CAff :=
  { p := CPoly.one, q := CPoly.zero, r := CPoly.zero, s := -CPoly.one
    tx := CPoly.zero, ty := CPoly.zero, d := CPoly.one }

def R1 : CAff :=
  { p := -CPoly.one, q := CPoly.zero, r := CPoly.zero, s := CPoly.one
    tx := CPoly.const 2 * CPoly.aV, ty := CPoly.zero, d := CPoly.one }

def R2 : CAff :=
  { p := CPoly.aV * CPoly.aV - CPoly.bV * CPoly.bV
    q := CPoly.const 2 * CPoly.aV * CPoly.bV
    r := CPoly.const 2 * CPoly.aV * CPoly.bV
    s := CPoly.bV * CPoly.bV - CPoly.aV * CPoly.aV
    tx := CPoly.zero, ty := CPoly.zero
    d := D }

def applyWord : List Nat → CAff
  | []      => CAff.one
  | i :: is =>
      let g := match i with
        | 0 => R0
        | 1 => R1
        | _ => R2
      CAff.comp g (applyWord is)

/-! ## Universality at depth 10 -/

open SymbolicUniversality

/-- Symbolic affine images of all 233 canonical length-10 Coxeter
    words, as computable polynomial Affs. -/
def imagesAtDepth10 : List CAff :=
  (canonicalWords 10).map applyWord

/-- There are 233 canonical length-10 Coxeter words. -/
example : imagesAtDepth10.length = 233 := by native_decide

/-- Number of distinct symbolic affine images at depth 10. -/
def distinctCountAtDepth10 : Nat := imagesAtDepth10.eraseDup.length

/-- **Universality at depth 10.**

    Among the 233 canonical reduced Coxeter words of length 10 in
    the abstract group W = ⟨R_0, R_1, R_2 | R_i² = 1, (R_0 R_1)² = 1⟩,
    there are exactly 225 distinct symbolic affine isometries over
    ℚ[a, b].

    Since structural equality of polynomial Affs implies equality of
    affine isometries for *every* specific rational pair (a, b), this
    proves that the BFS layer count at depth 10 is at most 225 for
    every right triangle with unequal legs.  Combined with the eight
    explicit relations of Table 1 (each proven symbolically in
    `SymbolicVerification.lean`), this gives exactly 225 distinct
    affine isometries — independently of the triangle.

    Hence:  a(10) = 225 universally.  -/
theorem universality_at_depth_10 : distinctCountAtDepth10 = 225 := by
  native_decide

end ComputableUniversality
