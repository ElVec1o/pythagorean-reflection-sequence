/-
The stratum translation census, generically on the stratum.

On the stratum `α = π/m` two of the three sides meet at angle `π/m`, so with
`A = 0`, `B = 1` and `ω = e^{iπ/m}` the first two reflections are
`z ↦ conj z` and `z ↦ ω² conj z`. The direction of the third side is the free
parameter of the stratum, so it enters as an indeterminate `V` on the unit
circle: `z ↦ V conj z + (1 - V)`, with `conj V = V⁻¹`.

Everything therefore lives in the Laurent ring `ℤ[ω][V, V⁻¹]`, where `ω` is a
primitive `2m`-th root of unity, represented as `ℤ[x]/(Φ_{2m})`. Two words are
equal for a generic shape of the stratum exactly when they are equal in this
ring, a nonzero Laurent polynomial having finitely many roots -- so the counts
below are the generic ones, not a witness's. No inverses are ever needed, since
the linear coefficients are Laurent monomials, so the arithmetic stays in `ℤ`.

A translation is an element with trivial linear coefficient and no reflection.
`census_*` record the number of translations of each even length up to 18,
which is the table of the stratum translation census. Proved by `native_decide`.
-/
import Std.Data.HashMap
import Std.Data.HashSet

namespace CylCensus

/-! ## `Z[ω]`, `ω` a primitive `2m`-th root of unity

Coefficient lists of length `d = deg Φ_{2m}`; `red` encodes `ω^d = Σ red[i] ω^i`. -/

abbrev Cyc := List Int

def cycZero (d : Nat) : Cyc := List.replicate d 0
def cycOne (d : Nat) : Cyc := 1 :: List.replicate (d - 1) 0
def cycAdd (p q : Cyc) : Cyc := (p.zip q).map fun x => x.1 + x.2
def cycSMul (n : Int) (p : Cyc) : Cyc := p.map fun x => n * x

/-- Multiply by `ω`: shift, then fold the overflow back with `red`. -/
def shiftC (d : Nat) (red : Cyc) (p : Cyc) : Cyc :=
  cycAdd (0 :: p.take (d - 1)) (cycSMul (p.getD (d - 1) 0) red)

/-- `ω^0, ω^1, …, ω^(n-1)`. -/
def powTable (d : Nat) (red : Cyc) : Nat → List Cyc
  | 0 => []
  | 1 => [cycOne d]
  | n + 1 =>
      let t := powTable d red n
      t ++ [shiftC d red (t.getD (n - 1) (cycOne d))]

structure Cfg where
  d : Nat
  twoM : Nat
  red : Cyc
  tbl : List Cyc

def mkCfg (twoM d : Nat) (red : Cyc) : Cfg :=
  ⟨d, twoM, red, powTable d red (2 * d + twoM + 2)⟩

def cycMul (C : Cfg) (p q : Cyc) : Cyc :=
  (List.range (2 * C.d - 1)).foldl (fun acc k =>
    let c := ((List.range (k + 1)).map fun i =>
      p.getD i 0 * q.getD (k - i) 0).foldl (· + ·) 0
    if c == 0 then acc else cycAdd acc (cycSMul c (C.tbl.getD k (cycZero C.d)))) (cycZero C.d)

/-- Conjugation `ω ↦ ω⁻¹`. -/
def cycConj (C : Cfg) (p : Cyc) : Cyc :=
  (List.range C.d).foldl (fun acc k =>
    let c := p.getD k 0
    if c == 0 then acc
    else cycAdd acc (cycSMul c (C.tbl.getD ((C.twoM - k) % C.twoM) (cycZero C.d))))
    (cycZero C.d)

/-! ## Laurent polynomials in a free unit `V` over `Z[ω]`

The third side's direction is a free parameter of the stratum, so `V` is an
indeterminate on the unit circle: `conj V = V⁻¹`. Sorted by exponent, no zero
coefficients, so equality is structural. -/

abbrev Lau := List (Int × Cyc)

def lauNorm (C : Cfg) (l : Lau) : Lau :=
  let m : Std.HashMap Int Cyc :=
    l.foldl (fun m p => m.insert p.1 (cycAdd p.2 (m.getD p.1 (cycZero C.d)))) ∅
  (m.toList.filter fun p => p.2.any (· != 0)).mergeSort fun x y => x.1 ≤ y.1

def lauAdd (C : Cfg) (p q : Lau) : Lau := lauNorm C (p ++ q)
def lauMul (C : Cfg) (p q : Lau) : Lau :=
  lauNorm C (p.flatMap fun a => q.map fun b => (a.1 + b.1, cycMul C a.2 b.2))
def lauConj (C : Cfg) (p : Lau) : Lau :=
  lauNorm C (p.map fun a => (-a.1, cycConj C a.2))
def lauC (C : Cfg) (c : Cyc) : Lau := if c.any (· != 0) then [(0, c)] else []
def lauOne (C : Cfg) : Lau := lauC C (cycOne C.d)
def lauNeg (p : Lau) : Lau := p.map fun a => (a.1, cycSMul (-1) a.2)

/-! ## Isometries `z ↦ a z + b` or `z ↦ a conj z + b` -/

structure El where
  a : Lau
  b : Lau
  flip : Bool
deriving BEq, Hashable

def elId (C : Cfg) : El := ⟨lauOne C, [], false⟩

def cjL (C : Cfg) (s : Bool) (p : Lau) : Lau := if s then lauConj C p else p

/-- `comp F G` is `F` after `G`. -/
def comp (C : Cfg) (F G : El) : El :=
  { a := lauMul C F.a (cjL C F.flip G.a)
    b := lauAdd C (lauMul C F.a (cjL C F.flip G.b)) F.b
    flip := xor F.flip G.flip }

/-- The three reflections. `A = 0` with the first two sides through it at angle
`π/m`, and the third side through `B = 1` with free direction. -/
def gensOf (C : Cfg) : List El :=
  let w2 : Lau := lauC C (C.tbl.getD 2 (cycZero C.d))     -- ω²
  let V : Lau := [(1, cycOne C.d)]
  [ ⟨lauOne C, [], true⟩,                                  -- side AB
    ⟨w2, [], true⟩,                                        -- side AC
    ⟨V, lauAdd C (lauOne C) (lauNeg V), true⟩ ]            -- side BC through 1

/-- Breadth-first search; returns, for each radius, the number of new elements
and the number of those that are translations. -/
def levels (C : Cfg) (gs : List El) :
    Nat → Std.HashSet El → List El → List (Nat × Nat)
  | 0, _, _ => []
  | n + 1, seen, frontier =>
      let raw := frontier.flatMap fun g => gs.map fun s => comp C s g
      let (seen', next) :=
        raw.foldl (fun (acc : Std.HashSet El × List El) g =>
          if acc.1.contains g then acc else (acc.1.insert g, g :: acc.2)) (seen, [])
      let trans := next.filter fun g => !g.flip && g.a == lauOne C
      (next.length, trans.length) :: levels C gs n seen' next

def run (C : Cfg) (n : Nat) : List (Nat × Nat) :=
  let gs := gensOf C
  levels C gs n (Std.HashSet.emptyWithCapacity.insert (elId C)) [elId C]

/-! ## Configurations -/

def c3 : Cfg := mkCfg 6 2 [-1, 1]                       -- Φ₆  = x²-x+1
def c4 : Cfg := mkCfg 8 4 [-1, 0, 0, 0]                 -- Φ₈  = x⁴+1
def c5 : Cfg := mkCfg 10 4 [-1, 1, -1, 1]               -- Φ₁₀ = x⁴-x³+x²-x+1
def c6 : Cfg := mkCfg 12 4 [-1, 0, 1, 0]                -- Φ₁₂ = x⁴-x²+1
def c7 : Cfg := mkCfg 14 6 [-1, 1, -1, 1, -1, 1]        -- Φ₁₄
def c9 : Cfg := mkCfg 18 6 [-1, 0, 0, 1, 0, 0]          -- Φ₁₈ = x⁶-x³+1

-- sanity: ω^(2m) = 1 and ω^m = -1
#eval c3.tbl.getD 6 []
#eval c3.tbl.getD 3 []
#eval c5.tbl.getD 10 []
#eval c5.tbl.getD 5 []
-- the reflections must be involutions
#eval ((gensOf c5).map fun g => comp c5 g g == elId c5)
def rw : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (rw n).flatMap fun w => (List.range 3).filterMap fun l =>
      match w with | [] => some (l::w) | x::_ => if x == l then none else some (l::w)

def ev (C : Cfg) (w : List Nat) : El :=
  w.foldr (fun l acc => comp C ((gensOf C).getD l (elId C)) acc) (elId C)

/-- Translation counts at even lengths `2, 4, …, 2n`. -/
def transRow (C : Cfg) (n : Nat) : List Nat :=
  ((run C n).zipIdx.filter fun p => (p.2 + 1) % 2 == 0).map fun p => p.1.2

/-- The reflections are involutions, at every shape of every stratum. -/
theorem gens_involutive :
    [c3, c4, c5, c6, c7, c9].all (fun C => (gensOf C).all fun g => comp C g g == elId C) := by
  native_decide

/-- `ω^{2m} = 1` and `ω^m = -1`, so `ω` really is a primitive `2m`-th root. -/
theorem omega_order :
    [c3, c4, c5, c6, c7, c9].all
      (fun C => C.tbl.getD C.twoM [] == cycOne C.d &&
        C.tbl.getD (C.twoM / 2) [] == cycSMul (-1) (cycOne C.d)) := by
  native_decide


/-! ### The census

The number of translations of each even length up to 18, generically on each
stratum. These are the rows of the stratum translation census. Each is a
breadth-first search to depth 18 in `ℤ[ω][V, V⁻¹]`, so the file is slow to
check; the timings on one laptop are given with each row.
-/

/-- Stratum `α = π/3` (about 2 min). -/
theorem census_m3 : transRow c3 18 = [0, 0, 6, 8, 38, 76, 224, 630, 1456] := by
  native_decide

/-- Stratum `α = π/4` (about 4 min). -/
theorem census_m4 : transRow c4 18 = [0, 0, 6, 4, 34, 62, 198, 480, 1394] := by
  native_decide

/-- Stratum `α = π/5` (about 8 min). -/
theorem census_m5 : transRow c5 18 = [0, 0, 6, 6, 42, 104, 448, 1274, 4612] := by
  native_decide

/-- Stratum `α = π/6` (about 6 min). -/
theorem census_m6 : transRow c6 18 = [0, 0, 6, 6, 40, 78, 278, 750, 2342] := by
  native_decide

/-- Stratum `α = π/7` (about 13 min). -/
theorem census_m7 : transRow c7 18 = [0, 0, 6, 6, 42, 96, 350, 1110, 4204] := by
  native_decide

/-- Stratum `α = π/9` (about 9 min). -/
theorem census_m9 : transRow c9 18 = [0, 0, 6, 6, 42, 96, 350, 1092, 3684] := by
  native_decide

end CylCensus