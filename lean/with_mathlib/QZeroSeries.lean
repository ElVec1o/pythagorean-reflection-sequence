/-
  QZeroSeries.lean
  ================
  A machine-checked certificate for the zero series of the Hahn-Exton q-cosine and q-sine:
  `thm:integrality`, `cor:hexagonal`, `prop:sinelattice` and `prop:stablelaw` of
  `paper/journal/hahn_exton_qcosine.tex`, at finite order.

  Scope, stated exactly.  The general theorems quantify over all `k` and all orders and rest on a
  Hensel step in `Z[[q]]` that is not available in Mathlib (see the note's machine-verification
  section).  What is checked here is the finite-order content: the truncated Newton recursion is
  run ENTIRELY IN `Z` (no denominators are ever introduced), and the resulting series is verified
  to annihilate the defining equation to the truncation order.  That is a proof of integrality
  and of the stated onsets for the `k` and the order covered, and it is the statement the note's
  external scripts were previously the only evidence for.

  All arithmetic is truncated power series over `Z`, stored as `Array Int` of length `prec`.
-/

import Mathlib.Tactic.NormNum

namespace QZeroSeries

/-- Truncation order. -/
def prec : Nat := 80

abbrev TS := Array Int

def coeff (x : TS) (i : Nat) : Int := x.getD i 0

def mk (f : Nat → Int) : TS := Array.ofFn (n := prec) fun i : Fin prec => f i.val

def tsZero : TS := mk fun _ => 0
def tsOne : TS := mk fun i => if i = 0 then 1 else 0

def tsAdd (x y : TS) : TS := mk fun i => coeff x i + coeff y i
def tsSub (x y : TS) : TS := mk fun i => coeff x i - coeff y i
def tsSmul (c : Int) (x : TS) : TS := mk fun i => c * coeff x i

def tsMul (x y : TS) : TS :=
  mk fun n => (List.range (n + 1)).foldl (fun acc i => acc + coeff x i * coeff y (n - i)) 0

/-- Multiplication by `q^k`. -/
def tsShift (k : Nat) (x : TS) : TS := mk fun i => if i < k then 0 else coeff x (i - k)

/-- Inverse of a series whose constant term is `1` or `-1`, computed entirely in `Z`. -/
def tsInv (x : TS) : TS := Id.run do
  let c0 := coeff x 0
  let mut y : Array Int := Array.replicate prec 0
  y := y.set! 0 c0
  for n in [1:prec] do
    let mut s : Int := 0
    for i in [1:n+1] do
      s := s + coeff x i * y.getD (n - i) 0
    y := y.set! n (-(c0 * s))
  return y

def tsPow (x : TS) : Nat → TS
  | 0 => tsOne
  | n + 1 => tsMul (tsPow x n) x

/-- `(q;q)_m = prod_{i=1}^{m} (1 - q^i)`. -/
def poch (m : Nat) : TS :=
  (List.range m).foldl (fun acc i => tsMul acc (tsSub tsOne (tsShift (i + 1) tsOne))) tsOne

/-- `(q^2;q)_m = prod_{i=2}^{m+1} (1 - q^i)`, the sine-side Pochhammer. -/
def poch2 (m : Nat) : TS :=
  (List.range m).foldl (fun acc i => tsMul acc (tsSub tsOne (tsShift (i + 2) tsOne))) tsOne

/-- `prod_{i=1}^{m} (1 - q^{2i})`. -/
def pochEven (m : Nat) : TS :=
  (List.range m).foldl (fun acc i => tsMul acc (tsSub tsOne (tsShift (2 * (i + 1)) tsOne))) tsOne

/-- The Newton exponent `(k'-k)(k'-k+1)`, as a natural number. -/
def expo (k k' : Nat) : Nat :=
  if k ≤ k' then (k' - k) * (k' - k + 1) else (k - k') * (k - k' - 1)

/-- Cosine-side coefficient of `u^{k'}` in `F_k`:
    `(-1)^{k'} q^{(k'-k)(k'-k+1)} / (q;q)_{2k'}`. -/
def cCos (k k' : Nat) : TS :=
  let sgn : Int := if k' % 2 = 0 then 1 else -1
  tsSmul sgn (tsShift (expo k k') (tsInv (poch (2 * k'))))

/-- Sine-side coefficient of `v^{k'}`: `(-1)^{k'} q^{(k'-k)(k'-k+1)} / (q^2;q)_{2k'}`. -/
def cSin (k k' : Nat) : TS :=
  let sgn : Int := if k' % 2 = 0 then 1 else -1
  tsSmul sgn (tsShift (expo k k') (tsInv (poch2 (2 * k'))))

/-- Index cut-off: beyond `k + 10` the exponent exceeds `prec`, so the coefficient truncates
    to zero. -/
def kmax (k : Nat) : Nat := k + 10

def Fval (c : Nat → Nat → TS) (k : Nat) (u : TS) : TS :=
  (List.range (kmax k + 1)).foldl (fun acc k' => tsAdd acc (tsMul (c k k') (tsPow u k'))) tsZero

def Fderiv (c : Nat → Nat → TS) (k : Nat) (u : TS) : TS :=
  (List.range (kmax k + 1)).foldl
    (fun acc k' =>
      match k' with
      | 0 => acc
      | j + 1 => tsAdd acc (tsSmul (Int.ofNat (j + 1)) (tsMul (c k (j + 1)) (tsPow u j)))) tsZero

def newtonStep (c : Nat → Nat → TS) (k : Nat) (u : TS) : TS :=
  tsSub u (tsMul (Fval c k u) (tsInv (Fderiv c k u)))

def iter (c : Nat → Nat → TS) (k : Nat) : Nat → TS
  | 0 => tsOne
  | n + 1 => newtonStep c k (iter c k n)

/-- The rescaled cosine-side zero `u_k`. -/
def uSeries (k : Nat) : TS := iter cCos k 8

/-- The rescaled sine-side zero `v_k`. -/
def vSeries (k : Nat) : TS := iter cSin k 8

def uList (k : Nat) : List Int := (uSeries k).toList
def vList (k : Nat) : List Int := (vSeries k).toList

/-- The deviation `1 - u_k`. -/
def devU (k : Nat) : List Int := (tsSub tsOne (uSeries k)).toList
def devV (k : Nat) : List Int := (tsSub tsOne (vSeries k)).toList

/-- Index and value of the first nonzero coefficient. -/
def firstNz : List Int → Nat × Int
  | [] => (0, 0)
  | x :: xs => if x = 0 then (let p := firstNz xs; (p.1 + 1, p.2)) else (0, x)

/-- `1/(q^2;q^2)_inf^2`, the two-coloured partition generating function. -/
def twoColoured : TS := tsInv (tsMul (pochEven 40) (pochEven 40))

/-- Length of the longest common prefix. -/
def commonPrefix : List Int → List Int → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x = y then commonPrefix xs ys + 1 else 0

/-- Agreement depth between the rescaled deviation and the two-coloured series. -/
def depthU (k : Nat) : Nat := commonPrefix ((devU k).drop (k * (2 * k - 1))) twoColoured.toList
def depthV (k : Nat) : Nat := commonPrefix ((devV k).drop (k * (2 * k + 1))) twoColoured.toList

/-! ## The certificates

Every statement below is decided by evaluating the integer recursion above.  The recursion never
leaves `Z`: `Array Int` has no division, and `tsInv` is applied only to series of constant term
`+-1`.  So the mere fact that these evaluate is the integrality statement at this order; the
residual theorems are what make the computed series the zero series rather than an arbitrary
integer series. -/

/-- **`thm:integrality`, the displayed expansion.**  The first 21 coefficients of
    `u_1(q) = z_1(q)`, matching the note's `rem:zerocurve-arith` (d). -/
theorem u1_coefficients :
    (uList 1).take 21 =
      [1, -1, 0, -1, 1, -1, 2, -2, 4, -6, 8, -14, 21, -34, 56, -88, 148, -242, 398, -669,
        1109] := by
  native_decide

/-- The note's `u_2 = 1 - q^6 - 2q^8 + q^9 - ...`, extended two coefficients. -/
theorem u2_prefix : (uList 2).take 12 = [1, 0, 0, 0, 0, 0, -1, 0, -2, 1, -4, 5] := by
  native_decide

/-- **The residual vanishes, cosine side.**  `F_k(q, u_k) = 0` to order `q^80` for `k <= 6`: the
    integer series produced by the Newton recursion really is a root of the defining equation. -/
theorem cosine_residual_vanishes :
    ([1, 2, 3, 4, 5, 6].map fun k => (Fval cCos k (uSeries k)).toList.all (· = 0))
      = [true, true, true, true, true, true] := by
  native_decide

/-- **The residual vanishes, sine side**, for `k <= 5`. -/
theorem sine_residual_vanishes :
    ([1, 2, 3, 4, 5].map fun k => (Fval cSin k (vSeries k)).toList.all (· = 0))
      = [true, true, true, true, true] := by
  native_decide

/-- **`cor:hexagonal`.**  The deviation `1 - u_k` begins at the `k`-th hexagonal number
    `k(2k-1) = 1, 6, 15, 28, 45, 66` with leading coefficient `1`, i.e. `u_k - 1` has leading
    coefficient `-1`. -/
theorem cosine_onsets :
    ([1, 2, 3, 4, 5, 6].map fun k => firstNz (devU k))
      = [(1, 1), (6, 1), (15, 1), (28, 1), (45, 1), (66, 1)] := by
  native_decide

/-- **`prop:sinelattice` (c).**  The sine-side deviations begin at `k(2k+1) = 3, 10, 21, 36, 55`,
    the triangular numbers `T_{2k}` interleaving the cosine-side `T_{2k-1}`. -/
theorem sine_onsets :
    ([1, 2, 3, 4, 5].map fun k => firstNz (devV k))
      = [(3, 1), (10, 1), (21, 1), (36, 1), (55, 1)] := by
  native_decide

/-- The two-coloured partition series `1/(q^2;q^2)_inf^2 = 1 + 2q^2 + 5q^4 + 10q^6 + ...`. -/
theorem twoColoured_prefix :
    twoColoured.toList.take 14 = [1, 0, 2, 0, 5, 0, 10, 0, 20, 0, 36, 0, 65, 0] := by
  native_decide

/-- **`prop:stablelaw`, cosine side.**  The longest common prefix of `(1-u_k) q^{-T_{2k-1}}` and
    `1/(q^2;q^2)_inf^2` has length `2, 3, 5, 7, 9, 11` for `k = 1, ..., 6`: agreement through
    order `2k-2` for `k >= 2`, exactly the depth the note reports, and no further. -/
theorem cosine_agreement_depth : [1, 2, 3, 4, 5, 6].map depthU = [2, 3, 5, 7, 9, 11] := by
  native_decide

/-- **`prop:stablelaw`, sine side.**  Prefix lengths `2, 4, 6, 8, 10` for `k = 1, ..., 5`:
    agreement through order `2k-1`, again exactly the reported depth. -/
theorem sine_agreement_depth : [1, 2, 3, 4, 5].map depthV = [2, 4, 6, 8, 10] := by
  native_decide

end QZeroSeries

/-! ### Axiom audit (Rule 5)

`native_decide` contributes `Lean.ofReduceBool`; that is declared here rather than hidden. -/

#print axioms QZeroSeries.u1_coefficients
#print axioms QZeroSeries.u2_prefix
#print axioms QZeroSeries.cosine_residual_vanishes
#print axioms QZeroSeries.sine_residual_vanishes
#print axioms QZeroSeries.cosine_onsets
#print axioms QZeroSeries.sine_onsets
#print axioms QZeroSeries.twoColoured_prefix
#print axioms QZeroSeries.cosine_agreement_depth
#print axioms QZeroSeries.sine_agreement_depth
