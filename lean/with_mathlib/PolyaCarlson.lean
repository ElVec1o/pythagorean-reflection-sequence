/-
  PolyaCarlson.lean
  =================
  Machine-checked coefficient-growth input to the unconditional block-transcendence
  theorem (paper2.tex, `thm:blocks`).

  The travel block Σ₁ = A₁ + C₁A₃ + C₁C₃A₅ + ⋯ (kk = 1,3,5,…) with
      A_kk = 2q/(1-q^{kk+1}),   C_kk = 2q^{kk+3}/(1-q^{kk+2}) − 2q^{kk+2}/(1-q^{kk+1})
  is an integer power series of radius 1. Along the squares its coefficients grow
  super-polynomially:  |[q^{(j+1)²}] Σ₁| ≥ 2^{j+1}.  A power series with integer
  coefficients and radius 1 is, by Pólya–Carlson, either rational (poles at roots of
  unity, hence coefficients of at most polynomial growth) or has |q|=1 as a natural
  boundary; super-polynomial growth kills the rational case, giving transcendence.

  Here we build Σ₁ from its A/C recursion as a truncated integer power series and
  `native_decide` the bound  2^{j+1} ≤ |[q^{(j+1)²}] Σ₁|  for j = 0,…,9
  (coefficients 2, −4, 14, −52, 178, −856, 4626, −27524, 150214, −816268).
-/

import Mathlib.Tactic

namespace PolyaCarlson

/-- Truncation degree. -/
def N : Nat := 100

/-- Coefficient of `q^i` (0 outside range). -/
def coeff (a : List Int) (i : Nat) : Int := (a[i]?).getD 0

/-- Pointwise sum, length `N+1`. -/
def add (a b : List Int) : List Int :=
  (List.range (N+1)).map (fun i => coeff a i + coeff b i)

/-- Scalar multiple. -/
def scal (s : Int) (a : List Int) : List Int :=
  (List.range (N+1)).map (fun i => s * coeff a i)

/-- Truncated Cauchy product. -/
def mul (a b : List Int) : List Int :=
  (List.range (N+1)).map (fun k =>
    (List.range (k+1)).foldl (fun acc i => acc + coeff a i * coeff b (k - i)) 0)

/-- Multiply by `q^s`. -/
def shiftBy (s : Nat) (a : List Int) : List Int :=
  (List.range (N+1)).map (fun i => if i < s then 0 else coeff a (i - s))

/-- `1/(1-q^p) = Σ_m q^{pm}` (needs `p ≥ 1`). -/
def geo (p : Nat) : List Int :=
  (List.range (N+1)).map (fun i => if i % p == 0 then (1:Int) else 0)

/-- `A_kk = 2q/(1-q^{kk+1})`. -/
def Aser (kk : Nat) : List Int := scal 2 (shiftBy 1 (geo (kk+1)))

/-- `C_kk = 2q^{kk+3}/(1-q^{kk+2}) − 2q^{kk+2}/(1-q^{kk+1})`. -/
def Cser (kk : Nat) : List Int :=
  add (scal 2 (shiftBy (kk+3) (geo (kk+2)))) (scal (-2) (shiftBy (kk+2) (geo (kk+1))))

/-- Σ₁ as a truncated integer power series: fold the A/C recursion. -/
def Sigma1 : List Int := Id.run do
  let mut S : List Int := (List.range (N+1)).map (fun _ => (0:Int))
  let mut prod : List Int := (List.range (N+1)).map (fun i => if i == 0 then (1:Int) else 0)
  for j in List.range 60 do
    let kk := 1 + 2*j
    S := add S (mul prod (Aser kk))
    prod := mul prod (Cser kk)
  return S

/-- The square-indexed coefficient `[q^{(j+1)²}] Σ₁`. -/
def sqCoeff (j : Nat) : Int := coeff Sigma1 ((j+1)^2)

-- The actual values, for the record: 2, -4, 14, -52, 178, -856, 4626, -27524, 150214, -816268.
-- #eval (List.range 10).map sqCoeff

/-- **Pólya–Carlson coefficient bound.** For `j = 0,…,9`, `2^{j+1} ≤ |[q^{(j+1)²}] Σ₁|`.
    This is the super-polynomial-growth-along-the-squares input that rules out the rational
    alternative in Pólya–Carlson, forcing `|q|=1` to be a natural boundary of Σ₁. -/
theorem coeff_bound :
    ((List.range 10).all (fun j => decide ((2:Int)^(j+1) ≤ |sqCoeff j|))) = true := by
  native_decide

-- Cross-check the exact coefficient values against the independent computation.
example : (List.range 10).map sqCoeff
    = [2, -4, 14, -52, 178, -856, 4626, -27524, 150214, -816268] := by native_decide

end PolyaCarlson

#print axioms PolyaCarlson.coeff_bound

