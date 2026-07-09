/-
  SigmaKernel.lean
  ================
  Machine-checked non-automaticity evidence for the arithmetic ("mod p") route
  to transcendence of the block Σ₁ (paper2.tex §mod-p / outreach open problem).

  A power series over 𝔽_p is p-automatic (equivalently algebraic over 𝔽_p(q),
  Christol's theorem) iff its p-kernel — the set of decimation-subsequences
  {(a_{p^k n + r})_n} — is finite. We build Σ₁ mod 3 from its A/C recursion and
  `native_decide` that its 3-kernel through level 3 is the *full ternary tree*:
  all 1+3+9+27 = 40 decimation words of length ≤ 3 give pairwise-distinct
  sequences (compared on the first 18 terms). Hence the 3-kernel has ≥ 40
  elements — maximal growth, no collapses — strong evidence of non-automaticity
  (and thus transcendence of Σ₁ over 𝔽_3(q)).
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace SigmaKernel

abbrev F := ZMod 3

/-- Truncation degree of the working power series. -/
def N : Nat := 512

def coeff (a : Array F) (i : Nat) : F := a.getD i 0

def addA (a b : Array F) : Array F := Array.ofFn (fun i : Fin (N+1) => coeff a i.val + coeff b i.val)
def scalA (s : F) (a : Array F) : Array F := Array.ofFn (fun i : Fin (N+1) => s * coeff a i.val)
def mulA (a b : Array F) : Array F :=
  Array.ofFn (fun k : Fin (N+1) =>
    (List.range (k.val+1)).foldl (fun acc i => acc + coeff a i * coeff b (k.val - i)) 0)
def shiftA (s : Nat) (a : Array F) : Array F :=
  Array.ofFn (fun i : Fin (N+1) => if i.val < s then 0 else coeff a (i.val - s))
def geoA (p : Nat) : Array F := Array.ofFn (fun i : Fin (N+1) => if i.val % p == 0 then (1:F) else 0)

def Aser (kk : Nat) : Array F := scalA 2 (shiftA 1 (geoA (kk+1)))
def Cser (kk : Nat) : Array F :=
  addA (scalA 2 (shiftA (kk+3) (geoA (kk+2)))) (scalA (-2) (shiftA (kk+2) (geoA (kk+1))))

/-- Σ₁ mod 3 as a truncated series. -/
def Sigma1 : Array F := Id.run do
  let mut S : Array F := Array.ofFn (fun _ : Fin (N+1) => (0:F))
  let mut prod : Array F := Array.ofFn (fun i : Fin (N+1) => if i.val == 0 then (1:F) else 0)
  for j in List.range 30 do
    let kk := 1 + 2*j
    S := addA S (mulA prod (Aser kk))
    prod := mulA prod (Cser kk)
  return S

/-- The `r`-decimation `(a_{3n+r})_n` (elements at indices ≡ r mod 3). -/
def decim (seq : List F) (r : Nat) : List F :=
  seq.zipIdx.filterMap (fun p => if p.2 % 3 == r then some p.1 else none)

/-- All decimation sequences reachable in exactly `k` steps. -/
def levelSeqs : Nat → List (List F)
  | 0 => [Sigma1.toList]
  | (k+1) => (levelSeqs k).flatMap (fun s => [decim s 0, decim s 1, decim s 2])

/-- Comparison length (each level-3 sequence has ≥ 18 terms). -/
def L : Nat := 18

/-- The 40 decimation words of length ≤ 3, truncated to their first `L` terms. -/
def kernelPrefixes : List (List F) :=
  ((List.range 4).flatMap levelSeqs).map (fun s => s.take L)

/-- **Maximal 3-kernel through level 3.** The 40 decimation words of length ≤ 3 give
    pairwise-distinct sequences (on the first 18 terms): the 3-kernel of Σ₁ mod 3 is the
    full ternary tree with no collapses, so it has ≥ 40 elements. This is the strongest
    finite non-automaticity certificate — evidence that Σ₁ is not 3-automatic, hence
    transcendental over 𝔽₃(q) (Christol). -/
theorem kernel_full_tree : kernelPrefixes.dedup.length = 40 := by native_decide

end SigmaKernel

#print axioms SigmaKernel.kernel_full_tree
