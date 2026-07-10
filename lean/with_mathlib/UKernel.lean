/-
  UKernel.lean
  ============
  Machine-checked maximal non-automaticity of the TRUE growth series U = A396406
  (paper2.tex, sec:modp). The coefficients (u_n mod 3) for n = 0..270 are the validated
  output of the polynomial-time catalytic engine `tools/u_modp_rust` (self-checked against
  the 43 known u_n; the n <= 180 prefix is byte-identical to the earlier validated run, and
  the engine's exact big-prime run reproduces the full published b-file).

  We `native_decide` that the 3-kernel of (u_n mod 3) through level 3 is the FULL ternary
  tree: all 1 + 3 + 9 + 27 = 40 decimation words of length <= 3 give pairwise-distinct
  sequences (compared on their first 10 terms), no collapses. So the 3-kernel of the ACTUAL
  true series u_n = A396406 has >= 40 elements -- maximal growth, deficit 0 -- strong
  evidence that U is not 3-automatic, hence transcendental over F_3(q) (Christol).

  (The apparent level-3 "deficit 1" reported in earlier, shorter runs was a comparison-length
  artifact: with n <= 180 the level-3 subsequences carry too few terms and two distinct words
  falsely merge; at n = 270 every level-3 word carries >= 10 terms and the tree is full at
  comparison lengths 9 and 10 alike. The sibling certificate for the block Sigma_1 is
  `SigmaKernel.lean`.)
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace UKernel

abbrev F := ZMod 3

/-- (u_n mod 3) for n = 0..270, from `tools/u_modp_rust` (work270; validated as above). -/
def uSeq : List F := [1, 0, 2, 2, 1, 0, 1, 1, 2, 0, 0, 0, 2, 2, 1, 2, 2, 0, 2, 2, 1, 0, 0, 1, 2, 1, 0, 1, 2, 2, 1, 1, 2, 2, 2, 0, 1, 1, 2, 0, 0, 2, 1, 2, 1, 1, 1, 1, 0, 2, 0, 2, 1, 0, 2, 1, 0, 0, 0, 2, 1, 2, 1, 0, 0, 2, 0, 1, 1, 1, 2, 1, 1, 1, 2, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 2, 1, 1, 0, 1, 1, 0, 1, 2, 1, 0, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 2, 1, 1, 2, 2, 1, 0, 1, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1, 2, 0, 1, 0, 2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 0, 1, 2, 1, 2, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 2, 2, 1, 1, 0, 0, 1, 2, 1, 0, 1, 1, 2, 1, 2, 0, 1, 2, 2, 1, 2, 2, 2, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2, 1, 2, 1, 0, 1, 0, 2, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 2, 2, 1, 2, 0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0]

def decim (seq : List F) (r : Nat) : List F :=
  seq.zipIdx.filterMap (fun q => if q.2 % 3 == r then some q.1 else none)

def levelSeqs : Nat → List (List F)
  | 0 => [uSeq]
  | (k+1) => (levelSeqs k).flatMap (fun s => [decim s 0, decim s 1, decim s 2])

def L : Nat := 10

def kernelPrefixes : List (List F) := ((List.range 4).flatMap levelSeqs).map (fun s => s.take L)

/-- **Maximal 3-kernel of u_n = A396406 through level 3.** All 40 decimation words of
    length <= 3 give pairwise-distinct sequences (first 10 terms): the 3-kernel is the full
    ternary tree, deficit 0, so it has >= 40 elements. Strong evidence that U is not
    3-automatic, hence transcendental over F_3(q). -/
theorem u_kernel_full_tree : kernelPrefixes.dedup.length = 40 := by native_decide

end UKernel

#print axioms UKernel.u_kernel_full_tree
