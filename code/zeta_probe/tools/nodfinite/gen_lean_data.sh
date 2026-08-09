#!/bin/bash
# gen_lean_data.sh -- regenerate lean/with_mathlib/NoDFiniteData.lean from the rank
# certificates produced by the `nodfinite` tool.
#
#   cd code/zeta_probe/tools/nodfinite
#   cargo build --release
#   ./target/release/nodfinite                             > certificates.txt
#   ./target/release/nodfinite 0,31 1,15 2,9 13,1 20,0      > certificates_fhbox.txt
#   ./gen_lean_data.sh > ../../../../lean/with_mathlib/NoDFiniteData.lean
#
# The eleven pairs emitted are the maximal elements, under componentwise order, of the
# union of the two searched regions:
#
#   S1  (prop:no-dfinite)          1 <= k <= 9, m <= 7,        (k+1)(m+1) < 43-k
#   S2  (prop:finite-horizon(ii))  (k+1)(m+1) <= 32,           (k+1)(m+1) < 43-k
#
# S1 contributes (3,7) (4,6) (5,5) (6,4) (7,3) (9,2); S2 adds (0,31) (1,15) (2,9) (13,1)
# (20,0), its own maximal cells (4,5) and (5,4) being dominated by (4,6) and (5,5).

set -euo pipefail
cd "$(dirname "$0")"

PAIRS_S1="3,7 4,6 5,5 6,4 7,3 9,2"
PAIRS_S2="0,31 1,15 2,9 13,1 20,0"

cat <<'HEADER'
/-
  NoDFiniteData.lean
  ==================
  GENERATED FILE.  Regenerate with `code/zeta_probe/tools/nodfinite/gen_lean_data.sh`.

  Certificate data for `prop:no-dfinite` and for the narrowed holonomic box of
  `prop:finite-horizon`(ii), together with the kernel-checked modular identities that
  consume it.  `NoDFiniteCertificates.lean` turns those identities into the non-existence
  statements; this file carries no Mathlib dependency, so it elaborates in seconds.

  THE SYSTEM.  A recurrence of order `k` with coefficient polynomials of degree `m` is a
  family `(c_{j,t})`, `j <= k`, `t <= m`, with

      sum_{j <= k} sum_{t <= m} c_{j,t} n^t u_{n-j} = 0      for every n with k <= n <= 42.

  Unknowns are indexed by a single column number `c = j*(m+1) + t`, so `j = c / (m+1)` and
  `t = c % (m+1)`; equations are indexed by `n`.  Writing `N = (k+1)(m+1)`, non-existence of
  a nonzero solution is exactly full column rank of the `(43-k) x N` coefficient matrix.

  THE CERTIFICATE.  `rows_k_m` names `N` equation offsets `r` (so `n = k + r`), and
  `minv_k_m` is an `N x N` integer matrix which is a left inverse, modulo the prime
  `p = 2^31 - 1`, of the square submatrix cut out by those rows.  `certOK` checks exactly
  that, by kernel evaluation.  Since reduction modulo a prime can only lower rank, a modular
  left inverse forces a nonzero determinant over Z, hence trivial kernel over Q; that
  implication is `ModularRankCertificate.eq_zero_of_modular_left_inverse`.  A modular
  certificate therefore PROVES a rational statement, unlike a modular search, which would
  only be evidence.

  All arithmetic here is on `Nat`.  Certificate entries are already reduced mod `p`, and the
  matrix entries `n^t u_{n-j}` are nonnegative, so nothing needs `Int`; the products stay
  below `2^62` and the Lean kernel's GMP path handles them as single words.
-/

namespace NoDFiniteData

/-- The Mersenne prime `2^31 - 1`. -/
def pMod : Nat := 2147483647

/-- A396406, `u_0, ..., u_42`.  Identical to `DFiniteReduction.uList` under `Nat -> Int`;
    `NoDFiniteCertificates.u_eq` proves it. -/
def uNat : List Nat :=
  [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574,
   11543, 17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236,
   1697179, 2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781, 43997388,
   65932461, 98849591, 147969934]

def uN (i : Nat) : Nat := uNat.getD i 0

/-- Coefficient-matrix entry at equation `n` and column `c`, the column decoding as
    `j = c / (m+1)`, `t = c % (m+1)`. -/
def aEnt (m n c : Nat) : Nat := n ^ (c % (m + 1)) * uN (n - c / (m + 1))

/-- Column `c` of the certified square submatrix, reduced mod `p`. -/
def colOf (k m : Nat) (rows : List Nat) (c : Nat) : List Nat :=
  rows.map (fun r => aEnt m (k + r) c % pMod)

/-- The certified square submatrix, stored by columns. -/
def subT (k m : Nat) (rows : List Nat) : List (List Nat) :=
  (List.range ((k + 1) * (m + 1))).map (colOf k m rows)

/-- Inner product mod `p`, accumulator reduced at every step so the products stay small. -/
def dotm (as bs : List Nat) : Nat :=
  (as.zip bs).foldl (fun acc ab => (acc + ab.1 * ab.2) % pMod) 0

def idRow (n i : Nat) : List Nat := (List.range n).map (fun j => if i == j then 1 else 0)

def idMat (n : Nat) : List (List Nat) := (List.range n).map (idRow n)

/-- The certificate check.  `rows` selects `N` equations in range, `minv` is `N x N`, and
    `minv * M = I` modulo `p`, where `M` is the submatrix of the coefficient matrix on those
    rows.  `subT` stores `M` by columns, so `Mt.map (dotm mi)` is one row of the product. -/
def certOK (k m : Nat) (rows : List Nat) (minv : List (List Nat)) : Bool :=
  (rows.length == (k + 1) * (m + 1)) && (minv.length == (k + 1) * (m + 1)) &&
  rows.all (fun r => decide (k + r ≤ 42)) &&
  minv.all (fun mi => mi.length == (k + 1) * (m + 1)) &&
  (minv.map (fun mi => (subT k m rows).map (dotm mi)) == idMat ((k + 1) * (m + 1)))

/-! ### The searched region and its maximal cells

    `inBox k m` is the union of the two guarded search regions: the grid of
    `prop:no-dfinite` (`1 <= k <= 9`, `m <= 7`) and the narrowed holonomic box of
    `prop:finite-horizon`(ii) (`(k+1)(m+1) <= 32`), both under the over-determination
    condition `(k+1)(m+1) < 43-k`.  Without that condition the system has more unknowns than
    equations and a nonzero solution exists for every input sequence whatever, so a search
    proves nothing; see `OverDetermination.lean`. -/

def inBox (k m : Nat) : Bool :=
  decide ((k + 1) * (m + 1) < 43 - k) &&
    (decide (1 ≤ k ∧ k ≤ 9 ∧ m ≤ 7) || decide ((k + 1) * (m + 1) ≤ 32))

/-- The eleven maximal cells of `inBox` under the componentwise order. -/
def maxCells : List (Nat × Nat) :=
  [(0, 31), (1, 15), (2, 9), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (9, 2), (13, 1), (20, 0)]

/-- Every cell of the region is dominated by a maximal cell.  The bounds `k < 21`, `m < 32`
    are not a restriction: `NoDFiniteCertificates.box_bounds` derives them from `inBox`. -/
theorem box_covered :
    ∀ k, k < 21 → ∀ m, m < 32 → inBox k m = true →
      maxCells.any (fun p => decide (k ≤ p.1) && decide (m ≤ p.2)) = true := by decide

/-- Each maximal cell lies in the region. -/
theorem maxCells_inBox : maxCells.all (fun p => inBox p.1 p.2) = true := by decide

/-- The region contains the whole `prop:no-dfinite` grid. -/
theorem grid_subset_box :
    ∀ k, k < 10 → ∀ m, m < 8 →
      (decide (1 ≤ k) && decide (k ≤ 9) && decide (m ≤ 7) &&
        decide ((k + 1) * (m + 1) < 43 - k)) = true → inBox k m = true := by decide

/-! ### The eleven certificates

    Produced by `code/zeta_probe/tools/nodfinite`, which self-checks `minv * M = I (mod p)`
    in GMP-free `i128` arithmetic before printing.  Lean re-runs that check in the kernel;
    the search that produced the data is not trusted. -/

HEADER

./emit_lean.sh certificates.txt "$PAIRS_S1"
./emit_lean.sh certificates_fhbox.txt "$PAIRS_S2"

cat <<'FOOTER'
/-! ### Kernel evaluation of the eleven modular identities

    `decide +kernel` runs the check in the kernel only, so the elaborator does not duplicate
    the work.  Nothing here uses `native_decide`: the axiom list is `[propext]` throughout,
    with no compiler-evaluation axiom. -/

set_option maxRecDepth 100000

theorem cert_0_31 : certOK 0 31 rows_0_31 minv_0_31 = true := by decide +kernel
theorem cert_1_15 : certOK 1 15 rows_1_15 minv_1_15 = true := by decide +kernel
theorem cert_2_9  : certOK 2 9  rows_2_9  minv_2_9  = true := by decide +kernel
theorem cert_3_7  : certOK 3 7  rows_3_7  minv_3_7  = true := by decide +kernel
theorem cert_4_6  : certOK 4 6  rows_4_6  minv_4_6  = true := by decide +kernel
theorem cert_5_5  : certOK 5 5  rows_5_5  minv_5_5  = true := by decide +kernel
theorem cert_6_4  : certOK 6 4  rows_6_4  minv_6_4  = true := by decide +kernel
theorem cert_7_3  : certOK 7 3  rows_7_3  minv_7_3  = true := by decide +kernel
theorem cert_9_2  : certOK 9 2  rows_9_2  minv_9_2  = true := by decide +kernel
theorem cert_13_1 : certOK 13 1 rows_13_1 minv_13_1 = true := by decide +kernel
theorem cert_20_0 : certOK 20 0 rows_20_0 minv_20_0 = true := by decide +kernel

/-! ### Axiom audit (Rule 5) -/

#print axioms box_covered
#print axioms maxCells_inBox
#print axioms grid_subset_box
#print axioms cert_0_31
#print axioms cert_1_15
#print axioms cert_2_9
#print axioms cert_3_7
#print axioms cert_4_6
#print axioms cert_5_5
#print axioms cert_6_4
#print axioms cert_7_3
#print axioms cert_9_2
#print axioms cert_13_1
#print axioms cert_20_0

end NoDFiniteData
FOOTER
