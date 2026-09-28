/-
Paper1TierB1.lean
=================
Formalization-debt paydown, Tier-A items from `paper/journal/paper1.tex`
(2026-09-28 triage, `private/FORMALIZATION_TRIAGE.md`), session following the one that
produced `Paper1TierA.lean` / `Paper1TierACensus.lean` (committed 74c6ec7).

Target items for this session:

  * `thm:Bproved` -- NOT DONE. See the note at the bottom of this file for the precise
    reason (the statement's second half is a match against a 275,823-element breadth-first
    enumeration that exists only as Rust/Python output, not as Lean-ingestible data; the
    same obstruction that stopped the depth-32/33 BFS items in the prior triage pass).

  * `thm:WT-lowcomplexity`(i) -- DONE, for the *rational* case, which is the piece the
    paper's own proof states explicitly and by name: "the matrix is the 17x16 Hankel block
    `(u_{n-j})_{16<=n<=32, 0<=j<=15}`, whose kernel would contain the denominator. ... has
    full column rank modulo the prime `2^61-1`, hence over Q." We reproduce exactly this
    linear-algebra fact: the 17x16 integer Hankel matrix built from `u_0, ..., u_32`
    (A396406, the values already carried by `NoRecurrence.uList`) has trivial kernel over
    Q, certified by a modular left inverse of a 16x16 submatrix (prime `2^31-1`, matching
    this project's existing convention in `NoDFiniteData.lean` rather than the paper's
    `2^61-1` -- any prime works for the certificate, see `ModularRankCertificate.lean`).
    This is precisely the fact from which "no relation of type (i) exists" follows: a
    rational function `F_T = P/Q` of degree `<= 15` over `<= 15`, agreeing with `F_T` mod
    `x^33` (guaranteed by `thm:universality-sharp` for `d <= 32`), gives a nonzero
    coefficient vector of `Q` annihilated by this Hankel matrix.

    Parts (ii) (algebraic relations, six boxes) and (iii) (P-recursive relations, eleven
    boxes) of `thm:WT-lowcomplexity` are NOT attempted here: each box needs its own
    coefficient matrix and its own modular certificate (17 matrices total across (i)-(iii)
    in the paper), and generating + verifying all of them is beyond this session's budget.
    Part (i) is representative of the whole method (same lemma, same style of matrix,
    reused verbatim from `ModularRankCertificate.lean`), and is exactly what the paper
    highlights in its own proof text.

Reuses, without modification, the general bridge `ModularRankCertificate.lean`
(`no_nonzero_solution_of_submatrix`) already in this project for the "extra" paper's
`prop:no-dfinite`. No new general lemma was needed -- this file only supplies new concrete
data (the Hankel matrix and its modular inverse) and the finite `native_decide` check.

No `sorry`.
-/
import Mathlib
import ModularRankCertificate

namespace Paper1TierB1

open Matrix

/-! ## `thm:WT-lowcomplexity`(i): the rational-relation Hankel matrix has trivial kernel -/

/-- `u_0, ..., u_32`, A396406 (33 terms) -- the universal layer values shared by every
right triangle `T` through depth 32, by `thm:universality-sharp`. Identical prefix to
`NoRecurrence.uList`. -/
def uList : List Int :=
  [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066,
   3203, 4971, 7574, 11543, 17683, 27108, 41067, 62263, 94622, 143881,
   217101, 327832, 495443, 749195, 1127236, 1697179, 2554961]

def u (n : Nat) : Int := uList.getD n 0

/-- The `17 x 16` Hankel block `(u_{n-j})_{16 <= n <= 32, 0 <= j <= 15}` of the paper's
proof of `thm:WT-lowcomplexity`(i): row `i` (for `n = 16 + i`, `0 <= i <= 16`) has entries
`u_{16+i-j}` for `0 <= j <= 15`. A nonzero vector `q` in its kernel would be the (reversed)
coefficient list of a denominator `Q` of degree `<= 15` for a rational growth series
`F_T = P/Q` of type `(15,15)` agreeing with `F_T` through `x^32`. -/
def A : Matrix (Fin 17) (Fin 16) Int :=
  !![3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34, 21, 13, 8, 5, 3;
    4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34, 21, 13, 8, 5;
    7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34, 21, 13, 8;
    11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34, 21, 13;
    17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34, 21;
    27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55, 34;
    41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89, 55;
    62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144, 89;
    94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225, 144;
    143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351, 225;
    217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554, 351;
    327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875, 554;
    495443, 327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345, 875;
    749195, 495443, 327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066, 1345;
    1127236, 749195, 495443, 327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203, 2066;
    1697179, 1127236, 749195, 495443, 327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971, 3203;
    2554961, 1697179, 1127236, 749195, 495443, 327832, 217101, 143881, 94622, 62263, 41067, 27108, 17683, 11543, 7574, 4971]

/-- `A` really is the claimed Hankel block, entrywise. -/
theorem A_eq_hankel (i : Fin 17) (j : Fin 16) :
    A i j = u (16 + i.val - j.val) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The prime used for the certificate: `2^31 - 1`, this project's standing convention for
modular rank certificates (`NoDFiniteData.lean`); the paper's own proof uses `2^61-1`, but
any prime certifying the same nonzero determinant works, by `ModularRankCertificate.lean`. -/
def pMod : Nat := 2147483647

instance : Fact (1 < pMod) := ⟨by decide⟩

/-- Drop row `0` of `A` (the row for `n = 16`): the remaining 16 rows (`n = 17,...,32`)
form the square submatrix the certificate is for. -/
def rowsSel : Fin 16 → Fin 17 := fun i => ⟨i.val + 1, by omega⟩

/-- A modular inverse, mod `pMod`, of the square submatrix `A.submatrix rowsSel id`. -/
def Minv : Matrix (Fin 16) (Fin 16) Int :=
  !![1536868096, 1369938499, 459650942, 1416376995, 1202846014, 1046935549, 783659343, 2084592343, 1920646617, 2101318463, 1531961665, 384880259, 1769630162, 27391533, 1242722041, 31369880;
    417458480, 509922947, 669627611, 683114170, 996033649, 2022981726, 1983421829, 1229918162, 481713005, 289435932, 1880531793, 886972501, 1072680560, 789291234, 418364177, 1242722041;
    957477562, 1218115885, 919937771, 710666066, 1614215803, 995534237, 174019065, 1190939032, 1419319188, 1606313538, 1942615115, 940470230, 611923921, 708988866, 789291234, 27391533;
    630908507, 1253768359, 534477985, 1655075369, 1175335623, 1010045197, 847431891, 1535242377, 576468390, 443763162, 424898405, 1888159975, 1812265312, 611923921, 1072680560, 1769630162;
    130212816, 597982250, 1807008990, 2035014247, 1746682964, 169465850, 647125038, 472370975, 1760691421, 930770189, 2007249376, 1719195508, 1888159975, 940470230, 886972501, 384880259;
    1487497061, 2081721386, 267322731, 603387542, 311720721, 1479771619, 1885263045, 1557186548, 1167754193, 929463823, 1638515351, 2007249376, 424898405, 1942615115, 1880531793, 1531961665;
    1236799707, 1414071002, 1597873347, 27093876, 892377100, 314913209, 1484035633, 1898293072, 377075823, 1745272257, 929463823, 930770189, 443763162, 1606313538, 289435932, 2101318463;
    1137706122, 575228746, 1165001666, 2009428497, 521880334, 1810662508, 921250676, 1994458261, 303050724, 377075823, 1167754193, 1760691421, 576468390, 1419319188, 481713005, 1920646617;
    278919970, 197757179, 844973759, 1830826273, 1629200882, 66660800, 896130597, 1273244658, 1994458261, 1898293072, 1557186548, 472370975, 1535242377, 1190939032, 1229918162, 2084592343;
    135406863, 1943402280, 1780622354, 939266867, 2070353811, 1818098411, 34884753, 896130597, 921250676, 1484035633, 1885263045, 647125038, 847431891, 174019065, 1983421829, 783659343;
    630233331, 295283471, 503256154, 27437275, 1656052892, 702183967, 1818098411, 66660800, 1810662508, 314913209, 1479771619, 169465850, 1010045197, 995534237, 2022981726, 1046935549;
    1755327539, 547154243, 1846051566, 1903871986, 311349753, 1656052892, 2070353811, 1629200882, 521880334, 892377100, 311720721, 1746682964, 1175335623, 1614215803, 996033649, 1202846014;
    1413637947, 1173634062, 2137032927, 1151307598, 1903871986, 27437275, 939266867, 1830826273, 2009428497, 27093876, 603387542, 2035014247, 1655075369, 710666066, 683114170, 1416376995;
    1973754078, 1436153505, 1251639888, 2137032927, 1846051566, 503256154, 1780622354, 844973759, 1165001666, 1597873347, 267322731, 1807008990, 534477985, 919937771, 669627611, 459650942;
    1282859144, 776289891, 1436153505, 1173634062, 547154243, 295283471, 1943402280, 197757179, 575228746, 1414071002, 2081721386, 597982250, 1253768359, 1218115885, 509922947, 1369938499;
    1532850569, 1282859144, 1973754078, 1413637947, 1755327539, 630233331, 135406863, 278919970, 1137706122, 1236799707, 1487497061, 130212816, 630908507, 957477562, 417458480, 1536868096]

/-- The certificate check: `Minv` is a left inverse of the chosen 16x16 submatrix of `A`,
modulo `pMod`. Checked by `native_decide`: the entries are up to 10 digits, and `16^3`
multiply-add-mod steps for the product easily justify the compiler trust base (as in
`NoDFiniteData.lean` / `NoDFiniteCertificates.lean`, tier (ii) of the paper's own
three-tier trust bookkeeping, Appendix "reproduce"). -/
theorem cert_ok :
    (Minv * A.submatrix rowsSel id).map (Int.castRingHom (ZMod pMod)) = 1 := by
  native_decide

/-- **`thm:WT-lowcomplexity`(i), the certified linear-algebra core.** The Hankel matrix `A`
built from the universal depth-`<=32` layer values has trivial kernel over `Q`. Concretely:
no nonzero rational vector `q : Fin 16 → Q` (the coefficients of a would-be denominator
`Q(x) = sum_j q_j x^j` of degree `<= 15`) is annihilated by `A`, i.e. satisfies
`sum_j q_j * u_{n-j} = 0` for every `16 <= n <= 32` at once. This is exactly the fact the
paper's proof of part (i) invokes ("full column rank ... hence over Q"): since
`u_d^T = u_d` for `0 <= d <= 32` for every triangle `T` (`thm:universality-sharp`), a
rational relation `F_T = P/Q` of type `(15,15)` would force such a nonzero `q`, which this
theorem rules out. -/
theorem hankel_no_nonzero_kernel :
    ¬ ∃ q : Fin 16 → ℚ, q ≠ 0 ∧ (A.map (Int.castRingHom ℚ)).mulVec q = 0 := by
  rintro ⟨q, hq, hqz⟩
  exact hq (ModularRankCertificate.no_nonzero_solution_of_submatrix A rowsSel Minv cert_ok q hqz)

#print axioms A_eq_hankel
#print axioms hankel_no_nonzero_kernel

end Paper1TierB1

/-
NOT DONE: `thm:Bproved`.

The proposition has two parts. The first ("the transducer's output equals the closed form
`c_pred` for every `g`") is `Lemma~\ref{lem:fsm}`, a finite-state-transition check that
*could* plausibly be formalized along the lines of `CensusUniversal.lean`'s symbolic
polynomial-affine-map machinery, given the automaton's transition table (Definition
`def:transducer`) and the closed form of `Proposition~\ref{prop:Tform}` -- both of which
would first need to be transcribed into Lean as executable functions on a `GapProfile`-like
structure. That transcription alone (the side-automaton state machine, the closed-form sum
over gap-runs with shield bookkeeping, and the boundary cell `eta`) is a substantial
modeling task not attempted this session, since the second, and headline, part of the
statement cannot be closed regardless:

The second part ("on the depth-24 enumeration [275,823 elements] it also equals the true
defect, with 0 exceptions") is a match against the output of
`code/zeta_probe/c_formula.py 24`, a breadth-first enumeration that exists only as
Rust/Python-produced numeric output (not committed as Lean-ingestible term-mode data, and
at 275,823 elements far too large to hand-encode as a Lean literal within this session).
Proving it in Lean would require either (a) reimplementing the BFS enumeration itself as a
computable Lean function and running it via `native_decide` over the full state space -- a
much larger undertaking than the matrix certificates above, with no existing scaffolding in
this project comparable to `NoDFiniteData.lean`'s "certificate as data" pattern for this
specific census -- or (b) exporting the 275,823-element BFS result as committed Lean data
and checking pointwise equality, which needs a data-export step from the Rust tool that
does not currently exist.

This is the same category of obstruction noted in the prior triage round for the
depth-32/33 BFS items, and paper1.tex itself frames `thm:Bproved`'s second half as
computer-verified output of an external script, not as a target for the Lean development
(only the state-machine-transducer half, `lem:fsm`, is flagged there as formalizable
in-house). Recommendation for a future session: first build the BFS-enumeration-as-Lean-data
export path (likely needed for other depth-24/32/33 items too, e.g. `thm:universality-sharp`
itself, `prop:modular-cert`), then `thm:Bproved` and several siblings become tractable in
one pass.
-/
