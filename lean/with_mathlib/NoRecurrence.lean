/-
  NoRecurrence.lean
  =================
  Paper "extra", Proposition `prop:no-recurrence`: the sequence u_0, ..., u_38 (OEIS A396406)
  satisfies no linear recurrence over the rationals of order at most 19.

  METHOD.  For each order k the assertion is that the linear system

      u_n = sum_{j=1..k} c_j u_{n-j},     n = k, ..., 38

  of 39 - k equations in k unknowns has no rational solution.  Inconsistency is certified by
  a Farkas witness: an integer vector w with w^T A = 0 and w^T b /= 0.  If some rational c
  solved the system then w^T b = w^T (A c) = (w^T A) c = 0, contradicting w^T b /= 0.

  This is what makes the proposition machine-checkable.  Nothing here re-runs the linear
  algebra: the witnesses were computed once, in exact GMP arithmetic, by the Rust tool
  `code/zeta_probe/tools/norec`, and Lean only verifies the two defining properties of each
  witness, which are integer dot products.  A witness is a self-contained proof, so a reader
  need not trust the search that produced it.

  The witnesses are small, at most 22 digits per entry, so the verification is done by kernel
  evaluation (`decide`) and incurs no `native_decide` axiom.
-/

import Mathlib

namespace NoRecurrence

open Finset

/-! ### The sequence -/

/-- The first 39 terms of A396406, `u_0, ..., u_38`. -/
def uList : List Int :=
  [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066,
   3203, 4971, 7574, 11543, 17683, 27108, 41067, 62263, 94622, 143881,
   217101, 327832, 495443, 749195, 1127236, 1697179, 2554961, 3848384,
   5777651, 8679441, 13031206, 19574659, 29338781]

def u (n : Nat) : Int := uList.getD n 0

/-- Number of equations available at order `k`. -/
def rows (k : Nat) : Nat := 39 - k

/-- Coefficient of `c_{j+1}` in the equation indexed by `i` at order `k`. -/
def Amat (k i j : Nat) : Int := u (k + i - 1 - j)

/-- Right-hand side of the equation indexed by `i` at order `k`. -/
def bvec (k i : Nat) : Int := u (k + i)

/-! ### The Farkas witnesses, computed by `tools/norec` -/

/-- For each order `k` from 1 to 19, an integer vector `w` of length `39 - k`. -/
def certList : List (Nat × List Int) :=
[
  (1, [-3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (2, [1, -7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (3, [0, -5, -8, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (4, [0, -3, -5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (5, [0, -2, -3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (6, [0, -1, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (7, [0, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (8, [8192, -61659, 30593, 8455, -2252, -2832, 2368, -2304, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (9, [120374, -71661, 73034, -37787, 113476, -80652, -14297, 7194, -24893, 17751, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (10, [-4893442, -7852554, -2214592, 26438926, -20448605, 31965456, -16193177, -5606325, 4592941, -7446744, 4200201, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (11, [13365168, -30113068, -13411594, 8953230, 74708460, -44196079, 75350224, -48927053, -15760371, 9667045, -17695962, 11825083, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (12, [25286928, -57276292, -51150814, 22982730, 151562340, -20678989, 116374432, -50101799, -66158601, 4704607, -27638814, 11763217, 8631312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (13, [-854138710, 1979877818, 1579633744, -858363292, -5060237515, 1081368980, -4013543320, 1976189882, 2081279658, -302035170, 952186053, -465657561, -255355641, 15608861, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (14, [-6313769590, -88616795178, -39973137724, 195004060332, -48615234035, 168705965670, -69663201280, 9004354478, -73502700718, 28028630470, -11883604863, -8676952319, 19335247161, -16696460881, 7432858550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (15, [-808743204794, 252577376420, -744260333186, 1476414868580, -1696245798337, 2571736098748, -1567568444681, 624361035723, 815630626557, -1070191216337, 1092185756287, -716443612099, -75114369773, 91061627761, -169927761732, 124248208817, 0, 0, 0, 0, 0, 0, 0, 0]),
  (16, [121975819461568, 99412471571700, 255418887412642, -891321485354250, 603029611951664, -1108573991558511, 828716641115677, -363191446315046, 217247421637816, 186559520503244, -279165751813269, 296109276790733, -165367598608779, 25838298312463, 14438646766219, -43677403080429, 20347835411805, 0, 0, 0, 0, 0, 0]),
  (17, [-5448441209777022, 40169618748228028, 32076759995389446, -86023446643481154, -43036014506146429, -50936056232588368, -20261846909445586, 43520429371659330, 29298008296457473, 20751870137675245, 6265956826547797, -91217646511950, -1326764460889426, -9835405592877448, -436140590829629, -2214959287620138, -933670826809509, 2184229133591441, 0, 0, 0, 0]),
  (18, [18520863160616366, -58629321488708564, 63162840846191482, 107980380150538602, -68032022032840323, -119348759519025156, -5317698376445662, -136082218155503130, 70709010968628831, 49777837761975535, 10175546856034359, 39908274367934130, -13154507245900822, 13218758466754304, -18912348608248283, -1746909182808346, -1563121513605243, -5021013955305133, 4622247961626340, 0, 0]),
  (19, [-294489679895342166902, 2039549893049947569028, 1021002616493884336366, -3884628030041123269954, -1290661587604644243529, -2252672270386347702028, -1400800854591128058906, 2297787915166653182770, 547750733940296771293, 1096815338916723370125, 464722528296862207077, -68589201826702164330, 145018180774277366334, -532836400280483395328, 87430589406941197231, -174841337544912693198, -45094196523044070449, 104953137002206061241, -33738592351124038740, 19585297119629158400])
]

/-- The witness for order `k`, as a function on indices. -/
def w (k i : Nat) : Int :=
  ((certList.lookup k).getD []).getD i 0

/-! ### Verifying the two defining properties of each witness

    Both are integer dot products over `List.range`, hence decidable by kernel evaluation. -/

/-- `w^T A` at column `j`. -/
def orth (k j : Nat) : Int :=
  (((List.range (rows k)).map (fun i => w k i * Amat k i j)).sum)

/-- `w^T b`. -/
def pair (k : Nat) : Int :=
  (((List.range (rows k)).map (fun i => w k i * bvec k i)).sum)

/-- **Each witness is orthogonal to every column of its coefficient matrix.** -/
theorem orth_zero : ∀ k, k < 20 → 1 ≤ k → ∀ j, j < k → orth k j = 0 := by decide

/-- **And each witness pairs nontrivially with the right-hand side.** -/
theorem pair_ne_zero : ∀ k, k < 20 → 1 ≤ k → pair k ≠ 0 := by decide

/-- Every witness has the length its order requires. -/
theorem cert_lengths : ∀ k, k < 20 → 1 ≤ k → ((certList.lookup k).getD []).length = rows k := by
  decide

/-! ### The Farkas argument -/

theorem sum_range_eq_list (f : Nat → Int) (n : Nat) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := rfl

/-- **Farkas: a witness rules out every rational solution.**  Stated for arbitrary integer
    data, so the argument is visibly independent of the particular sequence. -/
theorem no_solution_of_witness {k r : Nat} (A : Nat → Nat → Int) (b : Nat → Int)
    (ω : Nat → Int)
    (horth : ∀ j, j < k → ∑ i ∈ Finset.range r, ω i * A i j = 0)
    (hpair : ∑ i ∈ Finset.range r, ω i * b i ≠ 0) :
    ¬ ∃ c : Nat → Rat, ∀ i, i < r →
        ∑ j ∈ Finset.range k, (A i j : Rat) * c j = (b i : Rat) := by
  rintro ⟨c, hc⟩
  apply hpair
  have cast_eq : ((∑ i ∈ Finset.range r, ω i * b i : Int) : Rat)
      = ∑ i ∈ Finset.range r, (ω i : Rat) * (b i : Rat) := by push_cast; ring
  have main : ∑ i ∈ Finset.range r, (ω i : Rat) * (b i : Rat) = 0 := by
    have step1 : ∑ i ∈ Finset.range r, (ω i : Rat) * (b i : Rat)
        = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range k,
            (ω i : Rat) * ((A i j : Rat) * c j) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← hc i (Finset.mem_range.mp hi), Finset.mul_sum]
    have step3 : ∀ j ∈ Finset.range k,
        ∑ i ∈ Finset.range r, (ω i : Rat) * ((A i j : Rat) * c j) = 0 := by
      intro j hj
      have h0 := horth j (Finset.mem_range.mp hj)
      have hq : ∑ i ∈ Finset.range r, (ω i : Rat) * (A i j : Rat) = 0 := by
        have hcast : ((∑ i ∈ Finset.range r, ω i * A i j : Int) : Rat) = 0 := by
          rw [h0]; simp
        push_cast at hcast
        exact hcast
      calc ∑ i ∈ Finset.range r, (ω i : Rat) * ((A i j : Rat) * c j)
          = (∑ i ∈ Finset.range r, (ω i : Rat) * (A i j : Rat)) * c j := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = 0 := by rw [hq, zero_mul]
    rw [step1, Finset.sum_comm, Finset.sum_eq_zero step3]
  rw [← cast_eq] at main
  exact_mod_cast main

/-! ### The proposition -/

/-- **Proposition `prop:no-recurrence`.**  For every order `k` with `1 <= k <= 19`, no rational
    coefficient vector satisfies the order-`k` recurrence on the available terms. -/
theorem no_linear_recurrence (k : Nat) (hk1 : 1 ≤ k) (hk19 : k ≤ 19) :
    ¬ ∃ c : Nat → Rat, ∀ i, i < rows k →
        ∑ j ∈ Finset.range k, (Amat k i j : Rat) * c j = (bvec k i : Rat) := by
  refine no_solution_of_witness (Amat k) (bvec k) (w k) ?_ ?_
  · intro j hj
    rw [sum_range_eq_list]
    exact orth_zero k (Nat.lt_succ_of_le hk19) hk1 j hj
  · rw [sum_range_eq_list]
    exact pair_ne_zero k (Nat.lt_succ_of_le hk19) hk1

/-! ### Axiom audit (Rule 5) -/

#print axioms orth_zero
#print axioms pair_ne_zero
#print axioms cert_lengths
#print axioms sum_range_eq_list
#print axioms no_solution_of_witness
#print axioms no_linear_recurrence

end NoRecurrence
