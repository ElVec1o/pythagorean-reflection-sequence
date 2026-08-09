/-
  NoDFiniteCertificates.lean
  ==========================
  Closes `prop:no-dfinite`, and the narrowed holonomic box of `prop:finite-horizon`(ii), by
  feeding the eleven modular rank certificates of `NoDFiniteData.lean` into the general
  implication of `ModularRankCertificate.lean` and the monotonicity reduction of
  `DFiniteReduction.lean`.

  THE THREE PIECES.

    * `DFiniteReduction.no_sol_mono`: non-existence at `(k', m')` propagates down to every
      `(k, m) <= (k', m')`, because zero-padding a coefficient family grows the ansatz while
      the constraint range `k <= n <= 42` shrinks.  So only the maximal cells of a search
      region need certificates.
    * `ModularRankCertificate.eq_zero_of_modular_left_inverse`: a modular left inverse of a
      square integer matrix forces `det /= 0` over `Z`, hence trivial kernel over `Q`.
    * `NoDFiniteData.cert_*`: the eleven concrete modular left inverses, checked in the
      kernel, with no `native_decide` anywhere.

  WHAT THIS FILE ADDS is the plumbing between them: the coefficient matrix of the
  `(k, m)`-recurrence as a `Matrix (Fin N) (Fin N) Int` with `N = (k+1)(m+1)`, the column
  bijection `c <-> (j, t) = (c / (m+1), c % (m+1))` that turns a coefficient family into a
  vector, and the passage from the list-based kernel computation to `Finset.sum` over
  `Fin N`.  The list layer exists only for speed: the eleven checks together are about
  350000 multiply-add-mod steps, which the kernel does in well under a minute on `Nat`
  literals, whereas the same statement phrased directly over `ZMod p` matrices does not
  reduce in usable time.

  SCOPE.  This closes the finite-horizon exclusions on `u_0, ..., u_42` inside the stated
  boxes.  It says nothing about recurrences outside those boxes, and nothing about whether
  the generating series is D-finite; see `rmk:scope-finite-horizon` in the paper.
-/

import Mathlib
import NoDFiniteData
import DFiniteReduction
import ModularRankCertificate

namespace NoDFiniteCertificates

open NoDFiniteData

/-! ### List indexing -/

theorem getD_map_lt {α β : Type*} (f : α → β) (l : List α) (da : α) (db : β) :
    ∀ {t : ℕ}, t < l.length → (l.map f).getD t db = f (l.getD t da) := by
  induction l with
  | nil => intro t h; simp at h
  | cons a l ih =>
    intro t h
    cases t with
    | zero => rfl
    | succ t =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih (by simpa using h)

theorem range_getD {N t : ℕ} (h : t < N) : (List.range N).getD t 0 = t := by
  have h' : t < (List.range N).length := by simpa using h
  rw [List.getD_eq_getElem _ _ h']
  simp

/-! ### From the list inner product to `Finset.sum` -/

theorem foldl_dot_cast (l : List (ℕ × ℕ)) : ∀ acc : ℕ,
    ((l.foldl (fun a ab => (a + ab.1 * ab.2) % pMod) acc : ℕ) : ZMod pMod)
      = (acc : ZMod pMod)
        + (l.map (fun ab => ((ab.1 : ZMod pMod) * (ab.2 : ZMod pMod)))).sum := by
  induction l with
  | nil => intro acc; simp
  | cons ab l ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, ZMod.natCast_mod]
    push_cast
    ring

theorem dotm_cast (as bs : List ℕ) :
    ((dotm as bs : ℕ) : ZMod pMod)
      = ((as.zip bs).map (fun ab => ((ab.1 : ZMod pMod) * (ab.2 : ZMod pMod)))).sum := by
  simp [dotm, foldl_dot_cast]

theorem zip_sum_cast (as : List ℕ) : ∀ bs : List ℕ, as.length = bs.length →
    ((as.zip bs).map (fun ab => ((ab.1 : ZMod pMod) * (ab.2 : ZMod pMod)))).sum
      = ∑ i ∈ Finset.range as.length,
          ((as.getD i 0 : ZMod pMod) * (bs.getD i 0 : ZMod pMod)) := by
  induction as with
  | nil => intro bs _; simp
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih bs (by simpa using h)]
      ring

/-! ### Splitting a range of length `K*T` along division and remainder -/

theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] {T : ℕ} (hT : 0 < T)
    (g : ℕ → ℕ → M) : ∀ K : ℕ,
      ∑ cc ∈ Finset.range (K * T), g (cc / T) (cc % T)
        = ∑ j ∈ Finset.range K, ∑ t ∈ Finset.range T, g j t := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    refine congrArg _ (Finset.sum_congr rfl (fun t ht => ?_))
    rw [Finset.mem_range] at ht
    have hd : (K * T + t) / T = K := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt ht, Nat.zero_add]
    have hm : (K * T + t) % T = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    rw [hd, hm]

/-! ### The sequence, over `Int` -/

theorem u_eq (i : ℕ) : DFiniteReduction.u i = ((uN i : ℕ) : ℤ) := by
  have hl : DFiniteReduction.uList = uNat.map (fun x : ℕ => (x : ℤ)) := by decide
  unfold DFiniteReduction.u uN
  rw [hl]
  rcases lt_or_ge i uNat.length with h | h
  · exact getD_map_lt (fun x : ℕ => (x : ℤ)) uNat 0 0 h
  · rw [List.getD_eq_default _ _ (by simpa using h),
        List.getD_eq_default _ _ (by simpa using h)]
    simp

/-! ### The two matrices of a certificate -/

/-- Entry of the certified square submatrix: row `t` is the equation at `n = k + rows[t]`. -/
def Mfun (k m : ℕ) (rows : List ℕ) (t c : ℕ) : ℤ := ((aEnt m (k + rows.getD t 0) c : ℕ) : ℤ)

/-- Entry of the certificate's left inverse. -/
def Minvfun (minv : List (List ℕ)) (i t : ℕ) : ℤ := (((minv.getD i []).getD t 0 : ℕ) : ℤ)

def Msq (k m : ℕ) (rows : List ℕ) :
    Matrix (Fin ((k + 1) * (m + 1))) (Fin ((k + 1) * (m + 1))) ℤ :=
  Matrix.of fun t c => Mfun k m rows t.val c.val

def Minvsq (k m : ℕ) (minv : List (List ℕ)) :
    Matrix (Fin ((k + 1) * (m + 1))) (Fin ((k + 1) * (m + 1))) ℤ :=
  Matrix.of fun i t => Minvfun minv i.val t.val

/-! ### Unpacking the certificate check -/

theorem certOK_unfold {k m : ℕ} {rows : List ℕ} {minv : List (List ℕ)}
    (h : certOK k m rows minv = true) :
    rows.length = (k + 1) * (m + 1) ∧ minv.length = (k + 1) * (m + 1) ∧
      (∀ r ∈ rows, k + r ≤ 42) ∧ (∀ mi ∈ minv, mi.length = (k + 1) * (m + 1)) ∧
      minv.map (fun mi => (subT k m rows).map (dotm mi)) = idMat ((k + 1) * (m + 1)) := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ### The modular identity, as a matrix statement -/

theorem modular_identity {k m : ℕ} {rows : List ℕ} {minv : List (List ℕ)}
    (h : certOK k m rows minv = true) :
    ((Minvsq k m minv * Msq k m rows).map (Int.castRingHom (ZMod pMod))) = 1 := by
  obtain ⟨hrl, hml, _, hmrl, hprod⟩ := certOK_unfold h
  ext i j
  have hi : i.val < minv.length := by rw [hml]; exact i.isLt
  have hj : j.val < (k + 1) * (m + 1) := j.isLt
  set as := minv.getD i.val [] with has
  set bs := colOf k m rows j.val with hbs
  have hasl : as.length = (k + 1) * (m + 1) := by
    refine hmrl as ?_
    rw [has, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hbsl : bs.length = (k + 1) * (m + 1) := by
    rw [hbs, colOf, List.length_map, hrl]
  -- the (i, j) entry of the product, pushed into `ZMod pMod`
  have hentry : ((Minvsq k m minv * Msq k m rows) i j : ℤ)
      = ∑ t : Fin ((k + 1) * (m + 1)), Minvfun minv i.val t.val * Mfun k m rows t.val j.val :=
    rfl
  rw [Matrix.map_apply, hentry, Matrix.one_apply, map_sum]
  simp only [map_mul, eq_intCast]
  rw [Fin.sum_univ_eq_sum_range
    (fun t => ((Minvfun minv i.val t : ℤ) : ZMod pMod) * ((Mfun k m rows t j.val : ℤ) : ZMod pMod))]
  -- rewrite the summand as the list inner product
  have hsummand : ∀ t ∈ Finset.range ((k + 1) * (m + 1)),
      ((Minvfun minv i.val t : ℤ) : ZMod pMod) * ((Mfun k m rows t j.val : ℤ) : ZMod pMod)
        = ((as.getD t 0 : ZMod pMod) * (bs.getD t 0 : ZMod pMod)) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have htr : t < rows.length := by rw [hrl]; exact ht
    have hb : bs.getD t 0 = aEnt m (k + rows.getD t 0) j.val % pMod := by
      rw [hbs, colOf, getD_map_lt (fun r => aEnt m (k + r) j.val % pMod) rows 0 0 htr]
    rw [hb, Minvfun, Mfun, ← has]
    push_cast [ZMod.natCast_mod]
    ring
  have hz : ((dotm as bs : ℕ) : ZMod pMod)
      = ∑ t ∈ Finset.range ((k + 1) * (m + 1)),
          ((as.getD t 0 : ZMod pMod) * (bs.getD t 0 : ZMod pMod)) := by
    rw [dotm_cast, zip_sum_cast as bs (by rw [hasl, hbsl]), hasl]
  rw [Finset.sum_congr rfl hsummand, ← hz]
  -- and read the value off the certificate
  have hrow : (minv.map (fun mi => (subT k m rows).map (dotm mi))).getD i.val []
      = (subT k m rows).map (dotm as) :=
    getD_map_lt (fun mi => (subT k m rows).map (dotm mi)) minv [] [] hi
  have hid : (idMat ((k + 1) * (m + 1))).getD i.val []
      = idRow ((k + 1) * (m + 1)) i.val := by
    rw [idMat, getD_map_lt (idRow ((k + 1) * (m + 1))) (List.range ((k + 1) * (m + 1))) 0 []
      (by simp [i.isLt]), range_getD i.isLt]
  have hcol : (subT k m rows).getD j.val [] = bs := by
    rw [hbs, subT, getD_map_lt (colOf k m rows) (List.range ((k + 1) * (m + 1))) 0 []
      (by simp [hj]), range_getD hj]
  have hMtlen : (subT k m rows).length = (k + 1) * (m + 1) := by
    rw [subT, List.length_map, List.length_range]
  have hdot : dotm as bs = (if i.val == j.val then 1 else 0) := by
    have h1 := congrArg (fun l => (l.getD i.val []).getD j.val 0) hprod
    simp only at h1
    rw [hrow, hid] at h1
    rw [getD_map_lt (dotm as) (subT k m rows) [] 0 (by rw [hMtlen]; exact hj), hcol] at h1
    rw [idRow, getD_map_lt (fun jj => if i.val == jj then 1 else 0)
      (List.range ((k + 1) * (m + 1))) 0 0 (by simp [hj]), range_getD hj] at h1
    exact h1
  rw [hdot]
  by_cases hij : i = j
  · subst hij; simp
  · have : ¬ (i.val = j.val) := fun hc => hij (Fin.ext hc)
    simp [hij, this]

/-! ### From a certificate to non-existence of a recurrence -/

theorem no_sol_of_cert {k m : ℕ} {rows : List ℕ} {minv : List (List ℕ)}
    (h : certOK k m rows minv = true) :
    ¬ ∃ c, DFiniteReduction.Sol k m c ∧ DFiniteReduction.Nz k m c := by
  obtain ⟨hrl, _, hrle, _, _⟩ := certOK_unfold h
  rintro ⟨c, hsol, hnz⟩
  haveI : Fact (1 < pMod) := ⟨by decide⟩
  have hzero : (fun cc : Fin ((k + 1) * (m + 1)) => c (cc.val / (m + 1)) (cc.val % (m + 1)))
      = 0 := by
    refine ModularRankCertificate.eq_zero_of_modular_left_inverse
      (Minvsq k m minv) (Msq k m rows) (modular_identity h) _ ?_
    funext t
    have htr : t.val < rows.length := by rw [hrl]; exact t.isLt
    have hmem : rows.getD t.val 0 ∈ rows := by
      rw [List.getD_eq_getElem _ _ htr]; exact List.getElem_mem htr
    have hn42 : k + rows.getD t.val 0 ≤ 42 := hrle _ hmem
    have hkn : k ≤ k + rows.getD t.val 0 := Nat.le_add_right _ _
    have hstep : (((Msq k m rows).map (Int.castRingHom ℚ)).mulVec
        (fun cc : Fin ((k + 1) * (m + 1)) => c (cc.val / (m + 1)) (cc.val % (m + 1)))) t
        = ∑ cc : Fin ((k + 1) * (m + 1)),
            ((Mfun k m rows t.val cc.val : ℤ) : ℚ) * c (cc.val / (m + 1)) (cc.val % (m + 1)) :=
      rfl
    rw [hstep, Pi.zero_apply,
      Fin.sum_univ_eq_sum_range (fun cc => ((Mfun k m rows t.val cc : ℤ) : ℚ)
        * c (cc / (m + 1)) (cc % (m + 1)))]
    have hsplit := sum_range_mul_split (T := m + 1) (Nat.succ_pos m)
      (fun j tt => ((k + rows.getD t.val 0 : ℕ) : ℚ) ^ tt
        * ((uN (k + rows.getD t.val 0 - j) : ℕ) : ℚ) * c j tt) (k + 1)
    have hrw : ∀ cc ∈ Finset.range ((k + 1) * (m + 1)),
        ((Mfun k m rows t.val cc : ℤ) : ℚ) * c (cc / (m + 1)) (cc % (m + 1))
          = ((k + rows.getD t.val 0 : ℕ) : ℚ) ^ (cc % (m + 1))
              * ((uN (k + rows.getD t.val 0 - cc / (m + 1)) : ℕ) : ℚ)
              * c (cc / (m + 1)) (cc % (m + 1)) := by
      intro cc _
      rw [Mfun, aEnt]
      push_cast
      ring
    rw [Finset.sum_congr rfl hrw, hsplit]
    have := hsol (k + rows.getD t.val 0) hkn hn42
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun tt _ => ?_))
    rw [u_eq]
    push_cast
    ring
  obtain ⟨j, hj, tt, htt, hne⟩ := hnz
  rw [Finset.mem_range] at hj htt
  have hlt : j * (m + 1) + tt < (k + 1) * (m + 1) := by
    have h1 : j + 1 ≤ k + 1 := by omega
    calc j * (m + 1) + tt < j * (m + 1) + (m + 1) := by omega
      _ = (j + 1) * (m + 1) := by ring
      _ ≤ (k + 1) * (m + 1) := Nat.mul_le_mul_right _ h1
  have hdiv : (j * (m + 1) + tt) / (m + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos m), Nat.div_eq_of_lt htt,
      Nat.zero_add]
  have hmod : (j * (m + 1) + tt) % (m + 1) = tt := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htt]
  have := congrFun hzero ⟨j * (m + 1) + tt, hlt⟩
  simp only [hdiv, hmod, Pi.zero_apply] at this
  exact hne this

/-! ### The eleven cells -/

theorem no_sol_0_31 : ¬ ∃ c, DFiniteReduction.Sol 0 31 c ∧ DFiniteReduction.Nz 0 31 c :=
  no_sol_of_cert cert_0_31
theorem no_sol_1_15 : ¬ ∃ c, DFiniteReduction.Sol 1 15 c ∧ DFiniteReduction.Nz 1 15 c :=
  no_sol_of_cert cert_1_15
theorem no_sol_2_9 : ¬ ∃ c, DFiniteReduction.Sol 2 9 c ∧ DFiniteReduction.Nz 2 9 c :=
  no_sol_of_cert cert_2_9
theorem no_sol_3_7 : ¬ ∃ c, DFiniteReduction.Sol 3 7 c ∧ DFiniteReduction.Nz 3 7 c :=
  no_sol_of_cert cert_3_7
theorem no_sol_4_6 : ¬ ∃ c, DFiniteReduction.Sol 4 6 c ∧ DFiniteReduction.Nz 4 6 c :=
  no_sol_of_cert cert_4_6
theorem no_sol_5_5 : ¬ ∃ c, DFiniteReduction.Sol 5 5 c ∧ DFiniteReduction.Nz 5 5 c :=
  no_sol_of_cert cert_5_5
theorem no_sol_6_4 : ¬ ∃ c, DFiniteReduction.Sol 6 4 c ∧ DFiniteReduction.Nz 6 4 c :=
  no_sol_of_cert cert_6_4
theorem no_sol_7_3 : ¬ ∃ c, DFiniteReduction.Sol 7 3 c ∧ DFiniteReduction.Nz 7 3 c :=
  no_sol_of_cert cert_7_3
theorem no_sol_9_2 : ¬ ∃ c, DFiniteReduction.Sol 9 2 c ∧ DFiniteReduction.Nz 9 2 c :=
  no_sol_of_cert cert_9_2
theorem no_sol_13_1 : ¬ ∃ c, DFiniteReduction.Sol 13 1 c ∧ DFiniteReduction.Nz 13 1 c :=
  no_sol_of_cert cert_13_1
theorem no_sol_20_0 : ¬ ∃ c, DFiniteReduction.Sol 20 0 c ∧ DFiniteReduction.Nz 20 0 c :=
  no_sol_of_cert cert_20_0

/-! ### `prop:no-dfinite`, closed -/

theorem maximalPairs_no_sol : ∀ p ∈ DFiniteReduction.maximalPairs,
    ¬ ∃ c, DFiniteReduction.Sol p.1 p.2 c ∧ DFiniteReduction.Nz p.1 p.2 c := by
  intro p hp
  simp only [DFiniteReduction.maximalPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_sol_3_7
  · exact no_sol_4_6
  · exact no_sol_5_5
  · exact no_sol_6_4
  · exact no_sol_7_3
  · exact no_sol_9_2

/-- **`prop:no-dfinite`.**  On the `52` pairs of the over-determined grid `1 <= k <= 9`,
    `m <= 7`, `(k+1)(m+1) < 43-k`, the sequence `u_0, ..., u_42` satisfies no nonzero
    recurrence of order `k` with coefficient polynomials of degree `m`. -/
theorem no_dfinite (k m : ℕ) (hk : k < 10) (hm : m < 8)
    (hgrid : DFiniteReduction.onGrid k m = true) :
    ¬ ∃ c, DFiniteReduction.Sol k m c ∧ DFiniteReduction.Nz k m c :=
  DFiniteReduction.no_dfinite_of_maximal maximalPairs_no_sol k m hk hm hgrid

/-! ### The narrowed holonomic box -/

theorem box_bounds {k m : ℕ} (h : inBox k m = true) : k < 21 ∧ m < 32 := by
  simp only [inBox, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hg, hc⟩ := h
  have h1 : k + 1 ≤ (k + 1) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
  have h2 : m + 1 ≤ (k + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  rcases hc with ⟨_, hk9, hm7⟩ | h32
  · omega
  · omega

/-- **The narrowed exclusion box.**  Every over-determined cell of the union of the two
    searched regions, namely the `prop:no-dfinite` grid and the holonomic box
    `(k+1)(m+1) <= 32` of `prop:finite-horizon`(ii), admits no nonzero recurrence on
    `u_0, ..., u_42`.  The over-determination condition is not a convenience: without it a
    nonzero solution exists for every input sequence whatever, so an exclusion would be
    vacuous (`OverDetermination.exists_nonzero_solution`). -/
theorem no_recurrence_in_box (k m : ℕ) (h : inBox k m = true) :
    ¬ ∃ c, DFiniteReduction.Sol k m c ∧ DFiniteReduction.Nz k m c := by
  obtain ⟨hk, hm⟩ := box_bounds h
  have hcov := box_covered k hk m hm h
  rw [List.any_eq_true] at hcov
  obtain ⟨p, hp, hle⟩ := hcov
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  refine DFiniteReduction.no_sol_mono hle.1 hle.2 ?_
  simp only [maxCells, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_sol_0_31
  · exact no_sol_1_15
  · exact no_sol_2_9
  · exact no_sol_3_7
  · exact no_sol_4_6
  · exact no_sol_5_5
  · exact no_sol_6_4
  · exact no_sol_7_3
  · exact no_sol_9_2
  · exact no_sol_13_1
  · exact no_sol_20_0

/-! ### Axiom audit (Rule 5) -/

#print axioms u_eq
#print axioms modular_identity
#print axioms no_sol_of_cert
#print axioms maximalPairs_no_sol
#print axioms no_dfinite
#print axioms box_bounds
#print axioms no_recurrence_in_box

end NoDFiniteCertificates
