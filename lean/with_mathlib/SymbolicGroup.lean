/-
SymbolicGroup.lean
==================
The generic group `W_gen` in the symbolic model of `lem:symbolic-form` (`paper1.tex`):
associativity of the composition law, the translation lattice
`T = {P : (1,0,0,P) ∈ W_gen} = 2(t-1) Z[t^{±1}]` (`thm:translation-lattice`), and the membership
characterisation of `thm:normal-form`.  Here `W_gen` is the set of symbolic data `wd w` of words.
No sorry.
-/
import SymbolicForm

namespace SymbolicGroup

open SymbolicForm Finsupp

theorem mulD_assoc (g h w : Sym) : mulD (mulD g h) w = mulD g (mulD h w) := by
  rcases g with ⟨eg, dg, kg, Pg⟩
  rcases h with ⟨eh, dh, kh, Ph⟩
  rcases w with ⟨ew, dw, kw, Pw⟩
  have hP : ∀ j, ((mulD (mulD ⟨eg, dg, kg, Pg⟩ ⟨eh, dh, kh, Ph⟩) ⟨ew, dw, kw, Pw⟩).P) j =
      ((mulD ⟨eg, dg, kg, Pg⟩ (mulD ⟨eh, dh, kh, Ph⟩ ⟨ew, dw, kw, Pw⟩)).P) j := by
    intro j
    simp only [mulD, Finsupp.add_apply, Finsupp.smul_apply, sh_apply, comb_apply, smul_eq_mul]
    cases dg <;> cases dh <;> cases dw <;> simp <;> ring_nf
  have hk : (mulD (mulD ⟨eg, dg, kg, Pg⟩ ⟨eh, dh, kh, Ph⟩) ⟨ew, dw, kw, Pw⟩).k =
      (mulD ⟨eg, dg, kg, Pg⟩ (mulD ⟨eh, dh, kh, Ph⟩ ⟨ew, dw, kw, Pw⟩)).k := by
    simp only [mulD]
    cases dg <;> cases dh <;> cases dw <;> simp <;> ring
  have hPeq : (mulD (mulD ⟨eg, dg, kg, Pg⟩ ⟨eh, dh, kh, Ph⟩) ⟨ew, dw, kw, Pw⟩).P =
      (mulD ⟨eg, dg, kg, Pg⟩ (mulD ⟨eh, dh, kh, Ph⟩ ⟨ew, dw, kw, Pw⟩)).P :=
    Finsupp.ext hP
  simp only [mulD] at hk hPeq ⊢
  congr 1
  · ring
  · cases dg <;> cases dh <;> cases dw <;> rfl

/-- The identity datum. -/
def one : Sym := ⟨1, false, 0, 0⟩

theorem sh_zero_shift (P : ℤ →₀ ℤ) : sh 0 P = P := by
  ext j; rw [sh_apply]; simp

theorem sh_zero (k : ℤ) : sh k (0 : ℤ →₀ ℤ) = 0 := by
  ext j; rw [sh_apply]; simp

theorem comb_zero (δ : Bool) : comb δ (0 : ℤ →₀ ℤ) = 0 := by
  ext j; rw [comb_apply]; split_ifs <;> simp

theorem mulD_one (g : Sym) : mulD g one = g := by
  rcases g with ⟨e, d, k, P⟩
  simp only [mulD, one]
  have : P + e • sh k (comb d (0 : ℤ →₀ ℤ)) = P := by
    rw [comb_zero, sh_zero]; simp
  cases d <;> simp [this]

theorem one_mulD (w : Sym) : mulD one w = w := by
  rcases w with ⟨e, d, k, P⟩
  have h1 : comb false P = P := by simp [comb]
  simp only [mulD, one]
  congr 1 <;> simp [h1, sh_zero_shift]

theorem wd_append (w1 w2 : List Gen) : wd (w1 ++ w2) = mulD (wd w1) (wd w2) := by
  induction w1 with
  | nil =>
    simp only [List.nil_append, wd]
    exact (one_mulD _).symm
  | cons g w ih =>
    simp only [List.cons_append, wd, ih, mulD_assoc]

theorem wd_single (g : Gen) : wd [g] = gd g := by
  show mulD (gd g) one = gd g
  exact mulD_one _

theorem wd_cons (g : Gen) (w : List Gen) : wd (g :: w) = mulD (gd g) (wd w) := rfl

theorem wd_conj (g : Gen) (w : List Gen) :
    wd (g :: (w ++ [g])) = mulD (gd g) (mulD (wd w) (gd g)) := by
  rw [wd_cons, wd_append, wd_single]

/-- `W_gen`: symbolic data of words. -/
def WGen : Set Sym := {d | ∃ w : List Gen, wd w = d}

/-- Pure translations: `P` with `(1, false, 0, P) ∈ W_gen`. -/
def IsT (P : ℤ →₀ ℤ) : Prop := (⟨1, false, 0, P⟩ : Sym) ∈ WGen

theorem WGen_mul {d d' : Sym} (h : d ∈ WGen) (h' : d' ∈ WGen) : mulD d d' ∈ WGen := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w ++ w', wd_append w w'⟩

theorem IsT_zero : IsT 0 := ⟨[], rfl⟩

theorem IsT_add {P Q : ℤ →₀ ℤ} (hP : IsT P) (hQ : IsT Q) : IsT (P + Q) := by
  have := WGen_mul hP hQ
  have e : mulD (⟨1, false, 0, P⟩ : Sym) ⟨1, false, 0, Q⟩ = ⟨1, false, 0, P + Q⟩ := by
    simp [mulD, comb, sh_zero_shift]
  rw [e] at this; exact this

theorem rf_rf (P : ℤ →₀ ℤ) : rf (rf P) = P := by
  ext j; rw [rf_apply, rf_apply]; simp

theorem IsT_refl {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (rf P) := by
  obtain ⟨w, hw⟩ := hP
  refine ⟨Gen.x :: (w ++ [Gen.x]), ?_⟩
  rw [wd_conj, hw]
  have e : mulD (gd Gen.x) (mulD (⟨1, false, 0, P⟩ : Sym) (gd Gen.x)) = ⟨1, false, 0, rf P⟩ := by
    simp [gd, mulD, comb, sh_zero_shift, comb_zero, sh_zero]
  exact e

theorem IsT_conjy {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (-(rf P)) := by
  obtain ⟨w, hw⟩ := hP
  refine ⟨Gen.y :: (w ++ [Gen.y]), ?_⟩
  rw [wd_conj, hw]
  have e : mulD (gd Gen.y) (mulD (⟨1, false, 0, P⟩ : Sym) (gd Gen.y)) =
      ⟨1, false, 0, -(rf P)⟩ := by
    simp [gd, mulD, comb, sh_zero_shift, comb_zero, sh_zero]
  exact e

theorem IsT_neg {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (-P) := by
  have h1 := IsT_refl hP
  have h2 := IsT_conjy h1
  rwa [rf_rf] at h2

/-- `1 - t^{-1}`, the translation polynomial of `R_h`. -/
noncomputable def gP : ℤ →₀ ℤ := Finsupp.single 0 1 + (-1 : ℤ) • Finsupp.single (-1) 1

theorem gd_x : gd Gen.x = ⟨1, true, 0, 0⟩ := rfl
theorem gd_y : gd Gen.y = ⟨-1, true, 0, 0⟩ := rfl
theorem gd_h : gd Gen.h = ⟨1, true, -1, gP⟩ := rfl

theorem gP_apply (j : ℤ) : gP j = (if (0 : ℤ) = j then 1 else 0) - (if (-1 : ℤ) = j then 1 else 0) :=
  gh_apply j

theorem sh_add (k : ℤ) (P Q : ℤ →₀ ℤ) : sh k (P + Q) = sh k P + sh k Q := by
  ext j; simp only [sh_apply, Finsupp.add_apply]

theorem sh_neg1_rf_gP : sh (-1) (rf gP) = -gP := by
  ext j
  rw [sh_apply, rf_apply, gP_apply, Finsupp.neg_apply, gP_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem sh_one_gP : sh 1 gP = -(rf gP) := by
  ext j
  rw [sh_apply, gP_apply, Finsupp.neg_apply, rf_apply, gP_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem rf_zero : rf (0 : ℤ →₀ ℤ) = 0 := by ext j; rw [rf_apply]; simp

theorem comb_true (P : ℤ →₀ ℤ) : comb true P = rf P := by simp [comb]
theorem comb_false (P : ℤ →₀ ℤ) : comb false P = P := by simp [comb]

theorem wd_hx : wd [Gen.h, Gen.x] = ⟨1, false, -1, gP⟩ := by
  rw [wd_cons, wd_single, gd_h, gd_x]
  simp only [mulD, comb_true, comb_zero, sh_zero]
  simp [rf]

theorem wd_xh : wd [Gen.x, Gen.h] = ⟨1, false, 1, rf gP⟩ := by
  rw [wd_cons, wd_single, gd_h, gd_x]
  simp only [mulD, comb_true, sh_zero_shift]
  simp

theorem IsT_shift_down {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (sh (-1) P) := by
  obtain ⟨w, hw⟩ := hP
  refine ⟨[Gen.h, Gen.x] ++ (w ++ [Gen.x, Gen.h]), ?_⟩
  rw [wd_append, wd_append, hw, wd_hx, wd_xh]
  simp only [mulD, comb_false, sh_zero_shift, one_smul, sh_add, sh_neg1_rf_gP]
  congr 1 <;> first | norm_num | (simp; abel)

theorem IsT_shift_up {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (sh 1 P) := by
  obtain ⟨w, hw⟩ := hP
  refine ⟨[Gen.x, Gen.h] ++ (w ++ [Gen.h, Gen.x]), ?_⟩
  rw [wd_append, wd_append, hw, wd_hx, wd_xh]
  simp only [mulD, comb_false, sh_zero_shift, one_smul, sh_add, sh_one_gP]
  congr 1 <;> first | norm_num | (simp; abel)

theorem IsT_shift {P : ℤ →₀ ℤ} (hP : IsT P) (m : ℤ) : IsT (sh m P) := by
  induction m using Int.induction_on with
  | zero => rw [sh_zero_shift]; exact hP
  | succ i ih =>
    have : sh ((i : ℤ) + 1) P = sh 1 (sh (i : ℤ) P) := by
      ext j; simp only [sh_apply]; congr 1; ring
    rw [this]; exact IsT_shift_up ih
  | pred i ih =>
    have : sh (-(i : ℤ) - 1) P = sh (-1) (sh (-(i : ℤ)) P) := by
      ext j; simp only [sh_apply]; congr 1; ring
    rw [this]; exact IsT_shift_down ih

theorem IsT_smul {P : ℤ →₀ ℤ} (hP : IsT P) (c : ℤ) : IsT (c • P) := by
  induction c using Int.induction_on with
  | zero => simpa using IsT_zero
  | succ i ih =>
    have : ((i : ℤ) + 1) • P = (i : ℤ) • P + P := by rw [add_smul, one_smul]
    rw [this]; exact IsT_add ih hP
  | pred i ih =>
    have : (-(i : ℤ) - 1) • P = (-(i : ℤ)) • P + (-P) := by
      rw [sub_eq_add_neg, add_smul, neg_one_smul]
    rw [this]; exact IsT_add ih (IsT_neg hP)

/-- The glide-square word `R_h R_y R_x R_h R_y R_x`, a pure translation by `2(1 - t^{-1})`. -/
theorem IsT_two_gP : IsT ((2 : ℤ) • gP) := by
  refine ⟨[Gen.h, Gen.y, Gen.x] ++ [Gen.h, Gen.y, Gen.x], ?_⟩
  rw [wd_append]
  have hA : wd [Gen.h, Gen.y, Gen.x] = ⟨-1, true, -1, gP⟩ := by
    rw [wd_cons, wd_cons, wd_single, gd_h, gd_y, gd_x]
    simp [mulD, comb_true, comb_false, sh_zero, rf_zero, sh_zero_shift, comb_zero]
  rw [hA]
  have hP : gP + -sh (-1) (rf gP) = (2 : ℤ) • gP := by
    rw [sh_neg1_rf_gP]; module
  simp only [mulD, comb_true]
  norm_num
  exact hP

theorem IsT_shift_two_gP (m : ℤ) : IsT ((2 : ℤ) • (Finsupp.single m 1 - Finsupp.single (m - 1) 1)) := by
  have h := IsT_shift IsT_two_gP m
  convert h using 1
  ext j
  simp only [sh_apply, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply, smul_eq_mul,
    gP_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem IsT_Q (m : ℤ) : IsT ((2 : ℤ) • (Finsupp.single m 1 - Finsupp.single 0 1)) := by
  induction m using Int.induction_on with
  | zero => simpa using IsT_zero
  | succ i ih =>
    have h := IsT_add ih (IsT_shift_two_gP ((i : ℤ) + 1))
    convert h using 1
    simp only [add_sub_cancel_right]
    rw [← smul_add]; congr 1; abel
  | pred i ih =>
    have h := IsT_add ih (IsT_neg (IsT_shift_two_gP (-(i : ℤ))))
    convert h using 1
    module

theorem tot_zero : tot (0 : ℤ →₀ ℤ) = 0 := by unfold tot; simp

theorem tot_single' (j c : ℤ) : tot (Finsupp.single j c) = c := tot_single j c

/-- Every `2 (P' - P'(1))` is a translation of `W_gen`. -/
theorem IsT_two_normalised (P' : ℤ →₀ ℤ) :
    IsT ((2 : ℤ) • (P' - tot P' • Finsupp.single 0 1)) := by
  induction P' using Finsupp.induction_linear with
  | zero => simpa [tot_zero] using IsT_zero
  | add P Q hP hQ =>
    have h := IsT_add hP hQ
    convert h using 1
    rw [tot_add, add_smul]; module
  | single j c =>
    have h := IsT_smul (IsT_Q j) c
    convert h using 1
    rw [tot_single']
    ext i
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> first | ring | (exfalso; omega) | simp_all

/-- **The translation lattice (`thm:translation-lattice`)** in the symbolic model:
a pure translation with polynomial `P` lies in `W_gen` iff `P(1) = 0` and every coefficient is even,
i.e. iff `P ∈ 2(t-1) Z[t^{±1}]`. -/
theorem IsT_iff (P : ℤ →₀ ℤ) : IsT P ↔ tot P = 0 ∧ ∀ j, (2 : ℤ) ∣ P j := by
  constructor
  · rintro ⟨w, hw⟩
    have hP : (wd w).P = P := by rw [hw]
    have hk : (wd w).k = 0 := by rw [hw]
    have b := Bd_wd w
    refine ⟨?_, fun j => ?_⟩
    · rw [← hP]; exact b.2.2.2.2
    · have p := Par_wd w j
      rw [hk, hP] at p
      have : ((P j : ℤ) : ZMod 2) = 0 := by
        rw [p]; split_ifs <;> decide
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this
  · rintro ⟨htot, hev⟩
    let P' : ℤ →₀ ℤ := Finsupp.mapRange (fun x => x / 2) (by simp) P
    have hP' : (2 : ℤ) • P' = P := by
      ext j
      simp only [Finsupp.smul_apply, smul_eq_mul, P', Finsupp.mapRange_apply]
      exact Int.mul_ediv_cancel' (hev j)
    have htot' : tot P' = 0 := by
      have : tot ((2 : ℤ) • P') = 2 * tot P' := tot_smul 2 P'
      rw [hP', htot] at this; omega
    have := IsT_two_normalised P'
    rw [htot'] at this
    simpa [hP'] using this

/-- Ideal form of the lattice: `(t-1) Q` has total coefficient `0`. -/
theorem IsT_ideal (Q : ℤ →₀ ℤ) : IsT ((2 : ℤ) • (sh 1 Q - Q)) := by
  rw [IsT_iff]
  refine ⟨?_, fun j => ?_⟩
  · rw [tot_smul]
    have : tot (sh 1 Q - Q + Q) = tot (sh 1 Q - Q) + tot Q := tot_add _ _
    rw [sub_add_cancel, tot_sh] at this
    have h0 : tot (sh 1 Q - Q) = 0 := by omega
    rw [h0]; simp
  · simp

theorem comb_comb (δ : Bool) (P : ℤ →₀ ℤ) : comb δ (comb δ P) = P := by
  cases δ <;> simp [comb_true, comb_false, rf_rf]

theorem sh_sh (a b : ℤ) (P : ℤ →₀ ℤ) : sh a (sh b P) = sh (a + b) P := by
  ext j; simp only [sh_apply]; congr 1; ring

/-- Rotations `(R_h R_x)^m`. -/
def rotW : ℕ → List Gen
  | 0 => []
  | (m + 1) => [Gen.h, Gen.x] ++ rotW m

/-- Inverse rotations `(R_x R_h)^m`. -/
def rotInvW : ℕ → List Gen
  | 0 => []
  | (m + 1) => [Gen.x, Gen.h] ++ rotInvW m

theorem wd_rotW (m : ℕ) :
    (wd (rotW m)).ε = 1 ∧ (wd (rotW m)).δ = false ∧ (wd (rotW m)).k = -(m : ℤ) := by
  induction m with
  | zero => simp [rotW, wd]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [rotW, wd_append, wd_hx, mulD, h1, h2, h3]
    refine ⟨by simp, by simp, ?_⟩
    simp

theorem wd_rotInvW (m : ℕ) :
    (wd (rotInvW m)).ε = 1 ∧ (wd (rotInvW m)).δ = false ∧ (wd (rotInvW m)).k = (m : ℤ) := by
  induction m with
  | zero => simp [rotInvW, wd]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [rotInvW, wd_append, wd_xh, mulD, h1, h2, h3]
    refine ⟨by simp, by simp, ?_⟩
    simp; ring

theorem exists_base (k : ℤ) : ∃ w : List Gen, (wd w).ε = 1 ∧ (wd w).δ = false ∧ (wd w).k = k := by
  rcases le_or_gt 0 k with hk | hk
  · refine ⟨rotInvW k.toNat, ?_⟩
    obtain ⟨h1, h2, h3⟩ := wd_rotInvW k.toNat
    exact ⟨h1, h2, by rw [h3]; exact Int.toNat_of_nonneg hk⟩
  · refine ⟨rotW (-k).toNat, ?_⟩
    obtain ⟨h1, h2, h3⟩ := wd_rotW (-k).toNat
    refine ⟨h1, h2, ?_⟩
    rw [h3, Int.toNat_of_nonneg (by omega)]; ring

theorem wd_cons_x (w : List Gen) :
    (wd (Gen.x :: w)).ε = (wd w).ε ∧ (wd (Gen.x :: w)).δ = !(wd w).δ ∧
      (wd (Gen.x :: w)).k = -(wd w).k := by
  rw [wd_cons, gd_x]; simp [mulD]

theorem wd_cons_y (w : List Gen) :
    (wd (Gen.y :: w)).ε = -(wd w).ε ∧ (wd (Gen.y :: w)).δ = !(wd w).δ ∧
      (wd (Gen.y :: w)).k = -(wd w).k := by
  rw [wd_cons, gd_y]; simp [mulD]

/-- Every symbolic class `(ε, δ, k)` is realised by a word. -/
theorem exists_class (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (δ : Bool) (k : ℤ) :
    ∃ w : List Gen, (wd w).ε = ε ∧ (wd w).δ = δ ∧ (wd w).k = k := by
  rcases hε with rfl | rfl <;> cases δ
  · obtain ⟨w, h1, h2, h3⟩ := exists_base k
    exact ⟨w, h1, h2, h3⟩
  · obtain ⟨w, h1, h2, h3⟩ := exists_base (-k)
    refine ⟨Gen.x :: w, ?_⟩
    obtain ⟨a, b, c⟩ := wd_cons_x w
    refine ⟨by rw [a, h1], by rw [b, h2]; rfl, by rw [c, h3]; ring⟩
  · obtain ⟨w, h1, h2, h3⟩ := exists_base k
    refine ⟨Gen.x :: Gen.y :: w, ?_⟩
    obtain ⟨a, b, c⟩ := wd_cons_y w
    obtain ⟨a', b', c'⟩ := wd_cons_x (Gen.y :: w)
    refine ⟨by rw [a', a, h1], by rw [b', b, h2]; rfl, by rw [c', c, h3]; ring⟩
  · obtain ⟨w, h1, h2, h3⟩ := exists_base (-k)
    refine ⟨Gen.y :: w, ?_⟩
    obtain ⟨a, b, c⟩ := wd_cons_y w
    refine ⟨by rw [a, h1], by rw [b, h2]; rfl, by rw [c, h3]; ring⟩

/-- The mod-2 class `P ≡ 1 + t^k` (equivalently `(1+t)(1+...+t^{|k|-1}) t^{min(k,0)}`). -/
def ParT (k : ℤ) (P : ℤ →₀ ℤ) : Prop :=
  ∀ j : ℤ, ((P j : ℤ) : ZMod 2) = (if j = 0 then 1 else 0) + (if j = k then 1 else 0)

theorem IsT_comb {δ : Bool} {P : ℤ →₀ ℤ} (hP : IsT P) : IsT (comb δ P) := by
  cases δ
  · rwa [comb_false]
  · rw [comb_true]; exact IsT_refl hP

/-- **`thm:normal-form` (membership).**  A symbolic tuple `(ε, δ, k, P)` lies in `W_gen` iff
`ε = ±1`, `P(1) = 0`, and `P ≡ 1 + t^k (mod 2)` (the dihedral cocycle, which depends only on `k`).
So the word and membership problems for `W_gen` are solved explicitly. -/
theorem normal_form_iff (ε : ℤ) (δ : Bool) (k : ℤ) (P : ℤ →₀ ℤ) :
    (⟨ε, δ, k, P⟩ : Sym) ∈ WGen ↔ (ε = 1 ∨ ε = -1) ∧ tot P = 0 ∧ ParT k P := by
  constructor
  · rintro ⟨w, hw⟩
    have hε : (wd w).ε = ε := by rw [hw]
    have hk : (wd w).k = k := by rw [hw]
    have hP : (wd w).P = P := by rw [hw]
    have b := Bd_wd w
    refine ⟨hε ▸ b.1, ?_, fun j => ?_⟩
    · rw [← hP]; exact b.2.2.2.2
    · have p := Par_wd w j
      rw [hk, hP] at p
      exact p
  · rintro ⟨hε, htot, hpar⟩
    obtain ⟨w₀, h1, h2, h3⟩ := exists_class ε hε δ k
    obtain ⟨P₀, hd₀⟩ : ∃ P₀, wd w₀ = ⟨ε, δ, k, P₀⟩ :=
      ⟨(wd w₀).P, by rcases hw : wd w₀ with ⟨a, b, c, d⟩; rw [hw] at h1 h2 h3;
                     simp only at h1 h2 h3; subst h1; subst h2; subst h3; rfl⟩
    have b0 := Bd_wd w₀
    have p0 := Par_wd w₀
    rw [hd₀] at b0 p0
    obtain ⟨-, -, -, -, ht0⟩ := b0
    simp only at ht0
    -- the difference `R = P - P₀` is a pure translation
    obtain ⟨R, hR⟩ : ∃ R, R = P - P₀ := ⟨_, rfl⟩
    have htR : tot R = 0 := by
      have : tot (P - P₀ + P₀) = tot (P - P₀) + tot P₀ := tot_add _ _
      rw [sub_add_cancel] at this
      rw [hR]; omega
    have hevR : ∀ j, (2 : ℤ) ∣ R j := by
      intro j
      have : ((R j : ℤ) : ZMod 2) = 0 := by
        simp only [hR, Finsupp.sub_apply]; push_cast
        rw [hpar j, p0 j]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this
    have hTR : IsT R := (IsT_iff R).mpr ⟨htR, hevR⟩
    -- choose the translation `Q` to append so that `ε t^k Q^δ = R`
    set Q : ℤ →₀ ℤ := comb δ (sh (-k) (ε • R)) with hQ
    have hTQ : IsT Q := IsT_comb (IsT_shift (IsT_smul hTR ε) (-k))
    obtain ⟨u, hu⟩ := hTQ
    refine ⟨w₀ ++ u, ?_⟩
    rw [wd_append, hd₀, hu]
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hkey : ε • sh k (comb δ Q) = R := by
      rw [hQ, comb_comb, sh_sh, show k + -k = 0 by ring, sh_zero_shift, smul_smul, hε2, one_smul]
    simp only [mulD]
    congr 1
    · ring
    · cases δ <;> simp
    · cases δ <;> simp
    · rw [hkey, hR]; simp

/-! ### the edge lamplighter: right multiplication by the generators -/

theorem mulD_gd_x (ε : ℤ) (δ : Bool) (k : ℤ) (P : ℤ →₀ ℤ) :
    mulD ⟨ε, δ, k, P⟩ (gd Gen.x) = ⟨ε, !δ, k, P⟩ := by
  rw [gd_x]; cases δ <;> simp [mulD, comb_zero, sh_zero]

theorem mulD_gd_y (ε : ℤ) (δ : Bool) (k : ℤ) (P : ℤ →₀ ℤ) :
    mulD ⟨ε, δ, k, P⟩ (gd Gen.y) = ⟨-ε, !δ, k, P⟩ := by
  rw [gd_y]; cases δ <;> simp [mulD, comb_zero, sh_zero]

/-- `R_h` moves the walker one site (down if `δ = 0`, up if `δ = 1`), flips `δ`, and deposits
`ε t^k (1 - t^{-1})` (if `δ = 0`) resp. `ε t^k (1 - t)` (if `δ = 1`) on the traversed edge. -/
theorem mulD_gd_h (ε : ℤ) (δ : Bool) (k : ℤ) (P : ℤ →₀ ℤ) :
    mulD ⟨ε, δ, k, P⟩ (gd Gen.h) =
      ⟨ε, !δ, k + (if δ then 1 else -1), P + ε • sh k (comb δ gP)⟩ := by
  rw [gd_h]; cases δ <;> simp [mulD]

end SymbolicGroup

#print axioms SymbolicGroup.mulD_gd_h
