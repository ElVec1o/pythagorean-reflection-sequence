/-
**The assembly contract, repaired.**

`EltBridge.IsAssembly` (EltBridge.lean:10468) is the Lean form of `eq:assembly`.
BLOCK 340 proved that its *existential* closure carries no information:
`EltBridge.isAssembly_of_any` satisfies it for **arbitrary** `W` and `W0` with `n = 1`,
`T = X ^ 2`, `mu = 1` and `lam` chosen to hit the target, and
`EltBridge.isAssembly_of_any_order` shows the order-two side condition does not rescue
it.  So `exists n T lam mu, IsAssembly W W0 T lam mu` establishes nothing.

This file does three things.

* **Section 1 -- diagnosis.**  It isolates *which* feature is defective.  It is **not**
  the `k in range (N + 1)` truncation: `isAssemblyAll_of_any` proves the *untruncated*
  contract (the identity demanded at every cutoff `M >= N`, i.e. a genuine power-series
  identity) is satisfiable for arbitrary `W` and `W0` by the *same* witness.  De-truncating
  therefore restores nothing.  What is defective is the existential quantifier over
  `T, lam, mu`.  Naming them restores content in the strongest possible sense:
  `isAssembly_iff_eq_assemblyValue` shows that for **named** `T, lam, mu` the contract has
  exactly one solution `W`, so `exists_not_isAssembly` exhibits series that fail it.
  `assembly_trunc_stable` adds that once `T` is named with entries of positive order the
  truncation is pure bookkeeping -- the cutoff can be raised freely without changing any
  coefficient.

* **Section 2 -- a named transfer.**  Naming an *arbitrary* `T` is a formal repair: any
  predicate of the shape "`coeff N W = f N`" pins `W` down.  The mathematical content of
  `eq:assembly` is that the named `T` is *the transfer matrix of the site kernel*.  This
  section builds that transfer explicitly out of BLOCK 340's `EltBridge.maxM`: the ordered
  products `maxProd`, and the variation-of-parameters formula `vop` that solves the
  inhomogeneous chain in closed form.  Nothing here is existentially quantified.

* **Section 3 -- the contract, and the model satisfying it.**  `IsMaxAssembly q M W` is a
  scalar identity `W = maxAlpha q M + maxBeta q M * W` in which **both coefficients are
  named**, built from the ordered products of the site kernel's own transfer.
  `maxbulk_closure` proves that any solution `u` of the truncated `max`-kernel resolvent
  equations has generating constant `cS' q u M` satisfying it; over `PowerSeries Z` at
  `q = X`, `isMaxAssembly_existsUnique` proves the contract has **exactly one** solution;
  and `bulk_isMaxAssembly` constructs the truncated bulk model at every cutoff `M` (the
  finite system `(1 - K) u = 1`, invertible because every entry of `K` has positive
  order) and proves *it* satisfies the contract.  So `bulk_eq_of_isMaxAssembly` identifies
  the bulk generating constant with the unique solution of the named contract,
  unconditionally.  The contract is vacuous in neither direction: it is satisfiable by an
  object that exists, and it determines its subject.

**What is NOT claimed.**  `IsMaxAssembly` is a contract for the *bulk* `max`-kernel model
truncated at magnitude `M` -- no marker fibres, no `Fin 4` head/tail data, and no
`M -> infinity` limit (the cutoff is a parameter throughout; the limit is legitimate
because `maxM q a -> 1` coefficientwise, but it is not formalised).  It is **not** proved
for `EltBridge.W`.  Identifying `EltBridge.W` with the resolvent of the site kernel is
BLOCK 321's per-fibre resolvent problem and is untouched here.  Nor is BLOCK 340's
`q`-series closed form for the ordered products formalised: `maxProd` is defined by its
recursion, and the `k`-fold telescoping expansion over strictly decreasing chains remains
numerically validated only.  The advance is that the target is now a statement with
content rather than a vacuous existential, and that the bulk half of it is proved.

Cross-checked in exact arithmetic by `code/zeta_probe/tools/nogap/src/bin/assemblycontract.rs`:
`maxAlpha`/`maxBeta` solved against a raw double-sum solution of the truncated bulk system
at every cutoff `M <= 14` to degree 40, and reproducing BLOCK 340's tabulated
`T = 1, 2, 3, 10, 9, 30, 37, 82, ...`.
-/
import EltBridge
import Mathlib.RingTheory.PowerSeries.Inverse

namespace AssemblyContract

open EltBridge

/-! ## Section 1: what was wrong, and what fixes it -/

/-- The series the *named* data forces on `W`.  `IsAssembly` says nothing about `W`
except that it equals this. -/
noncomputable def assemblyValue {n : ℕ} (W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => PowerSeries.coeff N
    (W0 + ∑ md : Fin 4, ∑ k ∈ Finset.range (N + 1),
      ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b)

/-- **With `T`, `lam`, `mu` named, the contract pins `W` down completely.**  This is the
sharpest possible non-vacuity: the solution set is a singleton. -/
theorem isAssembly_iff_eq_assemblyValue {n : ℕ} (W W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) :
    IsAssembly W W0 T lam mu ↔ W = assemblyValue W0 T lam mu := by
  constructor
  · intro h
    refine PowerSeries.ext fun N => ?_
    rw [h N]
    simp only [assemblyValue, PowerSeries.coeff_mk]
  · intro h N
    rw [h]
    simp only [assemblyValue, PowerSeries.coeff_mk]

/-- **The named contract is satisfiable.** -/
theorem isAssembly_assemblyValue {n : ℕ} (W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) :
    IsAssembly (assemblyValue W0 T lam mu) W0 T lam mu :=
  (isAssembly_iff_eq_assemblyValue _ W0 T lam mu).mpr rfl

/-- **And it determines its subject.** -/
theorem isAssembly_unique {n : ℕ} (W W' W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ)
    (h : IsAssembly W W0 T lam mu) (h' : IsAssembly W' W0 T lam mu) : W = W' := by
  rw [(isAssembly_iff_eq_assemblyValue W W0 T lam mu).mp h,
    (isAssembly_iff_eq_assemblyValue W' W0 T lam mu).mp h']

/-- **So the analogue of `isAssembly_of_any` FAILS once `T`, `lam`, `mu` are named**:
for every named choice there are series that do not satisfy the contract. -/
theorem exists_not_isAssembly {n : ℕ} (W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) :
    ∃ W, ¬ IsAssembly W W0 T lam mu := by
  refine ⟨assemblyValue W0 T lam mu + 1, fun h => ?_⟩
  have heq := (isAssembly_iff_eq_assemblyValue _ W0 T lam mu).mp h
  have h1 : (1 : PowerSeries ℤ) = 0 := by linear_combination heq
  exact one_ne_zero h1

/-- The same, stated as the direct negation of `isAssembly_of_any`'s shape. -/
theorem not_forall_isAssembly {n : ℕ} (W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) :
    ¬ ∀ W, IsAssembly W W0 T lam mu := by
  obtain ⟨W, hW⟩ := exists_not_isAssembly W0 T lam mu
  exact fun h => hW (h W)

/-! ### De-truncating alone does NOT restore content

BLOCK 340's proof of `isAssembly_of_any` used the `range (N + 1)` cutoff, which invites
the guess that the repair is to demand the identity at every cutoff, i.e. as a genuine
power-series identity.  It is not: the very same witness works. -/

/-- The **untruncated** contract: the Neumann partial sums are required to agree with
`W - W0` at *every* cutoff `M >= N`, i.e. the identity is one of power series and not a
degree-by-degree accident. -/
def IsAssemblyAll {n : ℕ} (W W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) : Prop :=
  ∀ N M : ℕ, N ≤ M → PowerSeries.coeff N W
    = PowerSeries.coeff N
        (W0 + ∑ md : Fin 4, ∑ k ∈ Finset.range (M + 1),
          ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b)

/-- **Removing the truncation does not help.**  `IsAssemblyAll` is still satisfiable for
arbitrary `W` and `W0`, by BLOCK 340's own witness.  Hence the defect in `eq:assembly` is
the existential quantifier over `T`, `lam`, `mu`, not the cutoff. -/
theorem isAssemblyAll_of_any (W W0 : PowerSeries ℤ) :
    IsAssemblyAll W W0 (Matrix.of (fun _ _ : Fin 1 => (PowerSeries.X ^ 2 : PowerSeries ℤ)))
      (fun md _ => if md = 0 then (W - W0) * (1 - PowerSeries.X ^ 2) else 0)
      (fun _ _ => 1) := by
  intro N M hNM
  have hgeom : (∑ k ∈ Finset.range (M + 1), (PowerSeries.X ^ 2 : PowerSeries ℤ) ^ k)
      * (1 - PowerSeries.X ^ 2) = 1 - (PowerSeries.X ^ 2) ^ (M + 1) := geom_sum_mul_neg _ _
  have hpow : ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ (M + 1)
      = PowerSeries.X ^ (2 * (M + 1)) := by rw [← pow_mul]
  have inner : ∀ md : Fin 4,
      (∑ k ∈ Finset.range (M + 1), ∑ a : Fin 1, ∑ b : Fin 1,
        (if md = 0 then (W - W0) * (1 - PowerSeries.X ^ 2) else 0)
          * ((Matrix.of (fun _ _ : Fin 1 => (PowerSeries.X ^ 2 : PowerSeries ℤ))) ^ k) a b * 1)
      = if md = 0 then (W - W0) * (1 - PowerSeries.X ^ (2 * (M + 1))) else 0 := by
    intro md
    by_cases h : md = 0
    · simp only [Fin.sum_univ_one, mul_one, pow_apply_fin_one, h, if_pos]
      rw [← Finset.mul_sum, ← hpow, mul_assoc, mul_comm (1 - PowerSeries.X ^ 2), hgeom]
    · simp only [if_neg h, zero_mul, Finset.sum_const_zero]
  have hsum : (∑ md : Fin 4, ∑ k ∈ Finset.range (M + 1), ∑ a : Fin 1, ∑ b : Fin 1,
        (if md = 0 then (W - W0) * (1 - PowerSeries.X ^ 2) else 0)
          * ((Matrix.of (fun _ _ : Fin 1 => (PowerSeries.X ^ 2 : PowerSeries ℤ))) ^ k) a b * 1)
      = (W - W0) * (1 - PowerSeries.X ^ (2 * (M + 1))) := by
    rw [Finset.sum_congr rfl (fun md _ => inner md), Fin.sum_univ_four]
    simp
  have hcoeff : PowerSeries.coeff N ((W - W0) * PowerSeries.X ^ (2 * (M + 1))) = 0 := by
    rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
  have hfin : W0 + (W - W0) * (1 - PowerSeries.X ^ (2 * (M + 1)))
      = W - (W - W0) * PowerSeries.X ^ (2 * (M + 1)) := by ring
  show PowerSeries.coeff N W = PowerSeries.coeff N (W0 + _)
  rw [hsum, hfin, map_sub, hcoeff, sub_zero]

/-! ### With a named `T` of positive order the cutoff is bookkeeping -/

/-- Entries of `T ^ k` are divisible by `X ^ k` when the entries of `T` are divisible
by `X`. -/
theorem X_pow_dvd_pow_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (hT : ∀ a b, (PowerSeries.X : PowerSeries ℤ) ∣ T a b) :
    ∀ (k : ℕ) (a b : Fin n), (PowerSeries.X : PowerSeries ℤ) ^ k ∣ (T ^ k) a b := by
  intro k
  induction k with
  | zero => intro a b; simp
  | succ k ih =>
      intro a b
      have : (T ^ (k + 1)) a b = ∑ c : Fin n, (T ^ k) a c * T c b := by
        rw [pow_succ, Matrix.mul_apply]
      rw [this, pow_succ]
      exact Finset.dvd_sum fun c _ => mul_dvd_mul (ih a c) (hT c b)

/-- **Raising the cutoff changes no coefficient.**  So with `T` named and of positive
order, `IsAssembly` *is* the power-series identity `W - W0 = lam (1 - T)^{-1} mu`; the
truncation is not doing any work. -/
theorem assembly_trunc_stable {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ)
    (hT : ∀ a b, (PowerSeries.X : PowerSeries ℤ) ∣ T a b) (N M : ℕ) (hNM : N ≤ M) :
    PowerSeries.coeff N (∑ md : Fin 4, ∑ k ∈ Finset.range (N + 1),
        ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b)
      = PowerSeries.coeff N (∑ md : Fin 4, ∑ k ∈ Finset.range (M + 1),
        ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b) := by
  have hvanish : ∀ (k : ℕ), N < k → ∀ (md : Fin 4),
      PowerSeries.coeff N (∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b) = 0 := by
    intro k hk md
    rw [map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    obtain ⟨g, hg⟩ := X_pow_dvd_pow_apply T hT k a b
    have : lam md a * (T ^ k) a b * mu md b
        = (lam md a * g * mu md b) * PowerSeries.X ^ k := by rw [hg]; ring
    rw [this, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
  have hsplit : Finset.range (M + 1)
      = Finset.range (N + 1) ∪ Finset.Ico (N + 1) (M + 1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun md _ => ?_
  have hzero : PowerSeries.coeff N (∑ k ∈ Finset.Ico (N + 1) (M + 1),
      ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k hk =>
      hvanish k (by have := (Finset.mem_Ico.mp hk).1; omega) md
  rw [hsplit, Finset.sum_union (by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 (N + 1) (M + 1)), map_add, hzero, add_zero]

/-! ## Section 2: the named transfer of the site kernel

BLOCK 340 reduced the `max`-kernel resolvent to the two-dimensional chain
`(S a, S' a) = maxM q a *ᵥ (S (a-1), S' (a-1)) + src a`.  Here that chain is *solved*:
`maxProd` is the ordered product of transfers and `vop` is the discrete variation of
parameters.  All data below is explicitly constructed; nothing is quantified away. -/

section Chain

variable {R : Type*} [CommRing R]

/-- **The ordered product** `maxM q a * maxM q (a-1) * ... * maxM q (j+1)`: the transfer
from magnitude `j` up to magnitude `a`.  It is `1` when `a ≤ j`. -/
def maxProd (q : R) (j : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | a + 1 => if j ≤ a then maxM q (a + 1) * maxProd q j a else 1

@[simp] theorem maxProd_zero (q : R) (j : ℕ) : maxProd q j 0 = 1 := rfl

theorem maxProd_succ (q : R) (j a : ℕ) :
    maxProd q j (a + 1) = if j ≤ a then maxM q (a + 1) * maxProd q j a else 1 := rfl

theorem maxProd_succ_of_le (q : R) {j a : ℕ} (h : j ≤ a) :
    maxProd q j (a + 1) = maxM q (a + 1) * maxProd q j a := by
  rw [maxProd_succ, if_pos h]

theorem maxProd_succ_self (q : R) (a : ℕ) : maxProd q (a + 1) (a + 1) = 1 := by
  rw [maxProd_succ, if_neg (by omega)]

/-- **Discrete variation of parameters.**  A vector sequence obeying the chain step is
given in closed form by the ordered products applied to the initial vector and to each
source term.  This is what `maxM_det = 1` (BLOCK 340) makes possible, and it is the step
BLOCK 340 listed as not yet formalized. -/
theorem vop (q : R) (v s : ℕ → Fin 2 → R) (A : ℕ)
    (hstep : ∀ a, a + 1 ≤ A → v (a + 1) = (maxM q (a + 1)).mulVec (v a) + s (a + 1)) :
    ∀ a, a ≤ A → v a = (maxProd q 0 a).mulVec (v 0)
        + ∑ j ∈ Finset.range a, (maxProd q (j + 1) a).mulVec (s (j + 1)) := by
  intro a
  induction a with
  | zero => intro _; simp [Matrix.one_mulVec]
  | succ a ih =>
      intro hA
      have hIH := ih (by omega)
      have hsum : ∑ j ∈ Finset.range (a + 1), (maxProd q (j + 1) (a + 1)).mulVec (s (j + 1))
          = (maxM q (a + 1)).mulVec
              (∑ j ∈ Finset.range a, (maxProd q (j + 1) a).mulVec (s (j + 1)))
            + s (a + 1) := by
        rw [Finset.sum_range_succ, maxProd_succ_self, Matrix.one_mulVec, Matrix.mulVec_sum]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [maxProd_succ_of_le q (show j + 1 ≤ a from Finset.mem_range.mp hj),
          Matrix.mulVec_mulVec]
      rw [hstep a hA, hIH, maxProd_succ_of_le q (Nat.zero_le a), hsum,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
      abel

end Chain

/-! ## Section 3: the contract, and the bulk model that satisfies it -/

section Bulk

variable {R : Type*} [CommRing R]

/-- Sign-fibre multiplicity: magnitude `0` carries one sign, every other magnitude two. -/
def mm (b : ℕ) : R := if b = 0 then 1 else 2

@[simp] theorem mm_zero : (mm 0 : R) = 1 := rfl

theorem mm_succ (b : ℕ) : (mm (b + 1) : R) = 2 := by
  simp [mm]

/-- Cumulative sum `S a = sum_{b <= a} m b * u b`. -/
def cS (u : ℕ → R) (a : ℕ) : R := ∑ b ∈ Finset.range (a + 1), mm b * u b

/-- Cumulative sum `S' a = sum_{b <= a} m b * q ^ b * u b`.  Its value at the cutoff is
the global constant `T` of BLOCK 340 -- the bulk generating function. -/
def cS' (q : R) (u : ℕ → R) (a : ℕ) : R := ∑ b ∈ Finset.range (a + 1), mm b * q ^ b * u b

@[simp] theorem cS_zero (u : ℕ → R) : cS u 0 = u 0 := by simp [cS]

@[simp] theorem cS'_zero (q : R) (u : ℕ → R) : cS' q u 0 = u 0 := by simp [cS']

theorem cS_succ (u : ℕ → R) (a : ℕ) : cS u (a + 1) = cS u a + 2 * u (a + 1) := by
  rw [cS, cS, Finset.sum_range_succ, mm_succ]

theorem cS'_succ (q : R) (u : ℕ → R) (a : ℕ) :
    cS' q u (a + 1) = cS' q u a + 2 * q ^ (a + 1) * u (a + 1) := by
  rw [cS', cS', Finset.sum_range_succ, mm_succ]

/-- The source vector of the chain at magnitude `j`, exactly as `maxchain_transfer`
produces it. -/
def maxSrc (q Tc : R) (j : ℕ) : Fin 2 → R :=
  ![2 + 2 * q ^ j * Tc, 2 * q ^ j + 2 * q ^ j * q ^ j * Tc]

/-- The `Tc`-free part of the initial vector. -/
def maxInitA : Fin 2 → R := ![1, 1]

/-- The `Tc`-linear part of the initial vector. -/
def maxInitB (q : R) : Fin 2 → R := ![q ^ 2, q ^ 2]

/-- The `Tc`-free part of the source. -/
def maxSrcA (q : R) (j : ℕ) : Fin 2 → R := ![2, 2 * q ^ j]

/-- The `Tc`-linear part of the source. -/
def maxSrcB (q : R) (j : ℕ) : Fin 2 → R := ![2 * q ^ j, 2 * q ^ j * q ^ j]

theorem maxSrc_split (q Tc : R) (j : ℕ) :
    maxSrc q Tc j = maxSrcA q j + Tc • maxSrcB q j := by
  funext i
  fin_cases i <;>
    simp [maxSrc, maxSrcA, maxSrcB, smul_eq_mul] <;> ring

theorem init_split (q Tc u0 : R) (h : u0 = 1 + q ^ 2 * Tc) :
    (![u0, u0] : Fin 2 → R) = maxInitA + Tc • maxInitB q := by
  funext i
  fin_cases i <;>
    simp [maxInitA, maxInitB, smul_eq_mul, h] <;> ring

/-- **`alpha`**: the `Tc`-free part of the assembled bulk constant, an explicit ordered-product
expression in the site kernel's own transfer. -/
def maxAlpha (q : R) (M : ℕ) : R :=
  ((maxProd q 0 M).mulVec maxInitA
    + ∑ j ∈ Finset.range M, (maxProd q (j + 1) M).mulVec (maxSrcA q (j + 1))) 1

/-- **`beta`**: the `Tc`-linear part, likewise explicit. -/
def maxBeta (q : R) (M : ℕ) : R :=
  ((maxProd q 0 M).mulVec (maxInitB q)
    + ∑ j ∈ Finset.range M, (maxProd q (j + 1) M).mulVec (maxSrcB q (j + 1))) 1

/-- **The named bulk-assembly contract.**  Both `maxAlpha` and `maxBeta` are explicitly
constructed from the ordered products of `EltBridge.maxM`, the transfer of the site
kernel; nothing is existentially quantified.  Compare `EltBridge.IsAssembly`, whose
existential closure `isAssembly_of_any` shows is satisfied by every series. -/
def IsMaxAssembly (q : R) (M : ℕ) (W : R) : Prop :=
  W = maxAlpha q M + maxBeta q M * W

theorem isMaxAssembly_iff (q : R) (M : ℕ) (W : R) :
    IsMaxAssembly q M W ↔ W * (1 - maxBeta q M) = maxAlpha q M := by
  constructor
  · intro h
    have h' : W = maxAlpha q M + maxBeta q M * W := h
    linear_combination h'
  · intro h
    show W = maxAlpha q M + maxBeta q M * W
    linear_combination h

/-- **One chain step for the bulk model.**  `max_kernel_split` plus `maxchain_transfer`
(BLOCK 340), specialised to the cumulative sums. -/
theorem maxbulk_step (q : R) (u : ℕ → R) (M a : ℕ) (hM : a + 1 ≤ M)
    (hres : u (a + 1)
      = 1 + q ^ (a + 1) * ∑ b ∈ Finset.range (M + 1), mm b * q ^ max (a + 1) b * u b) :
    (![cS u (a + 1), cS' q u (a + 1)] : Fin 2 → R)
      = (maxM q (a + 1)).mulVec ![cS u a, cS' q u a] + maxSrc q (cS' q u M) (a + 1) := by
  have hsplit := max_kernel_split q mm u (a + 1) M (by omega)
  have hu : u (a + 1) = 1 + q ^ (a + 1)
      * (q ^ (a + 1) * cS u (a + 1) + cS' q u M - cS' q u (a + 1)) := by
    rw [hres, hsplit]; rw [cS, cS', cS']; ring
  have := maxchain_transfer q (a + 1) (cS u a) (cS' q u a) (cS u (a + 1)) (cS' q u (a + 1))
    (cS' q u M) (u (a + 1)) (cS_succ u a) (cS'_succ q u a) hu
  rw [← this, maxSrc]

/-- **The scalar closure.**  Any solution of the truncated `max`-kernel resolvent
equations has bulk generating constant satisfying the named contract. -/
theorem maxbulk_closure (q : R) (u : ℕ → R) (M : ℕ)
    (hres0 : u 0 = 1 + q ^ 2 * cS' q u M)
    (hres : ∀ a, a + 1 ≤ M → u (a + 1)
      = 1 + q ^ (a + 1) * ∑ b ∈ Finset.range (M + 1), mm b * q ^ max (a + 1) b * u b) :
    IsMaxAssembly q M (cS' q u M) := by
  have hvop := vop q (fun a => ![cS u a, cS' q u a]) (maxSrc q (cS' q u M)) M
    (fun a ha => maxbulk_step q u M a ha (hres a ha)) M le_rfl
  simp only [cS_zero, cS'_zero] at hvop
  rw [init_split q (cS' q u M) (u 0) hres0] at hvop
  have hcomp := congrFun hvop 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcomp
  rw [Matrix.mulVec_add, Matrix.mulVec_smul] at hcomp
  have hsrc : ∀ j ∈ Finset.range M,
      (maxProd q (j + 1) M).mulVec (maxSrc q (cS' q u M) (j + 1))
        = (maxProd q (j + 1) M).mulVec (maxSrcA q (j + 1))
          + cS' q u M • (maxProd q (j + 1) M).mulVec (maxSrcB q (j + 1)) := by
    intro j _
    rw [maxSrc_split, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [Finset.sum_congr rfl hsrc, Finset.sum_add_distrib, ← Finset.smul_sum] at hcomp
  show cS' q u M = maxAlpha q M + maxBeta q M * cS' q u M
  rw [maxAlpha, maxBeta]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hcomp ⊢
  linear_combination hcomp

end Bulk

/-! ### Non-vacuity of the named contract, over `PowerSeries Z` at `q = X`

The contract has **exactly one** solution.  So it is satisfiable (not vacuously false),
and it determines its subject (not vacuously true) -- the two failure modes the old
`IsAssembly` existential had. -/

section NonVacuity

theorem dvd_mulVec_apply {R : Type*} [CommRing R] {d : R}
    (P : Matrix (Fin 2) (Fin 2) R) (w : Fin 2 → R) (h : ∀ j, d ∣ w j) (i : Fin 2) :
    d ∣ (P.mulVec w) i := by
  have hexp : (P.mulVec w) i = ∑ j : Fin 2, P i j * w j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hexp]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (h j) _

/-- `beta` has zero constant term. -/
theorem X_dvd_maxBeta (M : ℕ) :
    (PowerSeries.X : PowerSeries ℤ) ∣ maxBeta (PowerSeries.X : PowerSeries ℤ) M := by
  have hInit : ∀ i : Fin 2,
      (PowerSeries.X : PowerSeries ℤ) ∣ maxInitB (PowerSeries.X : PowerSeries ℤ) i := by
    have hX2 : (PowerSeries.X : PowerSeries ℤ) ∣ PowerSeries.X ^ 2 :=
      ⟨PowerSeries.X, by ring⟩
    intro i; fin_cases i <;> simp [maxInitB]
  have hSrc : ∀ (j : ℕ) (i : Fin 2),
      (PowerSeries.X : PowerSeries ℤ) ∣ maxSrcB (PowerSeries.X : PowerSeries ℤ) (j + 1) i := by
    intro j i
    have hXj : (PowerSeries.X : PowerSeries ℤ) ∣ PowerSeries.X ^ (j + 1) :=
      ⟨PowerSeries.X ^ j, by ring⟩
    fin_cases i
    · simpa [maxSrcB] using hXj.mul_left 2
    · simpa [maxSrcB] using hXj.mul_left (2 * (PowerSeries.X : PowerSeries ℤ) ^ (j + 1))
  rw [maxBeta]
  simp only [Pi.add_apply, Finset.sum_apply]
  exact dvd_add (dvd_mulVec_apply _ _ hInit 1)
    (Finset.dvd_sum fun j _ => dvd_mulVec_apply _ _ (hSrc j) 1)

theorem constantCoeff_one_sub_maxBeta (M : ℕ) :
    PowerSeries.constantCoeff (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) = 1 := by
  have h0 : PowerSeries.constantCoeff (maxBeta (PowerSeries.X : PowerSeries ℤ) M) = 0 :=
    PowerSeries.X_dvd_iff.mp (X_dvd_maxBeta M)
  rw [map_sub, map_one, h0, sub_zero]

/-- **The contract is satisfiable.** -/
theorem isMaxAssembly_exists (M : ℕ) :
    ∃ W : PowerSeries ℤ, IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W := by
  refine ⟨maxAlpha (PowerSeries.X : PowerSeries ℤ) M
    * PowerSeries.invOfUnit (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1, ?_⟩
  rw [isMaxAssembly_iff]
  have hinv := PowerSeries.mul_invOfUnit
    (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1 (by
      simpa using constantCoeff_one_sub_maxBeta M)
  calc maxAlpha (PowerSeries.X : PowerSeries ℤ) M
        * PowerSeries.invOfUnit (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1
        * (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M)
      = maxAlpha (PowerSeries.X : PowerSeries ℤ) M
        * ((1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M)
          * PowerSeries.invOfUnit (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1) := by ring
    _ = maxAlpha (PowerSeries.X : PowerSeries ℤ) M := by rw [hinv, mul_one]

/-- **And it determines its subject.**  This is the property `EltBridge.IsAssembly`'s
existential closure fails to have. -/
theorem isMaxAssembly_unique (M : ℕ) (W W' : PowerSeries ℤ)
    (h : IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W)
    (h' : IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W') : W = W' := by
  rw [isMaxAssembly_iff] at h h'
  have hinv := PowerSeries.mul_invOfUnit
    (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1 (by
      simpa using constantCoeff_one_sub_maxBeta M)
  have hz : (W - W') * (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) = 0 := by
    rw [sub_mul, h, h', sub_self]
  have := congrArg
    (fun z => z * PowerSeries.invOfUnit (1 - maxBeta (PowerSeries.X : PowerSeries ℤ) M) 1) hz
  simp only [zero_mul, mul_assoc, hinv, mul_one] at this
  exact sub_eq_zero.mp this

/-- **Exactly one solution.** -/
theorem isMaxAssembly_existsUnique (M : ℕ) :
    ∃! W : PowerSeries ℤ, IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W := by
  obtain ⟨W, hW⟩ := isMaxAssembly_exists M
  exact ⟨W, hW, fun W' hW' => isMaxAssembly_unique M W' W hW' hW⟩

/-- **So the analogue of `isAssembly_of_any` FAILS for this contract**: there are series
that do not satisfy it.  Without this theorem the restatement would be no better than the
one it replaces. -/
theorem exists_not_isMaxAssembly (M : ℕ) :
    ∃ W : PowerSeries ℤ, ¬ IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W := by
  obtain ⟨W, hW⟩ := isMaxAssembly_exists M
  refine ⟨W + 1, fun h => ?_⟩
  have heq := isMaxAssembly_unique M (W + 1) W h hW
  have h1 : (1 : PowerSeries ℤ) = 0 := by linear_combination heq
  exact one_ne_zero h1

theorem not_forall_isMaxAssembly (M : ℕ) :
    ¬ ∀ W : PowerSeries ℤ, IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W := by
  obtain ⟨W, hW⟩ := exists_not_isMaxAssembly M
  exact fun h => hW (h W)

end NonVacuity

/-! ### The model is not empty: the truncated bulk model exists at every cutoff

The contract of Section 3 is proved for *solutions* of the truncated `max`-kernel
resolvent equations.  Those solutions exist: at cutoff `M` the equations are a finite
linear system `(1 - K) u = 1` over `PowerSeries Z` whose kernel matrix `K` has every entry
of positive order (the exponent `mu a` is `2` at `a = 0` and `a` otherwise, so never `0`),
hence `det (1 - K)` has constant term `1` and is a unit.  So `bulk_isMaxAssembly` below is
unconditional, and with `isMaxAssembly_unique` it identifies the bulk generating constant
with the unique solution of the named contract. -/

section ModelExists

/-- The site-kernel exponent: `mu 0 = 2` (the boundary deviation `m 0 = 1`, `mu 0 = 2` of
BLOCK 340) and `mu a = a` otherwise.  It is never zero, which is what makes the truncated
system invertible. -/
def muN (a : ℕ) : ℕ := if a = 0 then 2 else a

theorem muN_ne_zero (a : ℕ) : muN a ≠ 0 := by
  unfold muN; split <;> omega

/-- The truncated site-kernel matrix, `K a b = X ^ mu a * (m b * X ^ max a b)`. -/
noncomputable def kerMat (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ) :=
  Matrix.of fun a b =>
    (PowerSeries.X : PowerSeries ℤ) ^ muN (a : ℕ) * (mm (b : ℕ) * PowerSeries.X ^ max (a : ℕ) (b : ℕ))

theorem X_dvd_kerMat (M : ℕ) (a b : Fin (M + 1)) :
    (PowerSeries.X : PowerSeries ℤ) ∣ kerMat M a b :=
  Dvd.dvd.mul_right (dvd_pow_self _ (muN_ne_zero (a : ℕ))) _

theorem constantCoeff_det_one_sub (M : ℕ) :
    PowerSeries.constantCoeff (((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ))
      - kerMat M).det) = 1 := by
  rw [RingHom.map_det]
  have hmap : (PowerSeries.constantCoeff (R := ℤ)).mapMatrix
      ((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ)) - kerMat M) = 1 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub,
      PowerSeries.X_dvd_iff.mp (X_dvd_kerMat M a b), sub_zero]
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  rw [hmap, Matrix.det_one]

theorem isUnit_det_one_sub (M : ℕ) :
    IsUnit (((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ)) - kerMat M).det) := by
  refine isUnit_iff_exists_inv.mpr ⟨PowerSeries.invOfUnit
    (((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ)) - kerMat M).det) 1, ?_⟩
  exact PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_det_one_sub M)

/-- The solution vector of the truncated system. -/
noncomputable def bulkVec (M : ℕ) : Fin (M + 1) → PowerSeries ℤ :=
  ((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ)) - kerMat M)⁻¹.mulVec (fun _ => 1)

theorem bulkVec_res (M : ℕ) (a : Fin (M + 1)) :
    bulkVec M a = 1 + (kerMat M).mulVec (bulkVec M) a := by
  have h : ((1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (PowerSeries ℤ)) - kerMat M).mulVec
      (bulkVec M) = fun _ => (1 : PowerSeries ℤ) := by
    rw [bulkVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_det_one_sub M), Matrix.one_mulVec]
  have ha := congrFun h a
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at ha
  have : bulkVec M a - (kerMat M).mulVec (bulkVec M) a = 1 := ha
  linear_combination this

/-- The solution, read as a function on all magnitudes (zero above the cutoff). -/
noncomputable def bulkSol (M : ℕ) : ℕ → PowerSeries ℤ :=
  fun n => if h : n < M + 1 then bulkVec M ⟨n, h⟩ else 0

theorem bulkSol_of_lt (M n : ℕ) (h : n < M + 1) : bulkSol M n = bulkVec M ⟨n, h⟩ := dif_pos h

theorem bulkSol_apply (M : ℕ) (b : Fin (M + 1)) : bulkSol M (b : ℕ) = bulkVec M b := by
  rw [bulkSol_of_lt M (b : ℕ) b.isLt]

theorem bulk_sum_eq (M a : ℕ) :
    ∑ b ∈ Finset.range (M + 1),
        mm b * (PowerSeries.X : PowerSeries ℤ) ^ max a b * bulkSol M b
      = ∑ b : Fin (M + 1),
        mm (b : ℕ) * (PowerSeries.X : PowerSeries ℤ) ^ max a (b : ℕ) * bulkVec M b := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun b => mm b * (PowerSeries.X : PowerSeries ℤ) ^ max a b * bulkSol M b) (M + 1)]
  exact Finset.sum_congr rfl fun b _ => by rw [bulkSol_apply]

theorem kerMat_mulVec (M : ℕ) (a : Fin (M + 1)) :
    (kerMat M).mulVec (bulkVec M) a
      = (PowerSeries.X : PowerSeries ℤ) ^ muN (a : ℕ)
        * ∑ b : Fin (M + 1),
            mm (b : ℕ) * (PowerSeries.X : PowerSeries ℤ) ^ max (a : ℕ) (b : ℕ) * bulkVec M b := by
  have hexp : (kerMat M).mulVec (bulkVec M) a
      = ∑ b : Fin (M + 1), kerMat M a b * bulkVec M b := by
    simp [Matrix.mulVec, dotProduct]
  rw [hexp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [kerMat]; simp only [Matrix.of_apply]; ring

theorem bulkSol_res (M a : ℕ) (ha : a ≤ M) :
    bulkSol M a = 1 + (PowerSeries.X : PowerSeries ℤ) ^ muN a
      * ∑ b ∈ Finset.range (M + 1),
          mm b * (PowerSeries.X : PowerSeries ℤ) ^ max a b * bulkSol M b := by
  have hlt : a < M + 1 := by omega
  have h := bulkVec_res M ⟨a, hlt⟩
  rw [kerMat_mulVec] at h
  rw [bulk_sum_eq, bulkSol_of_lt M a hlt]
  exact h

/-- **The `a = 0` equation**, with the boundary deviation `mu 0 = 2`, `m 0 = 1`. -/
theorem bulkSol_res0 (M : ℕ) :
    bulkSol M 0 = 1 + (PowerSeries.X : PowerSeries ℤ) ^ 2
      * cS' PowerSeries.X (bulkSol M) M := by
  have h := bulkSol_res M 0 (Nat.zero_le M)
  rw [show muN 0 = 2 from rfl] at h
  have hsum : ∑ b ∈ Finset.range (M + 1),
      mm b * (PowerSeries.X : PowerSeries ℤ) ^ max 0 b * bulkSol M b
      = cS' PowerSeries.X (bulkSol M) M :=
    Finset.sum_congr rfl fun b _ => by rw [Nat.zero_max]
  rw [h, hsum]

/-- **The interior equations.** -/
theorem bulkSol_resa (M a : ℕ) (ha : a + 1 ≤ M) :
    bulkSol M (a + 1) = 1 + (PowerSeries.X : PowerSeries ℤ) ^ (a + 1)
      * ∑ b ∈ Finset.range (M + 1),
          mm b * (PowerSeries.X : PowerSeries ℤ) ^ max (a + 1) b * bulkSol M b := by
  have h := bulkSol_res M (a + 1) (by omega)
  rwa [show muN (a + 1) = a + 1 by simp [muN]] at h

/-- **The bulk model at every cutoff satisfies the named contract.**  Unconditional: the
model is constructed, not hypothesised. -/
theorem bulk_isMaxAssembly (M : ℕ) :
    IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M (cS' PowerSeries.X (bulkSol M) M) :=
  maxbulk_closure PowerSeries.X (bulkSol M) M (bulkSol_res0 M) (fun a ha => bulkSol_resa M a ha)

/-- **The punchline.**  The bulk generating constant of the truncated `max`-kernel model
is *the* solution of the named contract -- the value assembled by the ordered products of
the site kernel's own transfer matrix.  Contract and object agree, and the contract has no
other solution.

This is the bulk statement only: no marker fibres, and no claim about `EltBridge.W`. -/
theorem bulk_eq_of_isMaxAssembly (M : ℕ) (W : PowerSeries ℤ)
    (hW : IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W) :
    cS' PowerSeries.X (bulkSol M) M = W :=
  isMaxAssembly_unique M _ _ (bulk_isMaxAssembly M) hW

end ModelExists

end AssemblyContract

#print axioms AssemblyContract.isAssembly_iff_eq_assemblyValue
#print axioms AssemblyContract.isAssembly_assemblyValue
#print axioms AssemblyContract.isAssembly_unique
#print axioms AssemblyContract.exists_not_isAssembly
#print axioms AssemblyContract.not_forall_isAssembly
#print axioms AssemblyContract.isAssemblyAll_of_any
#print axioms AssemblyContract.X_pow_dvd_pow_apply
#print axioms AssemblyContract.assembly_trunc_stable
#print axioms AssemblyContract.maxProd_succ_of_le
#print axioms AssemblyContract.maxProd_succ_self
#print axioms AssemblyContract.vop
#print axioms AssemblyContract.maxSrc_split
#print axioms AssemblyContract.init_split
#print axioms AssemblyContract.isMaxAssembly_iff
#print axioms AssemblyContract.maxbulk_step
#print axioms AssemblyContract.maxbulk_closure
#print axioms AssemblyContract.dvd_mulVec_apply
#print axioms AssemblyContract.X_dvd_maxBeta
#print axioms AssemblyContract.constantCoeff_one_sub_maxBeta
#print axioms AssemblyContract.isMaxAssembly_exists
#print axioms AssemblyContract.isMaxAssembly_unique
#print axioms AssemblyContract.isMaxAssembly_existsUnique
#print axioms AssemblyContract.exists_not_isMaxAssembly
#print axioms AssemblyContract.not_forall_isMaxAssembly
#print axioms AssemblyContract.muN_ne_zero
#print axioms AssemblyContract.X_dvd_kerMat
#print axioms AssemblyContract.constantCoeff_det_one_sub
#print axioms AssemblyContract.isUnit_det_one_sub
#print axioms AssemblyContract.bulkVec_res
#print axioms AssemblyContract.bulkSol_of_lt
#print axioms AssemblyContract.bulkSol_apply
#print axioms AssemblyContract.bulk_sum_eq
#print axioms AssemblyContract.kerMat_mulVec
#print axioms AssemblyContract.bulkSol_res
#print axioms AssemblyContract.bulkSol_res0
#print axioms AssemblyContract.bulkSol_resa
#print axioms AssemblyContract.bulk_isMaxAssembly
#print axioms AssemblyContract.bulk_eq_of_isMaxAssembly
