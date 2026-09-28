/-
  Paper4TierA.lean
  ================
  Tier-A formalization-debt paydown, batch continuing `Paper1TierA.lean` /
  `Paper1TierACensus.lean` / `Paper1TierB1.lean` / `MergedNovelTierA.lean`. This batch covers
  three labels from `paper/journal/paper4.tex`: `lem:kernel`, `cor:single`, `cor:cancel`.

  ## `lem:kernel` — PROVED (the algebraic identity)

  The paper's proof of Lemma `lem:kernel` (paper4.tex ~L359) turns on one word identity:
  modulo the relations `x_i^2 = 1`,

      x0 x1 x2 x0 x1 x2 = (x0 x1)(x0 x2)^{-1}(x0 x1)^{-1}(x0 x2) = rho_1 rho_2^{-1} rho_1^{-1} rho_2.

  This is exactly the content of `paper4_lem_kernel` below: a genuine identity in an arbitrary
  group, given three involutions `x0 x1 x2 : G`. It is proved by substituting `x_i^{-1} = x_i`
  (from the involution hypotheses) and cancelling, matching the paper's one-line computation.

  The lemma's "consequently" clause — that `ker(F -> P-hat)` is the *normal closure* of `w_6`,
  and that the flows of its elements form the Z-span of the flows of conjugates of `w_6^{+-1}`
  — is a statement about a group presentation (a kernel-of-quotient-map identification) and is
  NOT covered here: it needs a Lean model of the free product `P-hat` and its presentation,
  which does not exist in this repo. Only the word identity that the proof's first sentence
  establishes is formalized.

  ## `cor:cancel` — PROVED (the per-edge algebraic identity + the finite-sum form)

  Corollary `cor:cancel` (paper4.tex ~L627) states, for a finitely supported integer
  configuration `c` on the sites,

      ||phi(c)||_1 = 6 * sum_s |c_s| - 2 * sum_{{u,v} hex-adjacent, same sign} min(|c_u|,|c_v|).

  Its one-paragraph proof reduces to the per-edge identity: on the edge between adjacent sites
  `u,v`,

      |c_u - c_v| = |c_u| + |c_v|                          if signs differ or one vanishes,
      |c_u - c_v| = |c_u| + |c_v| - 2 min(|c_u|,|c_v|)      if signs agree,

  summed over the six edges at each site and halved for the double count. `edge_cancel` below
  is that per-edge identity, proved for all integers in one closed form (no case split needed
  in the statement, since `0 <= a*b` already captures "same sign or a zero"). `sum_cancel_general`
  lifts it, via `Finset.sum_congr`, to a finite sum over ANY finite edge set given as a
  `Finset (S x S)` of ordered adjacent pairs together with its endpoint data — this is the exact
  combinatorial content of the paper's "sum over the six edges of each site, halved", stated
  abstractly since the honeycomb's site-adjacency graph itself (six neighbours per site) is not
  yet a Lean object in this repo (`HexGraph.lean` builds the *dual* graph on triangular faces,
  not this site graph). Reusing that abstract edge set was chosen over asserting the concrete
  6-regular hex-adjacency relation, which would be new geometry outside this batch's scope.

  ## `cor:single` — NOT formalized this batch (documented, not forced)

  Corollary `cor:single` states `ell(t_{n,m}^{+-1}) = 6 + 2 d_X(e, f_{n,m})`, i.e. word length
  in the honeycomb group equals `6 + 2 k(n,m)`. `HexGraph.lean` / `HexDistance.lean` already
  PROVE, unconditionally, that `k(n,m) = d_X(e, f_{n,m})` equals the closed form `kClosed n j`
  (`lem_krows_face`, pre-existing, not new work here) — that is the *right-hand* content of
  `cor:single`. What is missing is the *left-hand* content: a Lean definition of `ell`, the
  actual word length of the group element `t_{n,m}` in the free-product-with-relations `P-hat`,
  and the Euler-circuit upper/lower bound argument (paper4.tex's `lem:sep`/`prop:cut`-adjacent
  proof, using the stratum function `st` and a directed-multigraph Eulerian-circuit
  construction) that connects it to `||phi||_1 + 2 st(c)`. No such word-length or stratum
  infrastructure exists yet in `lean/with_mathlib/` for paper4's honeycomb group (the nearby
  `TrueLengthUpper.lean`/`EltBridge.lean` machinery is paper2's different `(k,eps,delta)` model,
  not paper4's `X`). Building it is genuine new work (an Eulerian-circuit existence proof over
  a possibly-infinite locally-finite multigraph) well beyond a Tier-A item, so `cor:single` is
  left out of this batch rather than stated vacuously or reduced to only its already-proved
  half.
-/
import Mathlib.Tactic

namespace Paper4TierA

/-- `le_or_lt` is absent under that name in this Mathlib (see `HexDistance.lean`'s identical
note); the integer case is all we need. -/
private theorem le_or_lt (a b : ℤ) : a ≤ b ∨ b < a := by omega

/-! ### `lem:kernel` -/

/-- **`lem:kernel`, the word identity.** For three involutions `x0 x1 x2` in a group `G`,
`x0 x1 x2 x0 x1 x2` equals `rho_1 rho_2^{-1} rho_1^{-1} rho_2` with `rho_1 = x0 x1`,
`rho_2 = x0 x2` — exactly the equation the paper's proof displays
(`x0x1x2x0x1x2=(x0x1)(x2x0)(x1x0)(x0x2)`, read as `rho_1 rho_2^{-1} rho_1^{-1} rho_2`). -/
theorem paper4_lem_kernel {G : Type*} [Group G] (x0 x1 x2 : G)
    (h0 : x0 * x0 = 1) (h1 : x1 * x1 = 1) (h2 : x2 * x2 = 1) :
    x0 * x1 * x2 * x0 * x1 * x2 =
      (x0 * x1) * (x0 * x2)⁻¹ * (x0 * x1)⁻¹ * (x0 * x2) := by
  have hx0 : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right h0
  have hx1 : x1⁻¹ = x1 := inv_eq_of_mul_eq_one_right h1
  have hx2 : x2⁻¹ = x2 := inv_eq_of_mul_eq_one_right h2
  have expand : (x0 * x1) * (x0 * x2)⁻¹ * (x0 * x1)⁻¹ * (x0 * x2)
      = x0 * x1 * (x2 * x0) * (x1 * x0) * (x0 * x2) := by
    simp [mul_inv_rev, hx0, hx1, hx2, mul_assoc]
  rw [expand]
  -- x0 * x1 * (x2 * x0) * (x1 * x0) * (x0 * x2)
  --   = x0 x1 x2 x0 x1 (x0 x0) x2 = x0 x1 x2 x0 x1 x2, using x0*x0=1
  have step : x0 * x1 * (x2 * x0) * (x1 * x0) * (x0 * x2)
      = x0 * x1 * x2 * x0 * x1 * (x0 * x0) * x2 := by
    simp only [mul_assoc]
  rw [step, h0, mul_one]

/-- Restated with `rho_1`, `rho_2` bound to names, matching the paper's notation directly. -/
theorem paper4_lem_kernel' {G : Type*} [Group G] (x0 x1 x2 : G)
    (h0 : x0 * x0 = 1) (h1 : x1 * x1 = 1) (h2 : x2 * x2 = 1) :
    let rho1 := x0 * x1
    let rho2 := x0 * x2
    x0 * x1 * x2 * x0 * x1 * x2 = rho1 * rho2⁻¹ * rho1⁻¹ * rho2 :=
  paper4_lem_kernel x0 x1 x2 h0 h1 h2

/-! ### `cor:cancel` -/

/-- **The per-edge identity underlying `cor:cancel`.** For any two integers `a`, `b`,
`|a - b| = |a| + |b| - 2 * (if 0 <= a*b then min |a| |b| else 0)`. The condition `0 <= a*b`
is exactly "same sign, or at least one of them is zero" — the paper's case split
("when the signs differ or one side vanishes" vs. "when they agree"). -/
theorem edge_cancel (a b : ℤ) :
    |a - b| = |a| + |b| - 2 * (if 0 ≤ a * b then min |a| |b| else 0) := by
  rcases abs_cases a with ⟨ea, ha⟩ | ⟨ea, ha⟩ <;>
    rcases abs_cases b with ⟨eb, hb⟩ | ⟨eb, hb⟩ <;>
    rcases abs_cases (a - b) with ⟨ed, hd⟩ | ⟨ed, hd⟩ <;>
    rw [ea, eb, ed] <;>
    by_cases hab : 0 ≤ a * b <;>
    simp only [hab, if_true, if_false, min_def] <;>
    (try split_ifs) <;>
    (try have e1 : a ≤ 0 := by nlinarith) <;>
    (try have e2 : (0:ℤ) ≤ a := by nlinarith) <;>
    (try have e3 : b ≤ 0 := by nlinarith) <;>
    (try have e4 : (0:ℤ) ≤ b := by nlinarith) <;>
    omega

/-- Same-sign version, spelled out exactly as the paper's second display: when `a` and `b`
carry equal signs (both nonnegative or both nonpositive), `|a-b| = |a|+|b| - 2 min(|a|,|b|)`. -/
theorem edge_cancel_same_sign {a b : ℤ} (h : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    |a - b| = |a| + |b| - 2 * min |a| |b| := by
  have hab : 0 ≤ a * b := by rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> nlinarith
  rw [edge_cancel a b, if_pos hab]

/-- Opposite-sign (or a zero) version: `|a-b| = |a|+|b|` with no correction term. -/
theorem edge_cancel_opp_sign {a b : ℤ} (h : (0 ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ 0 ≤ b)) :
    |a - b| = |a| + |b| := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonneg (by omega : (0:ℤ) ≤ a - b)]; ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos (by omega : a - b ≤ (0:ℤ))]; ring


/-- **`cor:cancel`, the finite-sum form.** Given a finite `Finset` `E` of "edges" — ordered
pairs `(u,v) : S x S` together with a configuration `c : S -> Z` — the total variation
`sum_{(u,v) in E} |c u - c v|` splits into `sum_{(u,v) in E} (|c u| + |c v|)` minus twice the
same-sign correction, exactly mirroring the paper's "sum over edges, split by sign agreement"
argument (which is then halved for the site-indexed double count; that half is a bookkeeping
step of the *specific* six-edges-per-site enumeration and is not reproved abstractly here,
since it needs the concrete hex-adjacency structure that is out of scope, per the file header). -/
theorem sum_cancel_general {S : Type*} (E : Finset (S × S)) (c : S → ℤ) :
    ∑ e ∈ E, |c e.1 - c e.2|
      = ∑ e ∈ E, (|c e.1| + |c e.2|)
        - 2 * ∑ e ∈ E, (if 0 ≤ c e.1 * c e.2 then min |c e.1| |c e.2| else 0) := by
  have h : ∀ e ∈ E, |c e.1 - c e.2|
      = (|c e.1| + |c e.2|) - (if 0 ≤ c e.1 * c e.2 then min |c e.1| |c e.2| else 0) * 2 := by
    intro e _
    have := edge_cancel (c e.1) (c e.2)
    linarith
  rw [Finset.sum_congr rfl h]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf

end Paper4TierA

#print axioms Paper4TierA.paper4_lem_kernel
#print axioms Paper4TierA.edge_cancel
#print axioms Paper4TierA.edge_cancel_same_sign
#print axioms Paper4TierA.edge_cancel_opp_sign
#print axioms Paper4TierA.sum_cancel_general
