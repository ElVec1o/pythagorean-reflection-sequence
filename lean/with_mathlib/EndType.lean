/-
The end type of a configuration, and the transport of `EdgeData.mult_pos`.

Edges are indexed by `Fin n`; edge `e` carries `m e` crossings, and each crossing
has two ends.  So an end is a crossing together with a choice of which of its two
ends this is:

    Endpt n m = (Σ e : Fin n, Fin (m e)) × Bool

which is a `Fintype` automatically.  `edgeOf` reads off the edge.

`exists_end_of_mult_pos` is the transport: an edge with at least one crossing
carries an end.  That is the hypothesis `hcross` of
`GapFreeAssembly.shared_site_constructed`, and `EdgeData.mult_pos` is what supplies
its premise for a gap-free edge.  With it, the chain from gap-freeness to the
shared site has no assumptions left.
-/
import Mathlib.Tactic
import EdgeData

namespace EndType

/-- Ends of a configuration: a crossing of some edge, and which of its two ends. -/
def Endpt (n : ℕ) (m : Fin n → ℕ) : Type := (Σ e : Fin n, Fin (m e)) × Bool

instance (n : ℕ) (m : Fin n → ℕ) : Fintype (Endpt n m) := by
  unfold Endpt; infer_instance

instance (n : ℕ) (m : Fin n → ℕ) : DecidableEq (Endpt n m) := by
  unfold Endpt; infer_instance

/-- The edge an end belongs to. -/
def edgeOf {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : ℤ := (x.1.1 : ℤ)

/-- Which of the crossing's two ends. -/
def atTop {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : Bool := x.2

/-- **The transport.**  An edge with a crossing carries an end.  This is `hcross`. -/
theorem exists_end_of_mult_pos {n : ℕ} {m : Fin n → ℕ} (e : Fin n) (h : 0 < m e) :
    ∃ x : Endpt n m, edgeOf x = (e : ℤ) :=
  ⟨⟨⟨e, ⟨0, h⟩⟩, true⟩, rfl⟩

/-- Every end lies on an edge of the index range, which gives the two span bounds
`GapFreeAssembly.shared_site_constructed` also needs. -/
theorem edgeOf_nonneg {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : 0 ≤ edgeOf x := by
  unfold edgeOf; exact Int.natCast_nonneg _

theorem edgeOf_lt {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : edgeOf x < (n : ℤ) := by
  unfold edgeOf
  exact_mod_cast x.1.1.isLt

/-- The multiplicity of a gap-free edge is positive as a natural number, which is
the form the transport needs. -/
theorem mult_natPos {d f : ℤ} (hf : EdgeData.IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ EdgeData.IsGap d f) : 0 < (max |d| |f|).toNat := by
  have h := EdgeData.mult_pos hf hpar hgap
  omega

/-! ### Non-vacuity -/

/-- Two edges, one crossing each: an end exists on edge `0`. -/
theorem witness_end_exists :
    ∃ x : Endpt 2 (fun _ => 1), edgeOf x = (0 : ℤ) :=
  exists_end_of_mult_pos ⟨0, by norm_num⟩ (by norm_num)

/-- An edge with no crossings carries no end, so the hypothesis is doing work. -/
theorem witness_no_end : ¬ ∃ x : Endpt 1 (fun _ => 0), True := by
  rintro ⟨⟨⟨_, i⟩, _⟩, _⟩
  exact absurd i.isLt (Nat.not_lt_zero _)

/-! ### The crossing-partner map

The first of the two involutions a `WalkGraph.Data` needs, constructed on the
concrete end type.  It exchanges the two ends of a crossing, so it fixes the edge
and flips which end this is, which are exactly the two conditions the walk-graph
data asks of it. -/

/-- Exchange the two ends of a crossing. -/
def partner {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : Endpt n m := (x.1, !x.2)

@[simp] theorem partner_fst {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (partner x).1 = x.1 := rfl

@[simp] theorem partner_snd {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (partner x).2 = !x.2 := rfl

theorem partner_invol {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    partner (partner x) = x := by
  unfold partner
  simp

theorem partner_ne {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : partner x ≠ x := by
  intro h
  have := congrArg Prod.snd h
  simp only [partner_snd] at this
  exact (Bool.not_ne_self x.2) this

theorem partner_edgeOf {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    edgeOf (partner x) = edgeOf x := rfl

theorem partner_atTop {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    atTop (partner x) = !atTop x := rfl

/-- The two ends of a crossing sit at consecutive sites, one at the edge's index
and one at the next: this is what makes the crossing map move between sites while
the turn stays at one, which is the condition the walk graph needs to have two
distinct neighbours at every end. -/
theorem partner_site_ne {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (edgeOf (partner x) + (if atTop (partner x) then 1 else 0))
      ≠ (edgeOf x + (if atTop x then 1 else 0)) := by
  rw [partner_edgeOf, partner_atTop]
  cases h : atTop x <;> simp [h]

-- Certification (Rule 5).
#print axioms EndType.exists_end_of_mult_pos
#print axioms EndType.edgeOf_nonneg
#print axioms EndType.edgeOf_lt
#print axioms EndType.mult_natPos
#print axioms EndType.witness_end_exists
#print axioms EndType.witness_no_end
#print axioms EndType.partner_invol
#print axioms EndType.partner_ne
#print axioms EndType.partner_edgeOf
#print axioms EndType.partner_site_ne

end EndType
