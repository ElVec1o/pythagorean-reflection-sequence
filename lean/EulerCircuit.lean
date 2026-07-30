/-
Euler's theorem for finite directed multigraphs, towards the upper bound of the
metric theorem (paper 4, Theorem "Metric").

Mathlib supplies `SimpleGraph.Walk.IsEulerian` and the necessary degree
condition, but not the sufficiency: that a connected multigraph in which every
vertex has equal in- and out-degree carries a circuit using each directed edge
exactly once.  That is the statement `euler_circuit` below, and it is the one
input the paper's upper bound takes on faith.

The theorem is proved here, in core Lean 4 and with no `sorry`.  The route
avoids decomposing the multigraph into connected components, which is what
makes the usual presentation heavy: instead of removing a maximal closed trail
and recursing on the components of the remainder, the circuit is grown one
closed trail at a time.

  `trail_degree`          a trail from `a` to `b` uses, at every vertex, as many
                          outgoing as incoming edges, except for a surplus of
                          one at `a` and a deficit of one at `b`;
  `maximal_trail_closed`  hence in a balanced multigraph a trail that cannot be
                          extended has returned to its start;
  `walk_exists`           a greedy walk continues until it is stuck;
  `closed_trail_exists`   so in a balanced multigraph it is closed;
  `trail_split_at`        a circuit can be cut at any vertex it visits, and
  `splice`                a closed trail inserted there;
  `absorb`                iterating that while some unused edge leaves the
                          circuit, an induction on the number of unused edges;
  `reach_stays`           and when none does, connectivity forces the remainder
                          to be empty, since reachability from the base cannot
                          leave the circuit.

No imports: core Lean 4 only.
-/

namespace EulerMulti

variable {V : Type} [DecidableEq V]

/-- A directed edge. -/
abbrev DEdge (V : Type) := V × V

/-- Number of edges leaving `v`. -/
def outDeg (E : List (DEdge V)) (v : V) : Nat :=
  (E.filter (fun e => e.1 = v)).length

/-- Number of edges entering `v`. -/
def inDeg (E : List (DEdge V)) (v : V) : Nat :=
  (E.filter (fun e => e.2 = v)).length

/-- `IsTrail a b L` says the edges of `L`, in order, walk from `a` to `b`. -/
def IsTrail : V → V → List (DEdge V) → Prop
  | a, b, [] => a = b
  | a, b, e :: es => e.1 = a ∧ IsTrail e.2 b es

/-- Every vertex of `E` has equal in- and out-degree. -/
def Balanced (E : List (DEdge V)) : Prop := ∀ v, outDeg E v = inDeg E v

/-- Out-degree of a cons. -/
theorem outDeg_cons (e : DEdge V) (es : List (DEdge V)) (v : V) :
    outDeg (e :: es) v = (if v = e.1 then 1 else 0) + outDeg es v := by
  by_cases h : v = e.1
  · subst h; simp [outDeg] <;> omega
  · simp [outDeg, Ne.symm h, h] <;> omega

/-- In-degree of a cons. -/
theorem inDeg_cons (e : DEdge V) (es : List (DEdge V)) (v : V) :
    inDeg (e :: es) v = (if v = e.2 then 1 else 0) + inDeg es v := by
  by_cases h : v = e.2
  · subst h; simp [inDeg] <;> omega
  · simp [inDeg, Ne.symm h, h] <;> omega

/-- The degree identity along a trail, in subtraction-free form: at every
vertex the trail leaves as often as it enters, counting its start as one extra
departure and its end as one extra arrival.  This is the counting core of
Hierholzer's argument. -/
theorem trail_degree (a b : V) (L : List (DEdge V)) (h : IsTrail a b L) (v : V) :
    outDeg L v + (if v = b then 1 else 0) = inDeg L v + (if v = a then 1 else 0) := by
  induction L generalizing a with
  | nil =>
    simp only [IsTrail] at h
    subst h
    simp [outDeg, inDeg]
  | cons e es ih =>
    obtain ⟨he, htail⟩ := h
    have hrec := ih e.2 htail
    subst he
    rw [outDeg_cons, inDeg_cons]
    omega

/-- Splitting degrees over an append. -/
theorem outDeg_append (L R : List (DEdge V)) (v : V) :
    outDeg (L ++ R) v = outDeg L v + outDeg R v := by
  simp [outDeg, List.filter_append, List.length_append]

theorem inDeg_append (L R : List (DEdge V)) (v : V) :
    inDeg (L ++ R) v = inDeg L v + inDeg R v := by
  simp [inDeg, List.filter_append, List.length_append]

/-- A vertex of positive out-degree has an edge leaving it. -/
theorem exists_out (R : List (DEdge V)) (v : V) (h : 0 < outDeg R v) :
    ∃ e ∈ R, e.1 = v := by
  induction R with
  | nil => simp [outDeg] at h
  | cons e es ih =>
    rw [outDeg_cons] at h
    by_cases hv : v = e.1
    · exact ⟨e, by simp, hv.symm⟩
    · simp only [if_neg hv, Nat.zero_add] at h
      obtain ⟨f, hf, hfv⟩ := ih h
      exact ⟨f, List.mem_cons_of_mem _ hf, hfv⟩

/-- In a balanced multigraph, a trail that cannot be extended is closed.

`L` is the trail, `R` the edges it has not used, and `hmax` says no unused edge
leaves the trail's endpoint. -/
theorem maximal_trail_closed (L R : List (DEdge V)) (a b : V)
    (htrail : IsTrail a b L) (hbal : Balanced (L ++ R))
    (hmax : ∀ e ∈ R, e.1 ≠ b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · -- at `b` the trail arrives once more than it departs, so the unused edges
    -- must depart once more than they arrive; one of them therefore leaves `b`.
    have hdeg := trail_degree a b L htrail b
    rw [if_pos rfl, if_neg (fun h => hab h.symm)] at hdeg
    have hb := hbal b
    rw [outDeg_append, inDeg_append] at hb
    have hpos : 0 < outDeg R b := by omega
    obtain ⟨e, heR, heb⟩ := exists_out R b hpos
    exact absurd heb (hmax e heR)

/-- Trails compose. -/
theorem isTrail_append {a b c : V} {L1 L2 : List (DEdge V)}
    (h1 : IsTrail a b L1) (h2 : IsTrail b c L2) : IsTrail a c (L1 ++ L2) := by
  induction L1 generalizing a with
  | nil =>
    simp only [IsTrail] at h1
    subst h1
    simpa using h2
  | cons e es ih =>
    obtain ⟨he, htail⟩ := h1
    exact ⟨he, ih htail⟩

/-- Trails split: a trail along a concatenation passes through a middle vertex. -/
theorem isTrail_split {a c : V} (L1 L2 : List (DEdge V)) (h : IsTrail a c (L1 ++ L2)) :
    ∃ b, IsTrail a b L1 ∧ IsTrail b c L2 := by
  induction L1 generalizing a with
  | nil => exact ⟨a, rfl, by simpa using h⟩
  | cons e es ih =>
    obtain ⟨he, htail⟩ := h
    obtain ⟨b, hb1, hb2⟩ := ih htail
    exact ⟨b, ⟨he, hb1⟩, hb2⟩

/-- Splicing: a closed trail at a vertex of a circuit can be inserted there.
This is the step the induction of `euler_circuit` performs once per component. -/
theorem splice {a v : V} {C1 C2 D : List (DEdge V)}
    (h1 : IsTrail a v C1) (h2 : IsTrail v a C2) (hd : IsTrail v v D) :
    IsTrail a a (C1 ++ D ++ C2) := by
  rw [List.append_assoc]
  exact isTrail_append h1 (isTrail_append hd h2)

/-! ## Greedy closed trails

The step Hierholzer's induction needs is that a greedy walk in a balanced
multigraph, continued until it is stuck, is closed.  `walk_exists` builds the
walk, `Balanced` transfers along permutations, and `closed_trail_exists`
combines them with `maximal_trail_closed`. -/

/-- Remove one occurrence of `a`. -/
def removeOne (a : DEdge V) : List (DEdge V) → List (DEdge V)
  | [] => []
  | x :: xs => if x = a then xs else x :: removeOne a xs

theorem length_removeOne {a : DEdge V} {l : List (DEdge V)} (h : a ∈ l) :
    (removeOne a l).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = a
    · simp [removeOne, hx]
    · have : a ∈ xs := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hx
        · exact h'
      simp [removeOne, hx, ih this]

theorem perm_removeOne {a : DEdge V} {l : List (DEdge V)} (h : a ∈ l) :
    l.Perm (a :: removeOne a l) := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx; simp [removeOne]
    · have hmem : a ∈ xs := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hx
        · exact h'
      have := ih hmem
      simp only [removeOne, hx, if_false]
      exact (this.cons x).trans (List.Perm.swap a x _)

/-- Degrees, hence balance, are permutation invariants. -/
theorem outDeg_perm {L1 L2 : List (DEdge V)} (h : L1.Perm L2) (v : V) :
    outDeg L1 v = outDeg L2 v := by
  simp only [outDeg]
  exact (h.filter _).length_eq

theorem inDeg_perm {L1 L2 : List (DEdge V)} (h : L1.Perm L2) (v : V) :
    inDeg L1 v = inDeg L2 v := by
  simp only [inDeg]
  exact (h.filter _).length_eq

theorem balanced_perm {L1 L2 : List (DEdge V)} (h : L1.Perm L2) (hb : Balanced L1) :
    Balanced L2 := by
  intro v
  rw [← outDeg_perm h v, ← inDeg_perm h v]
  exact hb v

/-- A greedy walk from `v`, continued until no unused edge leaves its endpoint.
Proved by induction on a bound for the number of remaining edges. -/
theorem walk_exists_aux : ∀ (n : Nat) (R : List (DEdge V)) (v : V), R.length ≤ n →
    ∃ (b : V) (T S : List (DEdge V)),
      (T ++ S).Perm R ∧ IsTrail v b T ∧ (∀ e ∈ S, e.1 ≠ b) := by
  intro n
  induction n with
  | zero =>
    intro R v hR
    cases R with
    | nil => exact ⟨v, [], [], by simp, rfl, by simp⟩
    | cons x xs => exact absurd hR (Nat.not_succ_le_zero _)
  | succ n ih =>
    intro R v hR
    by_cases hstuck : ∃ e ∈ R, e.1 = v
    · obtain ⟨e, heR, hev⟩ := hstuck
      have hlen : (removeOne e R).length ≤ n := by
        have := length_removeOne heR
        omega
      obtain ⟨b, T, S, hperm, htrail, hmax⟩ := ih (removeOne e R) e.2 hlen
      exact ⟨b, e :: T, S, (hperm.cons e).trans (perm_removeOne heR).symm,
        ⟨hev, htrail⟩, hmax⟩
    · exact ⟨v, [], R, by simpa using List.Perm.refl R, rfl,
        fun e heR hev => hstuck ⟨e, heR, hev⟩⟩

theorem walk_exists (R : List (DEdge V)) (v : V) :
    ∃ (b : V) (T S : List (DEdge V)),
      (T ++ S).Perm R ∧ IsTrail v b T ∧ (∀ e ∈ S, e.1 ≠ b) :=
  walk_exists_aux R.length R v (Nat.le_refl _)

/-- In a balanced multigraph a greedy walk from `v` returns to `v`. -/
theorem closed_trail_exists (R : List (DEdge V)) (v : V) (hbal : Balanced R) :
    ∃ (T S : List (DEdge V)),
      (T ++ S).Perm R ∧ IsTrail v v T ∧ (∀ e ∈ S, e.1 ≠ v) := by
  obtain ⟨b, T, S, hperm, htrail, hmax⟩ := walk_exists R v
  have hbal' : Balanced (T ++ S) := balanced_perm hperm.symm hbal
  have hvb : v = b := maximal_trail_closed T S v b htrail hbal' hmax
  subst hvb
  exact ⟨T, S, hperm, htrail, hmax⟩

/-- The vertices a trail visits, in order. -/
def trailVerts (a : V) : List (DEdge V) → List V
  | [] => [a]
  | e :: es => a :: trailVerts e.2 es

/-- A trail can be cut at any vertex it visits.  With `splice`, this is how a
closed trail found at a visited vertex is inserted into the circuit. -/
theorem trail_split_at {a b v : V} {L : List (DEdge V)} (h : IsTrail a b L)
    (hv : v ∈ trailVerts a L) :
    ∃ L1 L2, L = L1 ++ L2 ∧ IsTrail a v L1 ∧ IsTrail v b L2 := by
  induction L generalizing a with
  | nil =>
    simp only [IsTrail] at h
    subst h
    simp only [trailVerts, List.mem_singleton] at hv
    subst hv
    exact ⟨[], [], rfl, rfl, rfl⟩
  | cons e es ih =>
    obtain ⟨he, htail⟩ := h
    simp only [trailVerts, List.mem_cons] at hv
    rcases hv with hv | hv
    · refine ⟨[], e :: es, rfl, hv.symm, ⟨he.trans hv.symm, htail⟩⟩
    · obtain ⟨L1, L2, hL, h1, h2⟩ := ih htail hv
      exact ⟨e :: L1, L2, by rw [hL]; rfl, ⟨he, h1⟩, h2⟩

/-- A closed trail is balanced. -/
theorem balanced_of_closed {a : V} {L : List (DEdge V)} (h : IsTrail a a L) :
    Balanced L := by
  intro v
  have := trail_degree a a L h v
  omega

/-- Balance subtracts. -/
theorem balanced_of_append {T S : List (DEdge V)}
    (h : Balanced (T ++ S)) (hT : Balanced T) : Balanced S := by
  intro v
  have h1 := h v
  have h2 := hT v
  rw [outDeg_append, inDeg_append] at h1
  omega

/-- The start of a trail is one of its vertices. -/
theorem mem_trailVerts_head (a : V) (L : List (DEdge V)) : a ∈ trailVerts a L := by
  cases L with
  | nil => simp [trailVerts]
  | cons e es => simp [trailVerts]

/-- Both endpoints of an edge of a trail are vertices of the trail. -/
theorem mem_trailVerts_of_mem {a b : V} {L : List (DEdge V)} (h : IsTrail a b L)
    {e : DEdge V} (he : e ∈ L) : e.1 ∈ trailVerts a L ∧ e.2 ∈ trailVerts a L := by
  induction L generalizing a with
  | nil => cases he
  | cons f fs ih =>
    obtain ⟨hf, htail⟩ := h
    rcases List.mem_cons.mp he with rfl | he'
    · refine ⟨?_, ?_⟩
      · simp only [trailVerts, List.mem_cons]
        exact Or.inl hf
      · simp only [trailVerts, List.mem_cons]
        exact Or.inr (mem_trailVerts_head _ _)
    · obtain ⟨h1, h2⟩ := ih htail he'
      exact ⟨by simp [trailVerts, h1], by simp [trailVerts, h2]⟩

/-- Absorption: as long as an unused edge leaves a vertex of the circuit, a
closed trail can be found there and spliced in.  Iterating until no unused edge
leaves the circuit is an induction on the number of unused edges. -/
theorem absorb : ∀ (n : Nat) (C R : List (DEdge V)) (base : V),
    R.length ≤ n → Balanced R → IsTrail base base C →
    ∃ C' R', (C' ++ R').Perm (C ++ R) ∧ IsTrail base base C' ∧
      (∀ f ∈ R', f.1 ∉ trailVerts base C') := by
  intro n
  induction n with
  | zero =>
    intro C R base hR hbal htrail
    cases R with
    | nil => exact ⟨C, [], by simp, htrail, by simp⟩
    | cons x xs => exact absurd hR (Nat.not_succ_le_zero _)
  | succ n ih =>
    intro C R base hR hbal htrail
    by_cases hex : ∃ f ∈ R, f.1 ∈ trailVerts base C
    · obtain ⟨f, hfR, hfv⟩ := hex
      obtain ⟨T, S, hperm, hT, hS⟩ := closed_trail_exists R f.1 hbal
      have hTne : 0 < T.length := by
        cases hT2 : T with
        | nil =>
          exfalso
          have hp : List.Perm S R := by
            rw [hT2] at hperm
            simpa using hperm
          exact hS f (hp.mem_iff.mpr hfR) rfl
        | cons a as => simp
      obtain ⟨C1, C2, hC, hC1, hC2⟩ := trail_split_at htrail hfv
      have hnew : IsTrail base base (C1 ++ T ++ C2) := splice hC1 hC2 hT
      have hlen : S.length ≤ n := by
        have h1 : (T ++ S).length = R.length := hperm.length_eq
        simp only [List.length_append] at h1
        omega
      have hbalS : Balanced S :=
        balanced_of_append (balanced_perm hperm.symm hbal) (balanced_of_closed hT)
      obtain ⟨C', R', hp, hc, hr⟩ := ih (C1 ++ T ++ C2) S base hlen hbalS hnew
      refine ⟨C', R', hp.trans ?_, hc, hr⟩
      have inner : List.Perm (T ++ (C2 ++ S)) (C2 ++ (T ++ S)) := by
        rw [← List.append_assoc T C2 S, ← List.append_assoc C2 T S]
        exact List.Perm.append_right S List.perm_append_comm
      have step1 : List.Perm (((C1 ++ T) ++ C2) ++ S) ((C1 ++ C2) ++ (T ++ S)) := by
        have l1 : ((C1 ++ T) ++ C2) ++ S = C1 ++ (T ++ (C2 ++ S)) := by
          simp [List.append_assoc]
        have l2 : (C1 ++ C2) ++ (T ++ S) = C1 ++ (C2 ++ (T ++ S)) := by
          simp [List.append_assoc]
        rw [l1, l2]
        exact List.Perm.append_left C1 inner
      refine step1.trans ?_
      rw [← hC]
      exact List.Perm.append_left C hperm
    · exact ⟨C, R, List.Perm.refl _, htrail, fun f hf hfv => hex ⟨f, hf, hfv⟩⟩

/-- Reachability cannot leave the circuit once every unused edge starts outside
it: walking from a circuit vertex, each edge met lies in the circuit. -/
theorem reach_stays {E C' R' : List (DEdge V)} {base : V}
    (hr : ∀ f ∈ R', f.1 ∉ trailVerts base C')
    (hsplit : ∀ g ∈ E, g ∈ C' ∨ g ∈ R')
    (hc : IsTrail base base C') :
    ∀ (P : List (DEdge V)) (a b : V), IsTrail a b P → (∀ g ∈ P, g ∈ E) →
      a ∈ trailVerts base C' → b ∈ trailVerts base C' := by
  intro P
  induction P with
  | nil => intro a b h _ ha; simp only [IsTrail] at h; subst h; exact ha
  | cons g gs ih =>
    intro a b h hsub ha
    obtain ⟨hg, htail⟩ := h
    have hgE : g ∈ E := hsub g (by simp)
    have hgC : g ∈ C' := by
      rcases hsplit g hgE with hgc | hgr
      · exact hgc
      · exact absurd (hg ▸ ha) (hr g hgr)
    have hhead : g.2 ∈ trailVerts base C' := (mem_trailVerts_of_mem hc hgC).2
    exact ih g.2 b htail (fun x hx => hsub x (List.mem_cons_of_mem g hx)) hhead

/-- **Euler's theorem for finite directed multigraphs.**  A balanced multigraph
whose edges all lie in one connected component carries a circuit using every
edge exactly once.

`hconn` is the connectivity hypothesis: every edge is reachable from the base
vertex through the multigraph. -/
theorem euler_circuit (E : List (DEdge V)) (base : V)
    (hbal : Balanced E)
    (hconn : ∀ e ∈ E, ∃ P : List (DEdge V), (∀ f ∈ P, f ∈ E) ∧ IsTrail base e.1 P) :
    ∃ L : List (DEdge V), L.Perm E ∧ IsTrail base base L := by
  obtain ⟨C', R', hp, hc, hr⟩ := absorb E.length [] E base (Nat.le_refl _) hbal rfl
  have hpE : (C' ++ R').Perm E := by simpa using hp
  have hsplit : ∀ g ∈ E, g ∈ C' ∨ g ∈ R' := by
    intro g hg
    exact List.mem_append.mp (hpE.mem_iff.mpr hg)
  have hR' : R' = [] := by
    cases hR2 : R' with
    | nil => rfl
    | cons f fs =>
      exfalso
      have hfR' : f ∈ R' := by rw [hR2]; simp
      have hfE : f ∈ E := hpE.mem_iff.mp (List.mem_append_right C' hfR')
      obtain ⟨P, hPsub, hPtrail⟩ := hconn f hfE
      have hbase : base ∈ trailVerts base C' := mem_trailVerts_head base C'
      exact hr f hfR' (reach_stays hr hsplit hc P base f.1 hPtrail hPsub hbase)
  rw [hR'] at hpE
  exact ⟨C', by simpa using hpE, hc⟩

end EulerMulti
