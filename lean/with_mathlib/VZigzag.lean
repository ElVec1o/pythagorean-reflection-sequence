/-
  VZigzag.lean
  ============
  The odd-span spine+zigzag turn on the EXTENDED end type `EltBridge.VEndpt`.

  `EltBridge.zzTurn` (BLOCK 339) builds an explicit turn on `EndType.Endpt n m` for
  ARBITRARY EVEN widths and proves the shield law `walkCount = |Z| + 1` from it.  The
  widths coming from a group element are not all even: `TravelParity.mu_odd_iff_mem`
  says `mu j` is ODD exactly on the travel interval, so at the two sites `0` and
  `kstar` the end count is odd and no turn exists on `Endpt` alone.  That is what the
  two extra points of `VEndpt n mm = Endpt n mm (+) Bool` are for: they are the two
  ends of ONE long virtual strand spanning the travel interval.

  This file builds the corresponding turn.  Writing `sp e = 0` for an edge of the
  travel span (odd width) and `sp e = 1` off it (even width, `>= 2`), each edge's
  "chain" is its strands `sp e .. m e - 1` -- an ODD number in both cases -- zigzagged
  into a single path, and the strands `0` of the non-span edges are "spines".  The
  virtual strand is the missing spine across the span:

      spine(0) .. spine(lo-1) -- V -- spine(hi) .. spine(n-1)

  is the spine line, and the chains run back the other way, so every run is one cycle.

  The construction was validated first in Rust
  (`code/zeta_probe/tools/nogap/src/bin/vzigzag_check.rs`, 46 618 configurations, two
  independent component counters agreeing, 0 failures) and only then formalised.

  Technique, inherited from BLOCK 339: never state an equation between `Endpt` values
  directly.  Every fact about the turn is stated on `.edge.val`, `.idx.val` and `.top`
  separately and reassembled by `endpt_ext`, so no dependent-`Fin` transport and no
  `HEq` ever appears and `omega` closes every index obligation.
-/
import EltBridge

namespace VZigzag

open EltBridge EndType

variable {n : ℕ} {m : Fin n → ℕ}

/-! ## The configuration -/

/-- An odd-span width configuration: widths are odd exactly on the edge interval
`[lo, hi)` and even (and at least `2`) off it.  `bl` records which of the two virtual
tags sits at the LOW site `lo`; the other sits at `hi`. -/
structure VZ (n : ℕ) (m : Fin n → ℕ) where
  /-- the low end of the travel span -/
  lo : ℕ
  /-- the high end of the travel span -/
  hi : ℕ
  /-- the tag of the virtual point at site `lo` -/
  bl : Bool
  /-- the span is non-empty -/
  hlh : lo < hi
  /-- and lies inside the chain of edges -/
  hhn : hi ≤ n
  /-- span edges have odd width -/
  hodd : ∀ e : Fin n, lo ≤ e.val → e.val < hi → m e % 2 = 1
  /-- edges off the span have even width, at least two -/
  heven : ∀ e : Fin n, ¬ (lo ≤ e.val ∧ e.val < hi) → 2 ≤ m e ∧ m e % 2 = 0

namespace VZ

/-- The number of spine strands of an edge: none on the span, one off it. -/
def sp (C : VZ n m) (e : Fin n) : ℕ := if C.lo ≤ e.val ∧ e.val < C.hi then 0 else 1

theorem n_pos (C : VZ n m) : 0 < n := by have := C.hlh; have := C.hhn; omega

theorem sp_eq_zero (C : VZ n m) {e : Fin n} (h : C.lo ≤ e.val ∧ e.val < C.hi) : C.sp e = 0 := by
  simp only [sp, if_pos h]

theorem sp_eq_one (C : VZ n m) {e : Fin n} (h : ¬ (C.lo ≤ e.val ∧ e.val < C.hi)) : C.sp e = 1 := by
  simp only [sp, if_neg h]

theorem sp_le (C : VZ n m) (e : Fin n) : C.sp e ≤ 1 := by unfold sp; split <;> omega

theorem sp_zero_mem (C : VZ n m) {e : Fin n} (h : C.sp e = 0) : C.lo ≤ e.val ∧ e.val < C.hi := by
  unfold sp at h; split at h
  · assumption
  · omega

theorem sp_one_not_mem (C : VZ n m) {e : Fin n} (h : C.sp e = 1) : ¬ (C.lo ≤ e.val ∧ e.val < C.hi) := by
  unfold sp at h; split at h
  · omega
  · assumption

/-- **The width parity, uniformly.**  `m e + sp e` is odd: odd width with no spine on
the span, even width with one spine off it.  Equivalently the chain
`sp e .. m e - 1` always has an odd number of strands. -/
theorem m_par (C : VZ n m) (e : Fin n) : (m e + C.sp e) % 2 = 1 := by
  unfold sp; split_ifs with h
  · have := C.hodd e h.1 h.2; omega
  · have := (C.heven e h).2; omega

theorem sp_lt (C : VZ n m) (e : Fin n) : C.sp e < m e := by
  unfold sp; split_ifs with h
  · have := C.hodd e h.1 h.2; omega
  · have := (C.heven e h).1; omega

theorem m_pos (C : VZ n m) (e : Fin n) : 0 < m e := lt_of_le_of_lt (Nat.zero_le _) (C.sp_lt e)

/-- Edge `0`. -/
def eFirst (C : VZ n m) : Fin n := ⟨0, C.n_pos⟩
/-- Edge `n - 1`. -/
def eLast (C : VZ n m) : Fin n := ⟨n - 1, by have := C.n_pos; omega⟩
/-- Edge `lo - 1`, the last edge below the span. -/
def eLoPred (C : VZ n m) : Fin n := ⟨C.lo - 1, by have := C.hlh; have := C.hhn; omega⟩
/-- Edge `hi`, the first edge above the span, when there is one. -/
def eHi (C : VZ n m) (h : C.hi ≠ n) : Fin n := ⟨C.hi, by have := C.hhn; omega⟩

@[simp] theorem eFirst_val (C : VZ n m) : (C.eFirst).val = 0 := rfl
@[simp] theorem eLast_val (C : VZ n m) : (C.eLast).val = n - 1 := rfl
@[simp] theorem eLoPred_val (C : VZ n m) : (C.eLoPred).val = C.lo - 1 := rfl
@[simp] theorem eHi_val (C : VZ n m) (h : C.hi ≠ n) : (C.eHi h).val = C.hi := rfl

end VZ

/-! ## The turn -/

/-- The turn on a real end. -/
def vzTurnR (C : VZ n m) (Zf : Finset ℤ) (x : Endpt n m) : VEndpt n m :=
  if _hb : x.top = false then
    if _hi : C.sp x.edge + 1 ≤ x.idx.val then
      -- inside the chain: the bottom bounces (sp+1, sp+2), (sp+3, sp+4), ...
      Sum.inl ⟨x.edge,
        ⟨if (x.idx.val - C.sp x.edge) % 2 = 1 then x.idx.val + 1 else x.idx.val - 1, by
          have h1 := C.m_par x.edge
          have h2 := C.sp_le x.edge
          have h3 := x.idx.isLt
          split <;> omega⟩, false⟩
    else if _hs : C.sp x.edge = 1 ∧ x.idx.val = 0 then
      -- the spine's bottom end
      if hp : PassLo Zf x.edge then
        if _hk : C.sp (edgePred x.edge) = 1 then
          Sum.inl ⟨edgePred x.edge, ⟨0, C.m_pos _⟩, true⟩
        else
          -- the previous edge is a span edge, so this edge is `hi`
          Sum.inr (!C.bl)
      else
        Sum.inl ⟨x.edge, ⟨C.sp x.edge, C.sp_lt _⟩, false⟩
    else
      -- the chain's loose bottom end, strand `sp`
      if _hp : PassLo Zf x.edge then
        Sum.inl ⟨edgePred x.edge, ⟨m (edgePred x.edge) - 1, by
          have := C.m_pos (edgePred x.edge); omega⟩, true⟩
      else if _hk : C.sp x.edge = 1 then
        Sum.inl ⟨x.edge, ⟨0, C.m_pos _⟩, false⟩
      else
        -- a span edge bouncing at its bottom site: that site is `lo = 0`
        Sum.inr C.bl
  else
    if _hi : C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge then
      -- inside the chain: the top bounces (sp, sp+1), (sp+2, sp+3), ...
      Sum.inl ⟨x.edge,
        ⟨if (x.idx.val - C.sp x.edge) % 2 = 0 then x.idx.val + 1 else x.idx.val - 1, by
          have h3 := x.idx.isLt
          split <;> omega⟩, true⟩
    else if _hs : C.sp x.edge = 1 ∧ x.idx.val = 0 then
      -- the spine's top end
      if hp : PassHi Zf x.edge then
        if _hk : C.sp ⟨x.edge.val + 1, hp.1⟩ = 1 then
          Sum.inl ⟨⟨x.edge.val + 1, hp.1⟩, ⟨0, C.m_pos _⟩, false⟩
        else
          -- the next edge is a span edge, so it is `lo`
          Sum.inr C.bl
      else
        Sum.inl ⟨x.edge, ⟨m x.edge - 1, by have := C.m_pos x.edge; omega⟩, true⟩
    else
      -- the chain's loose top end, strand `m e - 1`
      if hp : PassHi Zf x.edge then
        Sum.inl ⟨⟨x.edge.val + 1, hp.1⟩, ⟨C.sp ⟨x.edge.val + 1, hp.1⟩, C.sp_lt _⟩, false⟩
      else if _hk : C.sp x.edge = 1 then
        Sum.inl ⟨x.edge, ⟨0, C.m_pos _⟩, true⟩
      else
        -- a span edge bouncing at its top site: that site is `hi = n`
        Sum.inr (!C.bl)

/-- The turn on a virtual end. -/
def vzTurnV (C : VZ n m) (b : Bool) : VEndpt n m :=
  if _hb : b = C.bl then
    -- the virtual end at site `lo`
    if _h0 : C.lo = 0 then
      Sum.inl ⟨C.eFirst, ⟨0, C.m_pos _⟩, false⟩
    else
      Sum.inl ⟨C.eLoPred, ⟨0, C.m_pos _⟩, true⟩
  else
    -- the virtual end at site `hi`
    if hn : C.hi = n then
      Sum.inl ⟨C.eLast, ⟨m C.eLast - 1, by have := C.m_pos C.eLast; omega⟩, true⟩
    else
      Sum.inl ⟨C.eHi hn, ⟨0, C.m_pos _⟩, false⟩

/-- **The turn.** -/
def vzTurn (C : VZ n m) (Zf : Finset ℤ) : VEndpt n m → VEndpt n m
  | Sum.inl x => vzTurnR C Zf x
  | Sum.inr b => vzTurnV C b

@[simp] theorem vzTurn_inl (C : VZ n m) (Zf : Finset ℤ) (x : Endpt n m) :
    vzTurn C Zf (Sum.inl x) = vzTurnR C Zf x := rfl

@[simp] theorem vzTurn_inr (C : VZ n m) (Zf : Finset ℤ) (b : Bool) :
    vzTurn C Zf (Sum.inr b) = vzTurnV C b := rfl

/-! ### The branch computations

Each is stated as an existential over a real end described by its three fields, or as
a bare equation when the target is virtual.  Nothing here mentions a `Fin` bound. -/


section Branches

variable (C : VZ n m) (Zf : Finset ℤ) (x : Endpt n m)

theorem vzR_bot_pair (hb : x.top = false) (hi : C.sp x.edge + 1 ≤ x.idx.val) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = (if (x.idx.val - C.sp x.edge) % 2 = 1 then x.idx.val + 1
        else x.idx.val - 1) ∧ y.top = false := by
  unfold vzTurnR; rw [dif_pos hb, dif_pos hi]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_bot_spine_pass (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : PassLo Zf x.edge)
    (hk : C.sp (edgePred x.edge) = 1) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val - 1 ∧
      y.idx.val = 0 ∧ y.top = true := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_pos hs, dif_pos hp, dif_pos hk]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_bot_spine_virt (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : PassLo Zf x.edge)
    (hk : ¬ (C.sp (edgePred x.edge) = 1)) :
    vzTurnR C Zf x = Sum.inr (!C.bl) := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_pos hs, dif_pos hp, dif_neg hk]

theorem vzR_bot_spine_bounce (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : ¬ PassLo Zf x.edge) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = C.sp x.edge ∧ y.top = false := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_pos hs, dif_neg hp]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_bot_chain_pass (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : PassLo Zf x.edge) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val - 1 ∧
      y.idx.val = m (edgePred x.edge) - 1 ∧ y.top = true := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_neg hs, dif_pos hp]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_bot_chain_bounce (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : ¬ PassLo Zf x.edge)
    (hk : C.sp x.edge = 1) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = 0 ∧ y.top = false := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_neg hs, dif_neg hp, dif_pos hk]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_bot_chain_virt (hb : x.top = false) (hi : ¬ (C.sp x.edge + 1 ≤ x.idx.val))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : ¬ PassLo Zf x.edge)
    (hk : ¬ (C.sp x.edge = 1)) :
    vzTurnR C Zf x = Sum.inr C.bl := by
  unfold vzTurnR; rw [dif_pos hb, dif_neg hi, dif_neg hs, dif_neg hp, dif_neg hk]

theorem vzR_top_pair (hb : x.top = true)
    (hi : C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = (if (x.idx.val - C.sp x.edge) % 2 = 0 then x.idx.val + 1
        else x.idx.val - 1) ∧ y.top = true := by
  unfold vzTurnR; rw [dif_neg (by simp [hb]), dif_pos hi]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_top_spine_pass (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : PassHi Zf x.edge)
    (hk : C.sp ⟨x.edge.val + 1, hp.1⟩ = 1) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val + 1 ∧
      y.idx.val = 0 ∧ y.top = false := by
  unfold vzTurnR
  rw [dif_neg (by simp [hb]), dif_neg hi, dif_pos hs, dif_pos hp, dif_pos hk]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_top_spine_virt (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : PassHi Zf x.edge)
    (hk : ¬ (C.sp ⟨x.edge.val + 1, hp.1⟩ = 1)) :
    vzTurnR C Zf x = Sum.inr C.bl := by
  unfold vzTurnR
  rw [dif_neg (by simp [hb]), dif_neg hi, dif_pos hs, dif_pos hp, dif_neg hk]

theorem vzR_top_spine_bounce (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : C.sp x.edge = 1 ∧ x.idx.val = 0) (hp : ¬ PassHi Zf x.edge) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = m x.edge - 1 ∧ y.top = true := by
  unfold vzTurnR; rw [dif_neg (by simp [hb]), dif_neg hi, dif_pos hs, dif_neg hp]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_top_chain_pass (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : PassHi Zf x.edge) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val + 1 ∧
      y.idx.val = C.sp ⟨x.edge.val + 1, hp.1⟩ ∧ y.top = false := by
  unfold vzTurnR; rw [dif_neg (by simp [hb]), dif_neg hi, dif_neg hs, dif_pos hp]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_top_chain_bounce (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : ¬ PassHi Zf x.edge)
    (hk : C.sp x.edge = 1) :
    ∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧
      y.idx.val = 0 ∧ y.top = true := by
  unfold vzTurnR
  rw [dif_neg (by simp [hb]), dif_neg hi, dif_neg hs, dif_neg hp, dif_pos hk]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzR_top_chain_virt (hb : x.top = true)
    (hi : ¬ (C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge))
    (hs : ¬ (C.sp x.edge = 1 ∧ x.idx.val = 0)) (hp : ¬ PassHi Zf x.edge)
    (hk : ¬ (C.sp x.edge = 1)) :
    vzTurnR C Zf x = Sum.inr (!C.bl) := by
  unfold vzTurnR
  rw [dif_neg (by simp [hb]), dif_neg hi, dif_neg hs, dif_neg hp, dif_neg hk]

theorem vzV_lo_zero (h0 : C.lo = 0) :
    ∃ y : Endpt n m, vzTurnV C C.bl = Sum.inl y ∧ y.edge.val = 0 ∧
      y.idx.val = 0 ∧ y.top = false := by
  unfold vzTurnV; rw [dif_pos rfl, dif_pos h0]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzV_lo_pos (h0 : ¬ (C.lo = 0)) :
    ∃ y : Endpt n m, vzTurnV C C.bl = Sum.inl y ∧ y.edge.val = C.lo - 1 ∧
      y.idx.val = 0 ∧ y.top = true := by
  unfold vzTurnV; rw [dif_pos rfl, dif_neg h0]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzV_hi_top (hn : C.hi = n) :
    ∃ y : Endpt n m, vzTurnV C (!C.bl) = Sum.inl y ∧ y.edge.val = n - 1 ∧
      y.idx.val = m y.edge - 1 ∧ y.top = true := by
  unfold vzTurnV; rw [dif_neg (by simp), dif_pos hn]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem vzV_hi_mid (hn : ¬ (C.hi = n)) :
    ∃ y : Endpt n m, vzTurnV C (!C.bl) = Sum.inl y ∧ y.edge.val = C.hi ∧
      y.idx.val = 0 ∧ y.top = false := by
  unfold vzTurnV; rw [dif_neg (by simp), dif_neg hn]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

end Branches

/-! ## Where the virtual points sit

`hZ` -- no cut site in the closed interval `[lo, hi]` -- is what makes the four
"virtual" branches of the turn line up with the four branches that point at them.  It
is the hypothesis `hgap` of `EltBridge.VEndpt.shield_gap`, and holds for a real
configuration because a cut site carries zero travel on both adjacent edges. -/

section Sits

/-- No cut site anywhere in `[lo, hi]`. -/
def NoCut (C : VZ n m) (Zf : Finset ℤ) : Prop :=
  ∀ z ∈ Zf, ¬ ((C.lo : ℤ) ≤ z ∧ z ≤ (C.hi : ℤ))

theorem mid_not_cut (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf)
    (t : ℕ) (h1 : C.lo ≤ t) (h2 : t ≤ C.hi) : ((t : ℕ) : ℤ) ∉ Zf :=
  fun h => hZ _ h ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem lo_not_cut (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    ((C.lo : ℕ) : ℤ) ∉ Zf := mid_not_cut C Zf hZ C.lo (le_refl _) (le_of_lt C.hlh)

theorem hi_not_cut (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    ((C.hi : ℕ) : ℤ) ∉ Zf := mid_not_cut C Zf hZ C.hi (le_of_lt C.hlh) (le_refl _)

/-- **A spine whose predecessor is a span edge sits at `hi`.** -/
theorem edge_eq_hi (C : VZ n m) {e : Fin n} (hs : C.sp e = 1) (he : 1 ≤ e.val)
    (hk : C.sp (edgePred e) = 0) : e.val = C.hi ∧ C.hi < n := by
  have h1 := C.sp_one_not_mem hs
  have h2 := C.sp_zero_mem hk
  rw [edgePred_val] at h2
  have := e.isLt
  omega

/-- **A spine whose successor is a span edge sits just below `lo`.** -/
theorem edge_eq_loPred (C : VZ n m) {e : Fin n} (hs : C.sp e = 1) (he : e.val + 1 < n)
    (hk : C.sp ⟨e.val + 1, he⟩ = 0) : C.lo = e.val + 1 ∧ C.lo ≠ 0 := by
  have h1 := C.sp_one_not_mem hs
  have h2 := C.sp_zero_mem hk
  simp only at h2
  omega

/-- **A span edge that bounces at its bottom site is edge `0`, and then `lo = 0`.** -/
theorem edge_eq_first (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) {e : Fin n}
    (hs : C.sp e = 0) (hp : ¬ PassLo Zf e) : e.val = 0 ∧ C.lo = 0 := by
  have h2 := C.sp_zero_mem hs
  have hnc : ((e.val : ℕ) : ℤ) ∉ Zf := mid_not_cut C Zf hZ e.val h2.1 (by omega)
  by_cases h1 : 1 ≤ e.val
  · exact absurd (⟨h1, hnc⟩ : PassLo Zf e) hp
  · exact ⟨by omega, by omega⟩

/-- **A span edge that bounces at its top site is edge `n - 1`, and then `hi = n`.** -/
theorem edge_eq_last (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) {e : Fin n}
    (hs : C.sp e = 0) (hp : ¬ PassHi Zf e) : e.val + 1 = n ∧ C.hi = n := by
  have h2 := C.sp_zero_mem hs
  have hnc : (((e.val + 1 : ℕ)) : ℤ) ∉ Zf :=
    mid_not_cut C Zf hZ (e.val + 1) (by omega) (by omega)
  have hcast : ((e.val : ℕ) : ℤ) + 1 = (((e.val + 1 : ℕ)) : ℤ) := by push_cast; ring
  have hlt := e.isLt
  have hhn := C.hhn
  by_cases hc : e.val + 1 < n
  · exact absurd (⟨hc, by rw [hcast]; exact hnc⟩ : PassHi Zf e) hp
  · exact ⟨by omega, by omega⟩

/-! ### And the reverse readings, at the four named edges -/

theorem sp_eFirst (C : VZ n m) (h0 : C.lo = 0) : C.sp C.eFirst = 0 := by
  refine C.sp_eq_zero ⟨?_, ?_⟩ <;> simp only [VZ.eFirst_val] <;>
    (have := C.hlh; omega)

theorem notPassLo_eFirst (C : VZ n m) (Zf : Finset ℤ) : ¬ PassLo Zf C.eFirst := by
  rintro ⟨h, -⟩; simp only [VZ.eFirst_val] at h; omega

theorem sp_eLast (C : VZ n m) (hn : C.hi = n) : C.sp C.eLast = 0 := by
  have h1 := C.hlh
  have h2 := C.n_pos
  refine C.sp_eq_zero ⟨?_, ?_⟩ <;> simp only [VZ.eLast_val] <;> omega

theorem notPassHi_eLast (C : VZ n m) (Zf : Finset ℤ) : ¬ PassHi Zf C.eLast := by
  rintro ⟨h, -⟩; simp only [VZ.eLast_val] at h; have := C.n_pos; omega

theorem sp_eLoPred (C : VZ n m) (h0 : C.lo ≠ 0) : C.sp C.eLoPred = 1 := by
  refine C.sp_eq_one ?_
  simp only [VZ.eLoPred_val]
  omega

theorem passHi_eLoPred (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (h0 : C.lo ≠ 0) :
    PassHi Zf C.eLoPred := by
  refine ⟨?_, ?_⟩
  · simp only [VZ.eLoPred_val]; have := C.hlh; have := C.hhn; omega
  · have hc : ((C.eLoPred.val : ℕ) : ℤ) + 1 = ((C.lo : ℕ) : ℤ) := by
      simp only [VZ.eLoPred_val]; omega
    rw [hc]; exact lo_not_cut C Zf hZ

theorem sp_eHi (C : VZ n m) (h : C.hi ≠ n) : C.sp (C.eHi h) = 1 := by
  refine C.sp_eq_one ?_
  simp only [VZ.eHi_val]
  omega

theorem passLo_eHi (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (h : C.hi ≠ n) :
    PassLo Zf (C.eHi h) := by
  refine ⟨?_, ?_⟩
  · simp only [VZ.eHi_val]; have := C.hlh; omega
  · simp only [VZ.eHi_val]; exact hi_not_cut C Zf hZ

theorem sp_edgePred_eHi (C : VZ n m) (h : C.hi ≠ n) : C.sp (edgePred (C.eHi h)) = 0 := by
  have := C.hlh
  refine C.sp_eq_zero ⟨?_, ?_⟩ <;> simp only [edgePred_val, VZ.eHi_val] <;> omega

end Sits

/-! ## Step 1: the turn is an involution -/

theorem sp_val_eq {C : VZ n m} {e f : Fin n} (h : e.val = f.val) : C.sp e = C.sp f := by
  rw [Fin.ext h]

theorem m_val_eq {e f : Fin n} (h : e.val = f.val) : m e = m f := by rw [Fin.ext h]

theorem sp_zero_val (C : VZ n m) (e : Fin n) (h1 : C.lo ≤ e.val) (h2 : e.val < C.hi) :
    C.sp e = 0 := C.sp_eq_zero ⟨h1, h2⟩

theorem sp_one_val (C : VZ n m) (e : Fin n) (h : e.val < C.lo ∨ C.hi ≤ e.val) :
    C.sp e = 1 := C.sp_eq_one (by omega)

/-- **The turn is an involution.** -/
theorem vz_invol (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (v : VEndpt n m) :
    vzTurn C Zf (vzTurn C Zf v) = v := by
  cases v with
  | inr b =>
    rw [vzTurn_inr]
    by_cases hbb : b = C.bl
    · subst hbb
      by_cases h0 : C.lo = 0
      · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_zero (m := m) C h0
        have hsp : C.sp y.edge = 0 :=
          sp_zero_val C y.edge (by omega) (by have := C.hlh; omega)
        rw [hy, vzTurn_inl]
        exact vzR_bot_chain_virt C Zf y hyt (by omega) (by rintro ⟨h1, -⟩; omega)
          (by intro hc; have := hc.1; omega) (by omega)
      · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_pos (m := m) C h0
        have hey : y.edge = C.eLoPred := Fin.ext (by rw [hye]; simp)
        have hsp : C.sp y.edge = 1 := by rw [hey]; exact sp_eLoPred C h0
        have hph : PassHi Zf y.edge := by rw [hey]; exact passHi_eLoPred C Zf hZ h0
        rw [hy, vzTurn_inl]
        refine vzR_top_spine_virt C Zf y hyt (by omega) ⟨hsp, hyi⟩ hph ?_
        have hk0 : C.sp (⟨y.edge.val + 1, hph.1⟩ : Fin n) = 0 :=
          sp_zero_val C _ (by show C.lo ≤ y.edge.val + 1; omega)
            (by show y.edge.val + 1 < C.hi; have := C.hlh; omega)
        omega
    · have hb2 : b = !C.bl := by cases b <;> cases hbl : C.bl <;> simp_all
      subst hb2
      by_cases hn : C.hi = n
      · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_top (m := m) C hn
        have hey : y.edge = C.eLast := Fin.ext (by rw [hye]; simp)
        have hsp : C.sp y.edge = 0 := by rw [hey]; exact sp_eLast C hn
        have hnp : ¬ PassHi Zf y.edge := by rw [hey]; exact notPassHi_eLast C Zf
        have hmp := C.m_pos y.edge
        rw [hy, vzTurn_inl]
        exact vzR_top_chain_virt C Zf y hyt (by rintro ⟨-, h2⟩; omega)
          (by rintro ⟨h1, -⟩; omega) hnp (by omega)
      · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_mid (m := m) C hn
        have hey : y.edge = C.eHi hn := Fin.ext (by rw [hye]; simp)
        have hsp : C.sp y.edge = 1 := by rw [hey]; exact sp_eHi C hn
        have hpl : PassLo Zf y.edge := by rw [hey]; exact passLo_eHi C Zf hZ hn
        have hkk : C.sp (edgePred y.edge) = 0 := by rw [hey]; exact sp_edgePred_eHi C hn
        rw [hy, vzTurn_inl]
        exact vzR_bot_spine_virt C Zf y hyt (by omega) ⟨hsp, hyi⟩ hpl (by omega)
  | inl x =>
    rw [vzTurn_inl]
    have hmpx := C.m_pos x.edge
    have hspx := C.sp_le x.edge
    have hparx := C.m_par x.edge
    have hltx := x.idx.isLt
    by_cases hb : x.top = false
    · -- ============================ bottom ends
      by_cases hi : C.sp x.edge + 1 ≤ x.idx.val
      · -- inside the chain
        obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_pair C Zf x hb hi
        have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
        have hmy : m y.edge = m x.edge := by rw [hye]
        rw [hy, vzTurn_inl]
        obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_bot_pair C Zf y hyt
          (by rw [hsp, hyi]; split_ifs <;> omega)
        rw [hz]
        refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
        · rw [hze, hye]
        · rw [hzi, hsp, hyi]; split_ifs <;> omega
        · rw [hzt, hb]
      · by_cases hs : C.sp x.edge = 1 ∧ x.idx.val = 0
        · -- the spine's bottom end
          by_cases hp : PassLo Zf x.edge
          · by_cases hk : C.sp (edgePred x.edge) = 1
            · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_spine_pass C Zf x hb hi hs hp hk
              have heyv : y.edge.val = (edgePred x.edge).val := by rw [hye, edgePred_val]
              have hsp : C.sp y.edge = 1 := by rw [sp_val_eq heyv]; exact hk
              have hph : PassHi Zf y.edge := by
                refine ⟨by have := x.edge.isLt; have := hp.1; omega, ?_⟩
                have hc : ((y.edge.val : ℕ) : ℤ) + 1 = ((x.edge.val : ℕ) : ℤ) := by
                  have := hp.1; omega
                rw [hc]; exact hp.2
              have hk2 : C.sp (⟨y.edge.val + 1, hph.1⟩ : Fin n) = C.sp x.edge :=
                sp_val_eq (by show y.edge.val + 1 = x.edge.val; have := hp.1; omega)
              rw [hy, vzTurn_inl]
              obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_top_spine_pass C Zf y hyt
                (by rintro ⟨h1, -⟩; omega) ⟨hsp, hyi⟩ hph (by rw [hk2]; exact hs.1)
              rw [hz]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hze, hye]; have := hp.1; omega
              · rw [hzi, hs.2]
              · rw [hzt, hb]
            · have hhi := edge_eq_hi C hs.1 hp.1
                (by have := C.sp_le (edgePred x.edge); omega)
              have hn : C.hi ≠ n := by omega
              rw [vzR_bot_spine_virt C Zf x hb hi hs hp hk, vzTurn_inr]
              obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_mid (m := m) C hn
              rw [hy]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hye, hhi.1]
              · rw [hyi, hs.2]
              · rw [hyt, hb]
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_spine_bounce C Zf x hb hi hs hp
            have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
            rw [hy, vzTurn_inl]
            obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_bot_chain_bounce C Zf y hyt
              (by omega) (by rintro ⟨-, h2⟩; omega) (by rw [hye]; exact hp)
              (by omega)
            rw [hz]
            refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
            · rw [hze, hye]
            · rw [hzi, hs.2]
            · rw [hzt, hb]
        · -- the chain's loose bottom end
          have hix : x.idx.val = C.sp x.edge := by
            by_cases h1 : C.sp x.edge = 1
            · omega
            · omega
          by_cases hp : PassLo Zf x.edge
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_chain_pass C Zf x hb hi hs hp
            have heyv : y.edge.val = (edgePred x.edge).val := by rw [hye, edgePred_val]
            have hsp : C.sp y.edge = C.sp (edgePred x.edge) := sp_val_eq heyv
            have hmy : m y.edge = m (edgePred x.edge) := m_val_eq heyv
            have hmyp := C.m_pos y.edge
            have hspy := C.sp_le y.edge
            have hlty := C.sp_lt y.edge
            have hph : PassHi Zf y.edge := by
              refine ⟨by have := x.edge.isLt; have := hp.1; omega, ?_⟩
              have hc : ((y.edge.val : ℕ) : ℤ) + 1 = ((x.edge.val : ℕ) : ℤ) := by
                have := hp.1; omega
              rw [hc]; exact hp.2
            have hk2 : C.sp (⟨y.edge.val + 1, hph.1⟩ : Fin n) = C.sp x.edge :=
              sp_val_eq (by show y.edge.val + 1 = x.edge.val; have := hp.1; omega)
            rw [hy, vzTurn_inl]
            obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_top_chain_pass C Zf y hyt
              (by rintro ⟨-, h2⟩; omega) (by rintro ⟨h1, h2⟩; omega) hph
            rw [hz]
            refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
            · rw [hze, hye]; have := hp.1; omega
            · rw [hzi, hk2, hix]
            · rw [hzt, hb]
          · by_cases hk : C.sp x.edge = 1
            · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_chain_bounce C Zf x hb hi hs hp hk
              have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
              rw [hy, vzTurn_inl]
              obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_bot_spine_bounce C Zf y hyt
                (by omega) ⟨by omega, hyi⟩ (by rw [hye]; exact hp)
              rw [hz]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hze, hye]
              · rw [hzi, hsp, hix]
              · rw [hzt, hb]
            · have hf := edge_eq_first C Zf hZ (by omega) hp
              rw [vzR_bot_chain_virt C Zf x hb hi hs hp hk, vzTurn_inr]
              obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_zero (m := m) C hf.2
              rw [hy]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hye, hf.1]
              · rw [hyi, hix]; omega
              · rw [hyt, hb]
    · -- ============================ top ends
      have hbt : x.top = true := by
        cases hxt : x.top
        · exact absurd hxt hb
        · rfl
      by_cases hi : C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge
      · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_pair C Zf x hbt hi
        have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
        have hmy : m y.edge = m x.edge := by rw [hye]
        rw [hy, vzTurn_inl]
        obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_top_pair C Zf y hyt
          (by
            constructor
            · rw [hsp, hyi]; split_ifs <;> omega
            · rw [hyi, hmy]; split_ifs <;> omega)
        rw [hz]
        refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
        · rw [hze, hye]
        · rw [hzi, hsp, hyi]; split_ifs <;> omega
        · rw [hzt, hbt]
      · by_cases hs : C.sp x.edge = 1 ∧ x.idx.val = 0
        · by_cases hp : PassHi Zf x.edge
          · by_cases hk : C.sp (⟨x.edge.val + 1, hp.1⟩ : Fin n) = 1
            · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_pass C Zf x hbt hi hs hp hk
              have heyv : y.edge.val = (⟨x.edge.val + 1, hp.1⟩ : Fin n).val := by
                show y.edge.val = x.edge.val + 1; exact hye
              have hsp : C.sp y.edge = 1 := by rw [sp_val_eq heyv]; exact hk
              have hpl : PassLo Zf y.edge := by
                refine ⟨by omega, ?_⟩
                have hc : ((y.edge.val : ℕ) : ℤ) = ((x.edge.val : ℕ) : ℤ) + 1 := by omega
                rw [hc]; exact hp.2
              have hk2 : C.sp (edgePred y.edge) = C.sp x.edge :=
                sp_val_eq (by rw [edgePred_val, hye]; omega)
              rw [hy, vzTurn_inl]
              obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_bot_spine_pass C Zf y hyt
                (by omega) ⟨hsp, hyi⟩ hpl (by rw [hk2]; exact hs.1)
              rw [hz]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hze, hye]; omega
              · rw [hzi, hs.2]
              · rw [hzt, hbt]
            · have hlp := edge_eq_loPred C hs.1 hp.1
                (by have := C.sp_le (⟨x.edge.val + 1, hp.1⟩ : Fin n); omega)
              rw [vzR_top_spine_virt C Zf x hbt hi hs hp hk, vzTurn_inr]
              obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_pos (m := m) C hlp.2
              rw [hy]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · omega
              · rw [hyi, hs.2]
              · rw [hyt, hbt]
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_bounce C Zf x hbt hi hs hp
            have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
            have hmy : m y.edge = m x.edge := by rw [hye]
            rw [hy, vzTurn_inl]
            obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_top_chain_bounce C Zf y hyt
              (by rintro ⟨-, h2⟩; omega) (by rintro ⟨h1, h2⟩; omega)
              (by rw [hye]; exact hp) (by omega)
            rw [hz]
            refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
            · rw [hze, hye]
            · rw [hzi, hs.2]
            · rw [hzt, hbt]
        · have hix : x.idx.val = m x.edge - 1 := by
            by_cases h1 : C.sp x.edge = 1
            · omega
            · omega
          by_cases hp : PassHi Zf x.edge
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_chain_pass C Zf x hbt hi hs hp
            have heyv : y.edge.val = (⟨x.edge.val + 1, hp.1⟩ : Fin n).val := by
              show y.edge.val = x.edge.val + 1; exact hye
            have hsp : C.sp y.edge = C.sp (⟨x.edge.val + 1, hp.1⟩ : Fin n) := sp_val_eq heyv
            have hspy := C.sp_le y.edge
            have hlty := C.sp_lt y.edge
            have hpl : PassLo Zf y.edge := by
              refine ⟨by omega, ?_⟩
              have hc : ((y.edge.val : ℕ) : ℤ) = ((x.edge.val : ℕ) : ℤ) + 1 := by omega
              rw [hc]; exact hp.2
            have hk2 : m (edgePred y.edge) = m x.edge :=
              m_val_eq (by rw [edgePred_val, hye]; omega)
            rw [hy, vzTurn_inl]
            obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_bot_chain_pass C Zf y hyt
              (by omega) (by rintro ⟨h1, h2⟩; omega) hpl
            rw [hz]
            refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
            · rw [hze, hye]; omega
            · rw [hzi, hk2, hix]
            · rw [hzt, hbt]
          · by_cases hk : C.sp x.edge = 1
            · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_chain_bounce C Zf x hbt hi hs hp hk
              have hsp : C.sp y.edge = C.sp x.edge := by rw [hye]
              have hmy : m y.edge = m x.edge := by rw [hye]
              rw [hy, vzTurn_inl]
              obtain ⟨z, hz, hze, hzi, hzt⟩ := vzR_top_spine_bounce C Zf y hyt
                (by rintro ⟨h1, h2⟩; omega) ⟨by omega, hyi⟩ (by rw [hye]; exact hp)
              rw [hz]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hze, hye]
              · rw [hzi, hmy, hix]
              · rw [hzt, hbt]
            · have hl := edge_eq_last C Zf hZ (by omega) hp
              rw [vzR_top_chain_virt C Zf x hbt hi hs hp hk, vzTurn_inr]
              obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_top (m := m) C hl.2
              have hmy : m y.edge = m x.edge := m_val_eq (by rw [hye]; omega)
              rw [hy]
              refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
              · rw [hye]; omega
              · rw [hyi, hmy, hix]
              · rw [hyt, hbt]

/-! ## Steps 2, 3, 5: one classification, and the three facts it yields

Rather than re-run the branch analysis three times, `vzR_class` says once and for all
what the turn of a REAL end is: same edge, a pass down at a non-cut site, a pass up at
a non-cut site, or one of the two virtual points, whose site it then matches.  Fixed-
point freedom, site preservation and `hturn` all read off it. -/

/-- The site of a real end, at the value level. -/
def rsite (x : Endpt n m) : ℤ := (x.edge.val : ℤ) + (if x.top then 1 else 0)

theorem siteOf_eq_rsite (x : Endpt n m) : EndType.siteOf x = rsite x := rfl

/-- The site of the virtual point at `lo`. -/
def vs0 (C : VZ n m) : ℤ := if C.bl then (C.hi : ℤ) else (C.lo : ℤ)
/-- The site of the virtual point at `hi`. -/
def vs1 (C : VZ n m) : ℤ := if C.bl then (C.lo : ℤ) else (C.hi : ℤ)

theorem siteP_inr (C : VZ n m) (b : Bool) :
    VEndpt.siteP (mm := m) (vs0 C) (vs1 C) (Sum.inr b) =
      if b = C.bl then (C.lo : ℤ) else (C.hi : ℤ) := by
  cases b <;> cases hbl : C.bl <;> simp [VEndpt.siteP, vs0, vs1, hbl]

theorem siteP_inl (C : VZ n m) (x : Endpt n m) :
    VEndpt.siteP (mm := m) (vs0 C) (vs1 C) (Sum.inl x) = rsite x := rfl

/-- **The classification of the turn on a real end.** -/
theorem vzR_class (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (x : Endpt n m) :
    (∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge = x.edge ∧ y.top = x.top ∧
        y.idx.val ≠ x.idx.val)
      ∨ (∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val - 1 ∧
        1 ≤ x.edge.val ∧ y.top = true ∧ x.top = false ∧ ((x.edge.val : ℕ) : ℤ) ∉ Zf)
      ∨ (∃ y : Endpt n m, vzTurnR C Zf x = Sum.inl y ∧ y.edge.val = x.edge.val + 1 ∧
        y.top = false ∧ x.top = true ∧ (((x.edge.val : ℕ) : ℤ) + 1) ∉ Zf)
      ∨ (vzTurnR C Zf x = Sum.inr C.bl ∧ rsite x = (C.lo : ℤ))
      ∨ (vzTurnR C Zf x = Sum.inr (!C.bl) ∧ rsite x = (C.hi : ℤ)) := by
  have hmpx := C.m_pos x.edge
  have hspx := C.sp_le x.edge
  have hparx := C.m_par x.edge
  have hltx := x.idx.isLt
  have hspl := C.sp_lt x.edge
  by_cases hb : x.top = false
  · have hrb : rsite x = ((x.edge.val : ℕ) : ℤ) := by unfold rsite; rw [hb]; simp
    by_cases hi : C.sp x.edge + 1 ≤ x.idx.val
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_pair C Zf x hb hi
      exact Or.inl ⟨y, hy, hye, by rw [hyt, hb], by rw [hyi]; split_ifs <;> omega⟩
    · by_cases hs : C.sp x.edge = 1 ∧ x.idx.val = 0
      · by_cases hp : PassLo Zf x.edge
        · by_cases hk : C.sp (edgePred x.edge) = 1
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_spine_pass C Zf x hb hi hs hp hk
            exact Or.inr (Or.inl ⟨y, hy, hye, hp.1, hyt, hb, hp.2⟩)
          · have hhi := edge_eq_hi C hs.1 hp.1
              (by have := C.sp_le (edgePred x.edge); omega)
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
            · exact vzR_bot_spine_virt C Zf x hb hi hs hp hk
            · obtain ⟨hh1, hh2⟩ := hhi; rw [hrb]; omega
        · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_spine_bounce C Zf x hb hi hs hp
          exact Or.inl ⟨y, hy, hye, by rw [hyt, hb], by omega⟩
      · have hix : x.idx.val = C.sp x.edge := by omega
        by_cases hp : PassLo Zf x.edge
        · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_chain_pass C Zf x hb hi hs hp
          exact Or.inr (Or.inl ⟨y, hy, hye, hp.1, hyt, hb, hp.2⟩)
        · by_cases hk : C.sp x.edge = 1
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_chain_bounce C Zf x hb hi hs hp hk
            exact Or.inl ⟨y, hy, hye, by rw [hyt, hb], by omega⟩
          · have hf := edge_eq_first C Zf hZ (by omega) hp
            refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
            · exact vzR_bot_chain_virt C Zf x hb hi hs hp hk
            · obtain ⟨hf1, hf2⟩ := hf; rw [hrb]; omega
  · have hbt : x.top = true := by
      cases hxt : x.top
      · exact absurd hxt hb
      · rfl
    have hrt : rsite x = ((x.edge.val : ℕ) : ℤ) + 1 := by unfold rsite; rw [hbt]; simp
    by_cases hi : C.sp x.edge ≤ x.idx.val ∧ x.idx.val + 2 ≤ m x.edge
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_pair C Zf x hbt hi
      exact Or.inl ⟨y, hy, hye, by rw [hyt, hbt], by rw [hyi]; split_ifs <;> omega⟩
    · by_cases hs : C.sp x.edge = 1 ∧ x.idx.val = 0
      · by_cases hp : PassHi Zf x.edge
        · by_cases hk : C.sp (⟨x.edge.val + 1, hp.1⟩ : Fin n) = 1
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_pass C Zf x hbt hi hs hp hk
            exact Or.inr (Or.inr (Or.inl ⟨y, hy, hye, hyt, hbt, hp.2⟩))
          · have hlp := edge_eq_loPred C hs.1 hp.1
              (by have := C.sp_le (⟨x.edge.val + 1, hp.1⟩ : Fin n); omega)
            refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
            · exact vzR_top_spine_virt C Zf x hbt hi hs hp hk
            · obtain ⟨hl1, hl2⟩ := hlp; rw [hrt]; omega
        · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_bounce C Zf x hbt hi hs hp
          exact Or.inl ⟨y, hy, hye, by rw [hyt, hbt], by omega⟩
      · have hix : x.idx.val = m x.edge - 1 := by omega
        by_cases hp : PassHi Zf x.edge
        · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_chain_pass C Zf x hbt hi hs hp
          exact Or.inr (Or.inr (Or.inl ⟨y, hy, hye, hyt, hbt, hp.2⟩))
        · by_cases hk : C.sp x.edge = 1
          · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_chain_bounce C Zf x hbt hi hs hp hk
            exact Or.inl ⟨y, hy, hye, by rw [hyt, hbt], by omega⟩
          · have hl := edge_eq_last C Zf hZ (by omega) hp
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
            · exact vzR_top_chain_virt C Zf x hbt hi hs hp hk
            · obtain ⟨hl1, hl2⟩ := hl; rw [hrt]; omega

/-! ### The three facts -/

theorem rsite_bot (x : Endpt n m) (h : x.top = false) : rsite x = ((x.edge.val : ℕ) : ℤ) := by
  unfold rsite; rw [h]; simp

theorem rsite_top (x : Endpt n m) (h : x.top = true) :
    rsite x = ((x.edge.val : ℕ) : ℤ) + 1 := by
  unfold rsite; rw [h]; simp

theorem vzV_inl (C : VZ n m) (b : Bool) : ∃ y : Endpt n m, vzTurnV C b = Sum.inl y := by
  unfold vzTurnV; split_ifs <;> exact ⟨_, rfl⟩

/-- **The turn of a virtual point sits at that point's own site.** -/
theorem vzV_site (C : VZ n m) (b : Bool) :
    VEndpt.siteP (mm := m) (vs0 C) (vs1 C) (vzTurnV C b)
      = VEndpt.siteP (mm := m) (vs0 C) (vs1 C) (Sum.inr b) := by
  rw [siteP_inr]
  by_cases hbb : b = C.bl
  · rw [if_pos hbb]
    subst hbb
    by_cases h0 : C.lo = 0
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_zero (m := m) C h0
      rw [hy, siteP_inl, rsite_bot y hyt]; omega
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_pos (m := m) C h0
      rw [hy, siteP_inl, rsite_top y hyt]; omega
  · rw [if_neg hbb]
    have hb2 : b = !C.bl := by cases b <;> cases hbl : C.bl <;> simp_all
    subst hb2
    by_cases hn : C.hi = n
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_top (m := m) C hn
      have := C.n_pos
      rw [hy, siteP_inl, rsite_top y hyt]; omega
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_mid (m := m) C hn
      rw [hy, siteP_inl, rsite_bot y hyt]; omega

/-- **The turn preserves sites.** -/
theorem vz_site (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (v : VEndpt n m) :
    VEndpt.siteP (mm := m) (vs0 C) (vs1 C) (vzTurn C Zf v)
      = VEndpt.siteP (mm := m) (vs0 C) (vs1 C) v := by
  cases v with
  | inr b => rw [vzTurn_inr]; exact vzV_site C b
  | inl x =>
    rw [vzTurn_inl, siteP_inl]
    rcases vzR_class C Zf hZ x with ⟨y, hy, he, ht, -⟩ | ⟨y, hy, he, h1, hyt, hxt, -⟩ |
      ⟨y, hy, he, hyt, hxt, -⟩ | ⟨hy, hs⟩ | ⟨hy, hs⟩
    · rw [hy, siteP_inl]; unfold rsite; rw [he, ht]
    · rw [hy, siteP_inl, rsite_top y hyt, rsite_bot x hxt]; omega
    · rw [hy, siteP_inl, rsite_bot y hyt, rsite_top x hxt]; omega
    · rw [hy, siteP_inr, if_pos rfl]; exact hs.symm
    · rw [hy, siteP_inr, if_neg (by simp)]; exact hs.symm

/-- **The turn has no fixed point.** -/
theorem vz_ne (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (v : VEndpt n m) :
    vzTurn C Zf v ≠ v := by
  cases v with
  | inr b =>
    obtain ⟨y, hy⟩ := vzV_inl (m := m) C b
    rw [vzTurn_inr, hy]; simp
  | inl x =>
    rw [vzTurn_inl]
    rcases vzR_class C Zf hZ x with ⟨y, hy, he, ht, hne⟩ | ⟨y, hy, he, h1, hyt, hxt, -⟩ |
      ⟨y, hy, he, hyt, hxt, -⟩ | ⟨hy, -⟩ | ⟨hy, -⟩
    · rw [hy]; intro hc
      exact hne (congrArg (fun w : Endpt n m => (w.idx : ℕ)) (Sum.inl.inj hc))
    · rw [hy]; intro hc
      have := congrArg Endpt.top (Sum.inl.inj hc)
      rw [hyt, hxt] at this; exact Bool.noConfusion this
    · rw [hy]; intro hc
      have := congrArg Endpt.top (Sum.inl.inj hc)
      rw [hyt, hxt] at this; exact Bool.noConfusion this
    · rw [hy]; simp
    · rw [hy]; simp

/-- **`hturn`: a turn that changes edge sits at a site that is not cut.** -/
theorem vz_hturn (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (u v : Endpt n m)
    (huv : vzTurn C Zf (Sum.inl u) = Sum.inl v)
    (hne : EndType.edgeOf u ≠ EndType.edgeOf v) : EndType.siteOf u ∉ Zf := by
  rw [vzTurn_inl] at huv
  rcases vzR_class C Zf hZ u with ⟨y, hy, he, ht, -⟩ | ⟨y, hy, he, h1, hyt, hxt, hnc⟩ |
    ⟨y, hy, he, hyt, hxt, hnc⟩ | ⟨hy, -⟩ | ⟨hy, -⟩
  · rw [hy] at huv
    have hvy : v = y := (Sum.inl.inj huv).symm
    exact absurd (by unfold EndType.edgeOf; rw [hvy, he]) hne
  · rw [siteOf_eq_rsite, rsite_bot u hxt]; exact hnc
  · rw [siteOf_eq_rsite, rsite_top u hxt]; exact hnc
  · rw [hy] at huv; simp at huv
  · rw [hy] at huv; simp at huv

/-! ## Step 4: the walk-graph data -/

theorem vs0_ne_vs1 (C : VZ n m) : vs0 C ≠ vs1 C := by
  have := C.hlh
  unfold vs0 vs1
  cases C.bl <;> simp <;> omega

/-- **The odd-span walk-graph data.**  The crossing map is `VEndpt.partner` on the nose,
so `hEp` is `rfl`; the turn is the odd-span zigzag. -/
def vzData (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    WalkGraph.Data (VEndpt n m) where
  p := VEndpt.partner
  t := vzTurn C Zf
  p_invol := VEndpt.partner_invol
  t_invol := vz_invol C Zf hZ
  p_ne := VEndpt.partner_ne
  t_ne := vz_ne C Zf hZ
  pt_ne := TurnBuild.partner_ne_turn (VEndpt.siteP (mm := m) (vs0 C) (vs1 C))
    VEndpt.partner (vzTurn C Zf)
    (fun y => VEndpt.partner_site_neP (vs0 C) (vs1 C) (vs0_ne_vs1 C) y)
    (fun y => vz_site C Zf hZ y)

@[simp] theorem vzData_p (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    (vzData C Zf hZ).p = VEndpt.partner := rfl

@[simp] theorem vzData_t (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    (vzData C Zf hZ).t = vzTurn C Zf := rfl

end VZigzag

-- Certification (Rule 5).
#print axioms VZigzag.VZ.m_par
#print axioms VZigzag.VZ.sp_lt
#print axioms VZigzag.vzR_bot_pair
#print axioms VZigzag.vzR_bot_spine_pass
#print axioms VZigzag.vzR_bot_spine_virt
#print axioms VZigzag.vzR_bot_spine_bounce
#print axioms VZigzag.vzR_bot_chain_pass
#print axioms VZigzag.vzR_bot_chain_bounce
#print axioms VZigzag.vzR_bot_chain_virt
#print axioms VZigzag.vzR_top_pair
#print axioms VZigzag.vzR_top_spine_pass
#print axioms VZigzag.vzR_top_spine_virt
#print axioms VZigzag.vzR_top_spine_bounce
#print axioms VZigzag.vzR_top_chain_pass
#print axioms VZigzag.vzR_top_chain_bounce
#print axioms VZigzag.vzR_top_chain_virt
#print axioms VZigzag.vzV_lo_zero
#print axioms VZigzag.vzV_lo_pos
#print axioms VZigzag.vzV_hi_top
#print axioms VZigzag.vzV_hi_mid
#print axioms VZigzag.edge_eq_hi
#print axioms VZigzag.edge_eq_loPred
#print axioms VZigzag.edge_eq_first
#print axioms VZigzag.edge_eq_last
#print axioms VZigzag.vz_invol
#print axioms VZigzag.vzR_class
#print axioms VZigzag.vz_site
#print axioms VZigzag.vz_ne
#print axioms VZigzag.vz_hturn
#print axioms VZigzag.vzData
