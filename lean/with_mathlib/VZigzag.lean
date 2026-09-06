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
import TravelParity

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

/-! ## Generic `AllJoined` plumbing

`EltBridge`'s versions are stated for `EndType.Endpt` through `botOf`; nothing in their
proofs uses that, so here they are with the representative map as a parameter. -/

section Generic

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Any turn step joins the two representatives. -/
theorem link_of_turn_gen (E : WalkGraph.Data α) (base : α → α)
    (hbase : ∀ x, base x = x ∨ base x = E.p x) (x : α) :
    (WalkGraph.graph E).Reachable (base x) (base (E.t x)) :=
  (((reachable_to_base E base hbase x).symm).trans (reachable_turn E x)).trans
    (reachable_to_base E base hbase (E.t x))

/-- A chain of turn steps joins a whole family of representatives. -/
theorem allJoined_step_gen (E : WalkGraph.Data α) (base : α → α)
    (hbase : ∀ x, base x = x ∨ base x = E.p x) (f : ℕ → α) (N : ℕ)
    (h : ∀ i : ℕ, i < N → base (E.t (f i)) = base (f (i + 1))) :
    AllJoined (WalkGraph.graph E) ((Finset.range (N + 1)).image (fun i => base (f i))) := by
  refine allJoined_image (WalkGraph.graph E) (fun i => base (f i)) N ?_
  intro i hi
  have hr := link_of_turn_gen E base hbase (f i)
  rw [h i hi] at hr
  exact hr

/-- **Absorbing a family, with a mere reachability at each link.**  Weaker than
`EltBridge.allJoined_biUnion`, which asks for a single turn step: here consecutive sets
may even coincide, which is what happens along the travel span, where the "spine slot"
is the one virtual strand for every edge at once. -/
theorem allJoined_biUnion_gen (G : SimpleGraph α) (S : ℕ → Finset α) (N : ℕ)
    (hS : ∀ j, AllJoined G (S j))
    (hlink : ∀ j, j < N → ∃ p ∈ S j, ∃ q ∈ S (j + 1), G.Reachable p q) :
    ∀ j : ℕ, j ≤ N → AllJoined G ((Finset.range (j + 1)).biUnion S) := by
  intro j
  induction j with
  | zero => intro _; simpa using hS 0
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    obtain ⟨p, hp, q, hq, hpq⟩ := hlink k (by omega)
    have hrw : (Finset.range (k + 1 + 1)).biUnion S
        = ((Finset.range (k + 1)).biUnion S) ∪ S (k + 1) := by
      rw [Finset.range_add_one, Finset.biUnion_insert]
      exact Finset.union_comm _ _
    rw [hrw]
    exact allJoined_union G _ _ hprev (hS (k + 1)) p q
      (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hp⟩) hq hpq

/-- **A joined set per run gives `hrun` on representatives.** -/
theorem hrun_of_allJoined_gen (G : SimpleGraph α) (base : α → α) (idx : α → ℕ)
    (S : ℕ → Finset α) (hS : ∀ r, AllJoined G (S r)) (hmem : ∀ x, base x ∈ S (idx x)) :
    ∀ x y : α, idx x = idx y → G.Reachable (base x) (base y) := by
  intro x y hxy
  have hx := hmem x
  have hy := hmem y
  rw [hxy] at hx
  exact hS _ _ hx _ hy

end Generic

/-! ## The representative of a strand -/

/-- The bottom end of a point's own strand: for a real end its crossing's bottom, for a
virtual end the tag `false`. -/
def vbot : VEndpt n m → VEndpt n m
  | Sum.inl x => Sum.inl (botOf x)
  | Sum.inr _ => Sum.inr false

@[simp] theorem vbot_inl (x : Endpt n m) : vbot (Sum.inl x) = Sum.inl (botOf x) := rfl
@[simp] theorem vbot_inr (b : Bool) : vbot (Sum.inr b : VEndpt n m) = Sum.inr false := rfl

theorem vbot_eq_or_partner (v : VEndpt n m) :
    vbot v = v ∨ vbot v = VEndpt.partner v := by
  cases v with
  | inl x =>
    rcases botOf_eq_or_partner x with h | h
    · exact Or.inl (by rw [vbot_inl, h])
    · exact Or.inr (by rw [vbot_inl, h]; rfl)
  | inr b => cases b
             · exact Or.inl rfl
             · exact Or.inr rfl

theorem vbot_edgeOf (bnd : ℤ) (v : VEndpt n m) :
    VEndpt.edgeOf bnd (vbot v) = VEndpt.edgeOf bnd v := by
  cases v with
  | inl x => rfl
  | inr b => rfl

/-! ## The zigzag chain of one edge

Strands `sp e .. m e - 1`, an odd number of them, wired into a single path from strand
`sp e`'s bottom end to strand `m e - 1`'s top end. -/

/-- The `i`-th end of edge `e`'s chain: strand `m e - 1 - i`, approached from the bottom
when `i` is even and from the top when `i` is odd. -/
def fC (C : VZ n m) (e : Fin n) (i : ℕ) : Endpt n m :=
  ⟨e, ⟨m e - 1 - i, by have := C.m_pos e; omega⟩, decide (i % 2 = 1)⟩

@[simp] theorem fC_edge (C : VZ n m) (e : Fin n) (i : ℕ) : (fC C e i).edge = e := rfl
@[simp] theorem fC_idx (C : VZ n m) (e : Fin n) (i : ℕ) :
    (fC C e i).idx.val = m e - 1 - i := rfl
@[simp] theorem fC_top (C : VZ n m) (e : Fin n) (i : ℕ) :
    (fC C e i).top = decide (i % 2 = 1) := rfl

/-- **The chain step.**  This is the only place the width parity is used: it is what
makes the two internal pairings exhaust the chain. -/
theorem vzC_step (C : VZ n m) (Zf : Finset ℤ) (e : Fin n) (i : ℕ)
    (hi : i < m e - C.sp e - 1) :
    vbot (vzTurn C Zf (Sum.inl (fC C e i))) = vbot (Sum.inl (fC C e (i + 1))) := by
  have hsp := C.sp_le e
  have hpar := C.m_par e
  have hmp := C.m_pos e
  have hlt := C.sp_lt e
  by_cases hp2 : i % 2 = 1
  · have hbt : (fC C e i).top = true := by rw [fC_top]; exact decide_eq_true hp2
    obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_pair C Zf (fC C e i) hbt
      (by show C.sp e ≤ m e - 1 - i ∧ m e - 1 - i + 2 ≤ m e; omega)
    rw [vzTurn_inl, hy, vbot_inl, vbot_inl]
    refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
    · simp only [botOf_edge, hye, fC_edge]
    · simp only [botOf_idx_val, hyi, fC_edge, fC_idx]
      split_ifs <;> omega
  · have hbt : (fC C e i).top = false := by rw [fC_top]; exact decide_eq_false hp2
    obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_pair C Zf (fC C e i) hbt
      (by show C.sp e + 1 ≤ m e - 1 - i; omega)
    rw [vzTurn_inl, hy, vbot_inl, vbot_inl]
    refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
    · simp only [botOf_edge, hye, fC_edge]
    · simp only [botOf_idx_val, hyi, fC_edge, fC_idx]
      split_ifs <;> omega

/-- The chain of edge `e`, as a set of representatives. -/
def vChain (C : VZ n m) (e : Fin n) : Finset (VEndpt n m) :=
  (Finset.range (m e - C.sp e)).image (fun i => vbot (Sum.inl (fC C e i)))

/-- **Each edge's chain is joined.** -/
theorem vChain_joined (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (e : Fin n) :
    AllJoined (WalkGraph.graph (vzData C Zf hZ)) (vChain C e) := by
  have h := allJoined_step_gen (vzData C Zf hZ) vbot
    (fun x => by rw [vzData_p]; exact vbot_eq_or_partner x) (fun i => Sum.inl (fC C e i))
    (m e - C.sp e - 1) (fun i hi => by rw [vzData_t]; exact vzC_step C Zf e i hi)
  have hrw : m e - C.sp e - 1 + 1 = m e - C.sp e := by
    have := C.sp_lt e; omega
  rw [hrw] at h
  exact h

/-! ### Named ends and membership in the chain -/

/-- The bottom end of edge `e`'s spine (only meaningful when `sp e = 1`). -/
def spineB (C : VZ n m) (e : Fin n) : Endpt n m := ⟨e, ⟨0, C.m_pos e⟩, false⟩
/-- The top end of edge `e`'s spine. -/
def spineT (C : VZ n m) (e : Fin n) : Endpt n m := ⟨e, ⟨0, C.m_pos e⟩, true⟩
/-- The loose bottom end of edge `e`'s chain: strand `sp e`. -/
def chainB (C : VZ n m) (e : Fin n) : Endpt n m := ⟨e, ⟨C.sp e, C.sp_lt e⟩, false⟩

@[simp] theorem spineB_edge (C : VZ n m) (e : Fin n) : (spineB C e).edge = e := rfl
@[simp] theorem spineB_idx (C : VZ n m) (e : Fin n) : (spineB C e).idx.val = 0 := rfl
@[simp] theorem spineB_top (C : VZ n m) (e : Fin n) : (spineB C e).top = false := rfl
@[simp] theorem spineT_edge (C : VZ n m) (e : Fin n) : (spineT C e).edge = e := rfl
@[simp] theorem spineT_idx (C : VZ n m) (e : Fin n) : (spineT C e).idx.val = 0 := rfl
@[simp] theorem spineT_top (C : VZ n m) (e : Fin n) : (spineT C e).top = true := rfl
@[simp] theorem chainB_edge (C : VZ n m) (e : Fin n) : (chainB C e).edge = e := rfl
@[simp] theorem chainB_idx (C : VZ n m) (e : Fin n) : (chainB C e).idx.val = C.sp e := rfl
@[simp] theorem chainB_top (C : VZ n m) (e : Fin n) : (chainB C e).top = false := rfl

theorem vbot_spineT (C : VZ n m) (e : Fin n) :
    vbot (Sum.inl (spineT C e)) = Sum.inl (spineB C e) := rfl

theorem fC_zero_mem (C : VZ n m) (e : Fin n) :
    vbot (Sum.inl (fC C e 0)) ∈ vChain C e :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by have := C.sp_lt e; omega), rfl⟩

theorem chainB_mem (C : VZ n m) (e : Fin n) :
    vbot (Sum.inl (chainB C e)) ∈ vChain C e := by
  have hlt := C.sp_lt e
  refine Finset.mem_image.mpr ⟨m e - C.sp e - 1, Finset.mem_range.mpr (by omega), ?_⟩
  refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
  · simp only [botOf_edge, fC_edge, chainB_edge]
  · simp only [botOf_idx_val, fC_idx, chainB_idx]; omega

theorem vbot_mem_vChain (C : VZ n m) (x : Endpt n m) (h : C.sp x.edge ≤ x.idx.val) :
    vbot (Sum.inl x) ∈ vChain C x.edge := by
  have hlt := x.idx.isLt
  have hsl := C.sp_lt x.edge
  refine Finset.mem_image.mpr ⟨m x.edge - 1 - x.idx.val, Finset.mem_range.mpr (by omega), ?_⟩
  refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
  · simp only [botOf_edge, fC_edge]
  · simp only [botOf_idx_val, fC_idx]; omega

/-! ### The local turn steps the assembly consumes -/

/-- A spine passes up to the next spine. -/
theorem vz_spine_pass (C : VZ n m) (Zf : Finset ℤ) (e f : Fin n) (hse : C.sp e = 1)
    (hsf : C.sp f = 1) (hp : PassHi Zf e) (hf : f.val = e.val + 1) :
    vbot (vzTurn C Zf (Sum.inl (spineT C e))) = Sum.inl (spineB C f) := by
  have hk : C.sp (⟨e.val + 1, hp.1⟩ : Fin n) = 1 := by
    rw [sp_val_eq (show ((⟨e.val + 1, hp.1⟩ : Fin n)).val = f.val from by
      show e.val + 1 = f.val; omega)]
    exact hsf
  obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_pass C Zf (spineT C e) rfl
    (by show ¬ (C.sp e ≤ 0 ∧ 0 + 2 ≤ m e); rintro ⟨h1, -⟩; omega)
    ⟨by rw [spineT_edge]; exact hse, rfl⟩ (by rw [spineT_edge]; exact hp)
    (by exact hk)
  rw [vzTurn_inl, hy, vbot_inl]
  refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
  · simp only [botOf_edge, spineB_edge]; rw [hye, spineT_edge]; omega
  · simp only [botOf_idx_val, spineB_idx]; exact hyi
  · rfl

/-- A spine at the bottom of the span passes up into the virtual strand. -/
theorem vz_spine_virt (C : VZ n m) (Zf : Finset ℤ) (e f : Fin n) (hse : C.sp e = 1)
    (hsf : C.sp f = 0) (hp : PassHi Zf e) (hf : f.val = e.val + 1) :
    vbot (vzTurn C Zf (Sum.inl (spineT C e))) = (Sum.inr false : VEndpt n m) := by
  have hk : ¬ (C.sp (⟨e.val + 1, hp.1⟩ : Fin n) = 1) := by
    rw [sp_val_eq (show ((⟨e.val + 1, hp.1⟩ : Fin n)).val = f.val from by
      show e.val + 1 = f.val; omega)]
    omega
  rw [vzTurn_inl, vzR_top_spine_virt C Zf (spineT C e) rfl
    (by show ¬ (C.sp e ≤ 0 ∧ 0 + 2 ≤ m e); rintro ⟨h1, -⟩; omega)
    ⟨by rw [spineT_edge]; exact hse, rfl⟩ (by rw [spineT_edge]; exact hp)
    (by exact hk), vbot_inr]

/-- The virtual strand passes up into the first spine above the span. -/
theorem vz_virt_spine (C : VZ n m) (Zf : Finset ℤ) (hn : C.hi ≠ n) (f : Fin n)
    (hf : f.val = C.hi) :
    vbot (vzTurn C Zf (Sum.inr (!C.bl))) = Sum.inl (spineB C f) := by
  obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_mid (m := m) C hn
  rw [vzTurn_inr, hy, vbot_inl]
  refine congrArg Sum.inl (endpt_ext ?_ ?_ ?_)
  · simp only [botOf_edge, spineB_edge]; omega
  · simp only [botOf_idx_val, spineB_idx]; exact hyi
  · rfl

/-- At the top of a run the spine bounces into its own chain. -/
theorem vz_spine_bounce (C : VZ n m) (Zf : Finset ℤ) (e : Fin n) (hse : C.sp e = 1)
    (hp : ¬ PassHi Zf e) :
    vbot (vzTurn C Zf (Sum.inl (spineT C e))) = vbot (Sum.inl (fC C e 0)) := by
  obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_top_spine_bounce C Zf (spineT C e) rfl
    (by show ¬ (C.sp e ≤ 0 ∧ 0 + 2 ≤ m e); rintro ⟨h1, -⟩; omega)
    ⟨by rw [spineT_edge]; exact hse, rfl⟩ (by rw [spineT_edge]; exact hp)
  rw [vzTurn_inl, hy, vbot_inl, vbot_inl]
  refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
  · simp only [botOf_edge, hye, spineT_edge, fC_edge]
  · simp only [botOf_idx_val, hyi, spineT_edge, fC_idx]; omega

/-- At the top of the chain of edges the virtual strand bounces into the last chain. -/
theorem vz_virt_bounce (C : VZ n m) (Zf : Finset ℤ) (hn : C.hi = n) (e : Fin n)
    (he : e.val = n - 1) :
    vbot (vzTurn C Zf (Sum.inr (!C.bl))) = vbot (Sum.inl (fC C e 0)) := by
  obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_top (m := m) C hn
  have hey : y.edge.val = e.val := by omega
  rw [vzTurn_inr, hy, vbot_inl, vbot_inl]
  refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
  · simp only [botOf_edge, fC_edge]; exact hey
  · simp only [botOf_idx_val, fC_idx]
    rw [hyi, m_val_eq (m := m) hey]; omega

/-- The chain's loose bottom passes down into the previous chain's loose top. -/
theorem vz_chain_pass (C : VZ n m) (Zf : Finset ℤ) (e f : Fin n) (hp : PassLo Zf e)
    (hf : f.val = e.val - 1) :
    vbot (vzTurn C Zf (Sum.inl (chainB C e))) = vbot (Sum.inl (fC C f 0)) := by
  have hsl := C.sp_le e
  obtain ⟨y, hy, hye, hyi, hyt⟩ := vzR_bot_chain_pass C Zf (chainB C e) rfl
    (by show ¬ (C.sp e + 1 ≤ C.sp e); omega)
    (by show ¬ (C.sp e = 1 ∧ C.sp e = 0); rintro ⟨h1, h2⟩; omega)
    (by rw [chainB_edge]; exact hp)
  have hef : (edgePred (chainB C e).edge).val = f.val := by
    rw [chainB_edge, edgePred_val]; omega
  rw [vzTurn_inl, hy, vbot_inl, vbot_inl]
  refine congrArg Sum.inl (endpt_ext ?_ ?_ rfl)
  · simp only [botOf_edge, fC_edge]; rw [hye, chainB_edge]; omega
  · simp only [botOf_idx_val, fC_idx]
    rw [hyi, m_val_eq (m := m) hef]; omega

/-! ## The run's joined set

A run is an interval `[a, b]` of edges (`EltBridge.runSet_interval`).  Its cycle is:
the spine line up -- with the one virtual strand standing in for the span's missing
spines -- then a bounce at the top, then the chains coming back down. -/

/-- Edge `lo`, the bottom edge of the span. -/
def eLoE (C : VZ n m) : Fin n := ⟨C.lo, by have := C.hlh; have := C.hhn; omega⟩

@[simp] theorem eLoE_val (C : VZ n m) : (eLoE C).val = C.lo := rfl

theorem sp_eLoE (C : VZ n m) : C.sp (eLoE C) = 0 :=
  sp_zero_val C _ (by simp) (by simp only [eLoE_val]; exact C.hlh)

/-- The `j`-th slot of run `[a, b]`. -/
def vFam (C : VZ n m) (a b : Fin n) (j : ℕ) : Finset (VEndpt n m) :=
  if j ≤ b.val - a.val then
    (if C.sp (eAdd a j) = 1 then {Sum.inl (spineB C (eAdd a j))}
      else {(Sum.inr false : VEndpt n m)})
  else if j ≤ 2 * (b.val - a.val) + 1 then vChain C (eSub b (j - (b.val - a.val) - 1))
  else ∅

theorem vFam_lo_spine (C : VZ n m) (a b : Fin n) (j : ℕ) (h : j ≤ b.val - a.val)
    (hs : C.sp (eAdd a j) = 1) : vFam C a b j = {Sum.inl (spineB C (eAdd a j))} := by
  unfold vFam; rw [if_pos h, if_pos hs]

theorem vFam_lo_virt (C : VZ n m) (a b : Fin n) (j : ℕ) (h : j ≤ b.val - a.val)
    (hs : ¬ (C.sp (eAdd a j) = 1)) :
    vFam C a b j = {(Sum.inr false : VEndpt n m)} := by
  unfold vFam; rw [if_pos h, if_neg hs]

theorem vFam_hi' (C : VZ n m) (a b : Fin n) (k : ℕ) (h2 : k ≤ b.val - a.val) :
    vFam C a b (b.val - a.val + 1 + k) = vChain C (eSub b k) := by
  unfold vFam
  rw [if_neg (by omega : ¬ (b.val - a.val + 1 + k ≤ b.val - a.val)),
    if_pos (by omega : b.val - a.val + 1 + k ≤ 2 * (b.val - a.val) + 1),
    show b.val - a.val + 1 + k - (b.val - a.val) - 1 = k from by omega]

theorem vFam_joined (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (a b : Fin n) (j : ℕ) :
    AllJoined (WalkGraph.graph (vzData C Zf hZ)) (vFam C a b j) := by
  unfold vFam
  split_ifs
  · exact allJoined_singleton _ _
  · exact allJoined_singleton _ _
  · exact vChain_joined C Zf hZ _
  · exact allJoined_empty _

/-- **The run's strands are all joined.** -/
theorem vz_run_joined (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (r : ℕ) (a b : Fin n)
    (ha : a ∈ runSet Zf r) (hb : b ∈ runSet Zf r)
    (hmin : ∀ e : Fin n, e ∈ runSet Zf r → a.val ≤ e.val)
    (hmax : ∀ e : Fin n, e ∈ runSet Zf r → e.val ≤ b.val) :
    AllJoined (WalkGraph.graph (vzData C Zf hZ))
      ((Finset.range (2 * (b.val - a.val) + 1 + 1)).biUnion (vFam C a b)) := by
  have hab : a.val ≤ b.val := hmin b hb
  have hbn := b.isLt
  have hbase : ∀ x : VEndpt n m, vbot x = x ∨ vbot x = (vzData C Zf hZ).p x :=
    fun x => by rw [vzData_p]; exact vbot_eq_or_partner x
  refine allJoined_biUnion_gen (WalkGraph.graph (vzData C Zf hZ)) (vFam C a b)
    (2 * (b.val - a.val) + 1) (fun j => vFam_joined C Zf hZ a b j) ?_ _ (le_refl _)
  intro j hj
  rcases Nat.lt_or_ge j (b.val - a.val) with hjd | hjd
  · -- a step along the spine line, strictly inside the run
    have hj1 : j ≤ b.val - a.val := le_of_lt hjd
    have hj2 : j + 1 ≤ b.val - a.val := hjd
    have hva : (eAdd a j).val = a.val + j := eAdd_val a j (by omega)
    have hva1 : (eAdd a (j + 1)).val = a.val + (j + 1) := eAdd_val a (j + 1) (by omega)
    have hmem : eAdd a j ∈ runSet Zf r := eAdd_mem_runSet Zf r ha hb j hj1 hab
    have hmem1 : eAdd a (j + 1) ∈ runSet Zf r := eAdd_mem_runSet Zf r ha hb (j + 1) hj2 hab
    have hpass : PassHi Zf (eAdd a j) :=
      ⟨by omega, runSet_no_cut Zf r hmem hmem1 (by omega)⟩
    have hlink := link_of_turn_gen (vzData C Zf hZ) vbot hbase
    by_cases hse : C.sp (eAdd a j) = 1
    · by_cases hsf : C.sp (eAdd a (j + 1)) = 1
      · refine ⟨Sum.inl (spineB C (eAdd a j)), ?_,
          Sum.inl (spineB C (eAdd a (j + 1))), ?_, ?_⟩
        · rw [vFam_lo_spine C a b j hj1 hse]; exact Finset.mem_singleton_self _
        · rw [vFam_lo_spine C a b (j + 1) hj2 hsf]; exact Finset.mem_singleton_self _
        · have h := hlink (Sum.inl (spineT C (eAdd a j)))
          rw [vbot_spineT, vzData_t,
            vz_spine_pass C Zf _ _ hse hsf hpass (by omega)] at h
          exact h
      · refine ⟨Sum.inl (spineB C (eAdd a j)), ?_, Sum.inr false, ?_, ?_⟩
        · rw [vFam_lo_spine C a b j hj1 hse]; exact Finset.mem_singleton_self _
        · rw [vFam_lo_virt C a b (j + 1) hj2 hsf]; exact Finset.mem_singleton_self _
        · have h := hlink (Sum.inl (spineT C (eAdd a j)))
          rw [vbot_spineT, vzData_t,
            vz_spine_virt C Zf _ (eAdd a (j + 1)) hse (by have := C.sp_le (eAdd a (j+1)); omega)
              hpass (by omega)] at h
          exact h
    · by_cases hsf : C.sp (eAdd a (j + 1)) = 1
      · -- the virtual strand rejoins the spine line at `hi`
        have h0 := C.sp_zero_mem (show C.sp (eAdd a j) = 0 by have := C.sp_le (eAdd a j); omega)
        have h1 := C.sp_one_not_mem hsf
        have hfhi : (eAdd a (j + 1)).val = C.hi := by omega
        have hn : C.hi ≠ n := by have := (eAdd a (j+1)).isLt; omega
        refine ⟨Sum.inr false, ?_, Sum.inl (spineB C (eAdd a (j + 1))), ?_, ?_⟩
        · rw [vFam_lo_virt C a b j hj1 hse]; exact Finset.mem_singleton_self _
        · rw [vFam_lo_spine C a b (j + 1) hj2 hsf]; exact Finset.mem_singleton_self _
        · have h := hlink (Sum.inr (!C.bl))
          rw [vbot_inr, vzData_t, vz_virt_spine C Zf hn _ hfhi] at h
          exact h
      · refine ⟨Sum.inr false, ?_, Sum.inr false, ?_, SimpleGraph.Reachable.refl _⟩
        · rw [vFam_lo_virt C a b j hj1 hse]; exact Finset.mem_singleton_self _
        · rw [vFam_lo_virt C a b (j + 1) hj2 hsf]; exact Finset.mem_singleton_self _
  · rcases Nat.eq_or_lt_of_le hjd with hje | hjd2
    · -- the bounce at the top of the run
      have hj1 : j ≤ b.val - a.val := by omega
      have hvab : (eAdd a j).val = b.val := by rw [eAdd_val a j (by omega)]; omega
      have heb : eAdd a j = b := Fin.ext hvab
      have hnp : ¬ PassHi Zf b := runSet_max_no_passHi Zf r hb hmax
      have hlink := link_of_turn_gen (vzData C Zf hZ) vbot hbase
      have hqmem : vbot (Sum.inl (fC C b 0)) ∈ vFam C a b (j + 1) := by
        rw [show j + 1 = b.val - a.val + 1 + 0 from by omega, vFam_hi' C a b 0 (by omega),
          show eSub b 0 = b from Fin.ext (by simp only [eSub_val]; omega)]
        exact fC_zero_mem C b
      by_cases hse : C.sp b = 1
      · refine ⟨Sum.inl (spineB C b), ?_, vbot (Sum.inl (fC C b 0)), hqmem, ?_⟩
        · rw [vFam_lo_spine C a b j hj1 (by rw [heb]; exact hse), heb]
          exact Finset.mem_singleton_self _
        · have h := hlink (Sum.inl (spineT C b))
          rw [vbot_spineT, vzData_t, vz_spine_bounce C Zf b hse hnp] at h
          exact h
      · have hl := edge_eq_last C Zf hZ (by have := C.sp_le b; omega) hnp
        refine ⟨Sum.inr false, ?_, vbot (Sum.inl (fC C b 0)), hqmem, ?_⟩
        · rw [vFam_lo_virt C a b j hj1 (by rw [heb]; exact hse)]
          exact Finset.mem_singleton_self _
        · have h := hlink (Sum.inr (!C.bl))
          rw [vbot_inr, vzData_t, vz_virt_bounce C Zf hl.2 b (by omega)] at h
          exact h
    · -- a chain pass, going back down the run
      obtain ⟨k, rfl⟩ : ∃ k, j = b.val - a.val + 1 + k := ⟨j - (b.val - a.val) - 1, by omega⟩
      have hkd : k + 1 ≤ b.val - a.val := by omega
      have hmemk : eSub b k ∈ runSet Zf r := eSub_mem_runSet Zf r ha hb k (by omega) hab
      have hmemk1 : eSub b (k + 1) ∈ runSet Zf r := eSub_mem_runSet Zf r ha hb (k + 1) hkd hab
      have hpass : PassLo Zf (eSub b k) := by
        refine ⟨by simp only [eSub_val]; omega, ?_⟩
        have hnc := runSet_no_cut Zf r hmemk1 hmemk (by simp only [eSub_val]; omega)
        rwa [show (((eSub b (k + 1)).val : ℤ) + 1) = ((eSub b k).val : ℤ) from by
          simp only [eSub_val]; omega] at hnc
      have hlink := link_of_turn_gen (vzData C Zf hZ) vbot hbase
      refine ⟨vbot (Sum.inl (chainB C (eSub b k))), ?_,
        vbot (Sum.inl (fC C (eSub b (k + 1)) 0)), ?_, ?_⟩
      · rw [vFam_hi' C a b k (by omega)]; exact chainB_mem C _
      · rw [show b.val - a.val + 1 + k + 1 = b.val - a.val + 1 + (k + 1) from by omega,
          vFam_hi' C a b (k + 1) hkd]
        exact fC_zero_mem C _
      · have h := hlink (Sum.inl (chainB C (eSub b k)))
        rw [vzData_t, vz_chain_pass C Zf (eSub b k) (eSub b (k + 1)) hpass
          (by simp only [eSub_val]; omega)] at h
        exact h

/-! ## The run's joined set covers the run -/

theorem vz_cover (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (r : ℕ) (a b : Fin n)
    (hb : b ∈ runSet Zf r)
    (hmin : ∀ e : Fin n, e ∈ runSet Zf r → a.val ≤ e.val)
    (hmax : ∀ e : Fin n, e ∈ runSet Zf r → e.val ≤ b.val)
    (v : VEndpt n m)
    (hv : CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) v) = r) :
    vbot v ∈ (Finset.range (2 * (b.val - a.val) + 1 + 1)).biUnion (vFam C a b) := by
  have hab : a.val ≤ b.val := hmin b hb
  rw [Finset.mem_biUnion]
  cases v with
  | inl x =>
    have hxe : x.edge ∈ runSet Zf r := mem_runSet.mpr (by
      have : VEndpt.edgeOf ((C.lo : ℤ) - 1) (Sum.inl x : VEndpt n m)
          = ((x.edge.val : ℕ) : ℤ) := rfl
      rw [this] at hv; exact hv)
    have h1 := hmin _ hxe
    have h2 := hmax _ hxe
    have hbn := b.isLt
    by_cases h0 : x.idx.val = 0 ∧ C.sp x.edge = 1
    · refine ⟨x.edge.val - a.val, Finset.mem_range.mpr (by omega), ?_⟩
      have hEq : eAdd a (x.edge.val - a.val) = x.edge :=
        Fin.ext (by rw [eAdd_val a _ (by omega)]; omega)
      rw [vFam_lo_spine C a b _ (by omega) (by rw [hEq]; exact h0.2), hEq,
        Finset.mem_singleton, vbot_inl]
      refine congrArg Sum.inl (endpt_ext rfl ?_ rfl)
      simp only [botOf_idx_val, spineB_idx]
      exact h0.1
    · have hsp : C.sp x.edge ≤ x.idx.val := by have := C.sp_le x.edge; omega
      refine ⟨b.val - a.val + 1 + (b.val - x.edge.val), Finset.mem_range.mpr (by omega), ?_⟩
      rw [vFam_hi' C a b (b.val - x.edge.val) (by omega),
        show eSub b (b.val - x.edge.val) = x.edge from Fin.ext (by
          simp only [eSub_val]; omega)]
      exact vbot_mem_vChain C x hsp
  | inr bb =>
    have hlo : CutComponents.gz Zf ((C.lo : ℤ)) = r := by
      rw [CutComponents.gz_step_eq Zf (lo_not_cut C Zf hZ)]
      exact hv
    have hmemlo : eLoE C ∈ runSet Zf r := mem_runSet.mpr hlo
    have h1 := hmin _ hmemlo
    have h2 := hmax _ hmemlo
    simp only [eLoE_val] at h1 h2
    have hbn := b.isLt
    refine ⟨C.lo - a.val, Finset.mem_range.mpr (by omega), ?_⟩
    have hEq : eAdd a (C.lo - a.val) = eLoE C :=
      Fin.ext (by rw [eAdd_val a _ (by omega)]; simp only [eLoE_val]; omega)
    rw [vFam_lo_virt C a b _ (by omega) (by rw [hEq, sp_eLoE]; omega), vbot_inr,
      Finset.mem_singleton]

/-- **Every run is one joined set.**  The analogue of `EltBridge.RunStrandsConnected`
on the extended type. -/
theorem vz_runs_connected (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (r : ℕ) :
    ∃ S : Finset (VEndpt n m), AllJoined (WalkGraph.graph (vzData C Zf hZ)) S ∧
      ∀ v : VEndpt n m,
        CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) v) = r → vbot v ∈ S := by
  by_cases hne : (runSet Zf r : Finset (Fin n)).Nonempty
  · have ha : (runSet Zf r).min' hne ∈ runSet Zf r := Finset.min'_mem _ _
    have hb : (runSet Zf r).max' hne ∈ runSet Zf r := Finset.max'_mem _ _
    have hmin : ∀ e : Fin n, e ∈ runSet Zf r → ((runSet Zf r).min' hne).val ≤ e.val :=
      fun e he => Fin.le_def.mp (Finset.min'_le _ _ he)
    have hmax : ∀ e : Fin n, e ∈ runSet Zf r → e.val ≤ ((runSet Zf r).max' hne).val :=
      fun e he => Fin.le_def.mp (Finset.le_max' _ _ he)
    exact ⟨_, vz_run_joined C Zf hZ r _ _ ha hb hmin hmax,
      fun v hv => vz_cover C Zf hZ r _ _ hb hmin hmax v hv⟩
  · refine ⟨∅, allJoined_empty _, ?_⟩
    intro v hv
    exfalso
    cases v with
    | inl x =>
      refine hne ⟨x.edge, mem_runSet.mpr ?_⟩
      have : VEndpt.edgeOf ((C.lo : ℤ) - 1) (Sum.inl x : VEndpt n m)
          = ((x.edge.val : ℕ) : ℤ) := rfl
      rw [this] at hv; exact hv
    | inr bb =>
      refine hne ⟨eLoE C, mem_runSet.mpr ?_⟩
      simp only [eLoE_val]
      rw [CutComponents.gz_step_eq Zf (lo_not_cut C Zf hZ)]
      exact hv

/-! ## Assembly: the shield law at odd-span widths -/

/-- **`hsep`: two points of the same run share a walk.** -/
theorem vz_hsep (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) :
    ∀ x y : VEndpt n m,
      runIndexG (VEndpt.edgeOf ((C.lo : ℤ) - 1)) Zf x
        = runIndexG (VEndpt.edgeOf ((C.lo : ℤ) - 1)) Zf y →
      (WalkGraph.graph (vzData C Zf hZ)).Reachable x y := by
  classical
  choose S hS hmem using vz_runs_connected C Zf hZ
  have hbase : ∀ x : VEndpt n m, vbot x = x ∨ vbot x = (vzData C Zf hZ).p x :=
    fun x => by rw [vzData_p]; exact vbot_eq_or_partner x
  have hidx : ∀ x : VEndpt n m,
      CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) (vbot x))
        = CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) x) := by
    intro x; rw [vbot_edgeOf]
  have hrun := hrun_of_allJoined_gen (WalkGraph.graph (vzData C Zf hZ)) vbot
    (fun v => CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) v)) S hS
    (fun v => hmem _ v rfl)
  have hfin := hsep_of_base_connected (vzData C Zf hZ) vbot
    (fun v => CutComponents.gz Zf (VEndpt.edgeOf ((C.lo : ℤ) - 1) v)) hbase hidx hrun
  intro x y hxy
  exact hfin x y (congrArg Fin.val hxy)

/-- **`hvirt`: the virtual pair stays inside one run.** -/
theorem vz_hvirt (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) : ∀ bb : Bool,
    CutComponents.blk (VEndpt.edgeOf ((C.lo : ℤ) - 1)) Zf (Sum.inr bb : VEndpt n m)
      = CutComponents.blk (VEndpt.edgeOf ((C.lo : ℤ) - 1)) Zf
          ((vzData C Zf hZ).t (Sum.inr bb : VEndpt n m)) := by
  have hlh := C.hlh
  have hhn := C.hhn
  have hnp := C.n_pos
  have hwin : ∀ z ∈ Zf, ¬ ((C.lo : ℤ) - 1 < z ∧ z ≤ (C.hi : ℤ)) := by
    rintro z hz ⟨h1, h2⟩
    exact hZ z hz ⟨by omega, h2⟩
  have hconst := gz_const_on Zf ((C.lo : ℤ) - 1) ((C.hi : ℤ)) hwin
  intro bb
  rw [vzData_t, vzTurn_inr]
  by_cases hbb : bb = C.bl
  · subst hbb
    by_cases h0 : C.lo = 0
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_zero (m := m) C h0
      rw [hy]
      show CutComponents.gz Zf ((C.lo : ℤ) - 1)
        = CutComponents.gz Zf ((y.edge.val : ℕ) : ℤ)
      exact hconst _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_lo_pos (m := m) C h0
      rw [hy]
      show CutComponents.gz Zf ((C.lo : ℤ) - 1)
        = CutComponents.gz Zf ((y.edge.val : ℕ) : ℤ)
      exact hconst _ _ (by omega) (by omega) (by omega) (by omega)
  · have hb2 : bb = !C.bl := by cases bb <;> cases hbl : C.bl <;> simp_all
    subst hb2
    by_cases hn : C.hi = n
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_top (m := m) C hn
      rw [hy]
      show CutComponents.gz Zf ((C.lo : ℤ) - 1)
        = CutComponents.gz Zf ((y.edge.val : ℕ) : ℤ)
      exact hconst _ _ (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨y, hy, hye, hyi, hyt⟩ := vzV_hi_mid (m := m) C hn
      rw [hy]
      show CutComponents.gz Zf ((C.lo : ℤ) - 1)
        = CutComponents.gz Zf ((y.edge.val : ℕ) : ℤ)
      exact hconst _ _ (by omega) (by omega) (by omega) (by omega)

/-- **`hruns`: every run carries a point.** -/
theorem vz_hruns (C : VZ n m) (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, EndType.edgeOf x = t) :
    ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n m, CutComponents.blk (VEndpt.edgeOf ((C.lo : ℤ) - 1)) Zf v = i := by
  intro i hi
  obtain ⟨t, ht1, ht2, ht3⟩ := CutComponents.exists_pos_with_gz Zf A B hAB hlow hhigh i hi
  obtain ⟨x, hx⟩ := hoc t ht1 ht2
  refine ⟨Sum.inl x, ?_⟩
  show CutComponents.gz Zf (EndType.edgeOf x) = i
  rw [hx]; exact ht3

/-- **THE SHIELD LAW AT ODD-SPAN WIDTHS.**  `walkCount = |Zf| + 1`, that is `c = |Z|`,
on the extended end type `VEndpt`, for widths that are ODD exactly on the travel span
`[lo, hi)` and even off it -- the parity a real configuration forces
(`TravelParity.mu_odd_iff_mem`).  Compare `EltBridge.zz_shield_law`, which needs every
width even, and `EltBridge.shield_law`, which needs them all equal. -/
theorem vz_shield_law (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, EndType.edgeOf x = t) :
    WalkGraph.walkCount (vzData C Zf hZ) = Zf.card + 1 :=
  VEndpt.shield (vs0 C) (vs1 C) ((C.lo : ℤ) - 1) Zf (vzData C Zf hZ) rfl
    (fun e => vz_site C Zf hZ e)
    (fun u v huv hne => vz_hturn C Zf hZ u v huv hne)
    (vz_hvirt C Zf hZ)
    (vz_hruns C Zf A B hAB hlow hhigh hoc)
    (vz_hsep C Zf hZ)
    (Sum.inr false)

/-- The existential form. -/
theorem vz_shield_law_exists (C : VZ n m) (Zf : Finset ℤ) (hZ : NoCut C Zf) (A B : ℤ)
    (hAB : A ≤ B) (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, EndType.edgeOf x = t) :
    ∃ E : WalkGraph.Data (VEndpt n m), WalkGraph.walkCount E = Zf.card + 1 :=
  ⟨vzData C Zf hZ, vz_shield_law C Zf hZ A B hAB hlow hhigh hoc⟩

/-! ## Non-vacuity

Four edges of widths `2, 3, 4, 2`: odd exactly on the span `[1, 2)`, even off it, and
not constant there either.  One cut site, at `3`.  Neither `EltBridge.shield_law` (equal
widths) nor `EltBridge.zz_shield_law` (all widths even) can even state this. -/

/-- Widths `2, 3, 4, 2`. -/
def w3 : Fin 4 → ℕ := fun e => if e.val = 1 then 3 else if e.val = 2 then 4 else 2

/-- The span is the single edge `1`. -/
def C3 : VZ 4 w3 where
  lo := 1
  hi := 2
  bl := false
  hlh := by norm_num
  hhn := by norm_num
  hodd := by
    intro e h1 h2
    have he : e.val = 1 := by omega
    simp [w3, he]
  heven := by
    intro e h
    have hlt := e.isLt
    have he : e.val ≠ 1 := by omega
    simp only [w3, if_neg he]
    split_ifs <;> norm_num

theorem C3_noCut : NoCut C3 ({(3 : ℤ)} : Finset ℤ) := by
  intro z hz
  rw [Finset.mem_singleton] at hz
  subst hz
  rintro ⟨h1, h2⟩
  norm_num [C3] at h2

/-- **The whole chain, on a configuration neither earlier shield law can state.** -/
theorem vz_witness_shield :
    WalkGraph.walkCount (vzData C3 ({(3 : ℤ)} : Finset ℤ) C3_noCut) = 2 := by
  have h := vz_shield_law C3 ({(3 : ℤ)} : Finset ℤ) C3_noCut 0 3 (by norm_num)
    (by intro z hz; rw [Finset.mem_singleton] at hz; omega)
    (by intro z hz; rw [Finset.mem_singleton] at hz; omega)
    (by
      intro t h0 h1
      have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
      rcases ht with rfl | rfl | rfl | rfl
      · exact ⟨⟨⟨0, by norm_num⟩, ⟨0, by norm_num [w3]⟩, true⟩, by
          simp [EndType.edgeOf]⟩
      · exact ⟨⟨⟨1, by norm_num⟩, ⟨0, by norm_num [w3]⟩, true⟩, by
          simp [EndType.edgeOf]⟩
      · exact ⟨⟨⟨2, by norm_num⟩, ⟨0, by norm_num [w3]⟩, true⟩, by
          simp [EndType.edgeOf]⟩
      · exact ⟨⟨⟨3, by norm_num⟩, ⟨0, by norm_num [w3]⟩, true⟩, by
          simp [EndType.edgeOf]⟩)
  simpa using h

/-! ## The configuration of a real group element

`SiteCost.PathData.mu_par` forces `mu j` to be ODD exactly on the travel interval
(`TravelParity.mu_odd_iff_mem`) and even off it, and `mu_pos` makes the even ones at
least `2`.  So the widths `pdMm P` of a real configuration ARE an odd-span family, with
the span the shifted travel interval -- which is what this file's `VZ` asks for and what
`EltBridge.zz_shield_law` (all widths even) cannot accommodate. -/

section PathDataInstance

open SiteCost

theorem pdWidth_cast (P : SiteCost.PathData) : (pdWidth P : ℤ) = P.B - P.A + 1 := by
  have := P.hA; have := P.hB; unfold pdWidth; omega

/-- For positive travel the span reaches at most one past `B`. -/
theorem kstar_le_B (P : SiteCost.PathData) (hk : 0 < P.kstar) : P.kstar ≤ P.B + 1 := by
  by_contra hc
  have h := (P.houter (P.kstar - 1) (Or.inr (by omega))).2
  unfold travel at h
  rw [if_pos (by omega)] at h
  omega

/-- For negative travel the span starts at or after `A`. -/
theorem A_le_kstar (P : SiteCost.PathData) (hk : P.kstar < 0) : P.A ≤ P.kstar := by
  by_contra hc
  have h := (P.houter P.kstar (Or.inl (by omega))).2
  unfold travel at h
  rw [if_neg (by omega), if_pos (by omega)] at h
  omega

theorem pd_edge_range (P : SiteCost.PathData) (e : Fin (pdWidth P)) :
    P.A ≤ P.A + ((e : ℕ) : ℤ) ∧ P.A + ((e : ℕ) : ℤ) ≤ P.B := by
  have hw := pdWidth_cast P
  have he : ((e : ℕ) : ℤ) < (pdWidth P : ℤ) := by exact_mod_cast e.isLt
  have he0 : (0 : ℤ) ≤ ((e : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- **On the travel span the width is odd.** -/
theorem pdMm_odd_of_travel (P : SiteCost.PathData) (e : Fin (pdWidth P))
    (h : (0 ≤ P.A + ((e : ℕ) : ℤ) ∧ P.A + ((e : ℕ) : ℤ) < P.kstar)
      ∨ (P.kstar ≤ P.A + ((e : ℕ) : ℤ) ∧ P.A + ((e : ℕ) : ℤ) < 0)) :
    pdMm P e % 2 = 1 := by
  simp only [pdMm]
  rw [P.mm_eq_mu (pd_edge_range P e)]
  exact (TravelParity.mu_odd_iff_mem P _).mpr h

/-- **Off it the width is even and at least two.** -/
theorem pdMm_even_of_no_travel (P : SiteCost.PathData) (e : Fin (pdWidth P))
    (h : ¬ ((0 ≤ P.A + ((e : ℕ) : ℤ) ∧ P.A + ((e : ℕ) : ℤ) < P.kstar)
      ∨ (P.kstar ≤ P.A + ((e : ℕ) : ℤ) ∧ P.A + ((e : ℕ) : ℤ) < 0))) :
    2 ≤ pdMm P e ∧ pdMm P e % 2 = 0 := by
  simp only [pdMm]
  rw [P.mm_eq_mu (pd_edge_range P e)]
  have h1 := (TravelParity.mu_even_iff_not_mem P _).mpr h
  have h2 := P.mu_pos (P.A + ((e : ℕ) : ℤ))
  omega

/-- **The odd-span configuration of a `PathData` with positive travel.** -/
noncomputable def pdVZpos (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    VZ (pdWidth P) (pdMm P) where
  lo := (-P.A).toNat
  hi := (P.kstar - P.A).toNat
  bl := false
  hlh := by have := P.hA; omega
  hhn := by
    have := P.hA; have := P.hB; have := kstar_le_B P hk; have := pdWidth_cast P; omega
  hodd := by
    intro e h1 h2
    have he0 : (0 : ℤ) ≤ ((e : ℕ) : ℤ) := Int.natCast_nonneg _
    have hc1 : ((((-P.A).toNat : ℕ)) : ℤ) ≤ ((e : ℕ) : ℤ) := by exact_mod_cast h1
    have hc2 : ((e : ℕ) : ℤ) < ((((P.kstar - P.A).toNat : ℕ)) : ℤ) := by exact_mod_cast h2
    have := P.hA
    exact pdMm_odd_of_travel P e (Or.inl ⟨by omega, by omega⟩)
  heven := by
    intro e h
    refine pdMm_even_of_no_travel P e ?_
    have he0 : (0 : ℤ) ≤ ((e : ℕ) : ℤ) := Int.natCast_nonneg _
    have hcn : ((e : ℕ) : ℤ) = ((e : ℕ) : ℤ) := rfl
    have hA := P.hA
    have hlo : ((((-P.A).toNat : ℕ)) : ℤ) = -P.A := by omega
    have hhi : ((((P.kstar - P.A).toNat : ℕ)) : ℤ) = P.kstar - P.A := by omega
    have h' : ¬ (((((-P.A).toNat : ℕ)) : ℤ) ≤ ((e : ℕ) : ℤ)
        ∧ ((e : ℕ) : ℤ) < ((((P.kstar - P.A).toNat : ℕ)) : ℤ)) := by
      rintro ⟨g1, g2⟩
      exact h ⟨by exact_mod_cast g1, by exact_mod_cast g2⟩
    rw [hlo, hhi] at h'
    omega

@[simp] theorem pdVZpos_lo (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    (pdVZpos P hk).lo = (-P.A).toNat := rfl
@[simp] theorem pdVZpos_hi (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    (pdVZpos P hk).hi = (P.kstar - P.A).toNat := rfl

/-- **The gap condition for the positive-travel configuration.**  Its interior is free
(`EltBridge.no_cut_inside_travel`); the two endpoints are the two virtual sites, and
`EltBridge.cut_at_zero` shows those genuinely can be cut, so they are hypotheses --
exactly as in `EltBridge.pd_hgap`. -/
theorem pdVZpos_noCut (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    NoCut (pdVZpos P hk) (pdCutSites P) := by
  rintro z hz ⟨h1, h2⟩
  have hA := P.hA
  have hlo : (((pdVZpos P hk).lo : ℕ) : ℤ) = -P.A := by simp only [pdVZpos_lo]; omega
  have hhi : (((pdVZpos P hk).hi : ℕ) : ℤ) = P.kstar - P.A := by
    simp only [pdVZpos_hi]; omega
  rw [hlo] at h1
  rw [hhi] at h2
  have hcut : P.cut (P.A + z) := ((mem_pdCutSites P z).mp hz).2
  rcases lt_trichotomy (P.A + z) 0 with h | h | h
  · omega
  · exact hne0 (by rw [show (-P.A) = z from by omega]; exact hz)
  · rcases lt_trichotomy (P.A + z) P.kstar with hh | hh | hh
    · exact no_cut_inside_travel P (P.A + z) h hh hcut
    · exact hne1 (by rw [show (P.kstar - P.A) = z from by omega]; exact hz)
    · omega

/-- Every edge of the span carries an end. -/
theorem pd_hoc (P : SiteCost.PathData) :
    ∀ t : ℤ, 0 ≤ t → t ≤ (pdWidth P : ℤ) - 1 →
      ∃ x : Endpt (pdWidth P) (pdMm P), EndType.edgeOf x = t := by
  intro t h0 h1
  have hw := pdWidth_cast P
  have hlt : t.toNat < pdWidth P := by omega
  refine ⟨⟨⟨t.toNat, hlt⟩, ⟨0, ?_⟩, true⟩, ?_⟩
  · exact pdMm_pos P ⟨t.toNat, hlt⟩ (by show P.A ≤ P.A + ((t.toNat : ℕ) : ℤ); omega)
      (by show P.A + ((t.toNat : ℕ) : ℤ) ≤ P.B; omega)
  · show (((t.toNat : ℕ)) : ℤ) = t
    omega

/-- **THE SHIELD LAW FOR A REAL CONFIGURATION** (positive travel): the walk count of the
explicitly constructed datum on `VEndpt` is exactly `|Z| + 1`.  The only hypotheses
beyond `0 < kstar` are that neither virtual site is a cut site -- the same two
exclusions `EltBridge.pd_hgap` needs, and which `EltBridge.cut_at_zero_iff` shows are
genuine conditions on the element, not free. -/
theorem pd_shield_law_pos (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    WalkGraph.walkCount
        (vzData (pdVZpos P hk) (pdCutSites P) (pdVZpos_noCut P hk hne0 hne1))
      = (pdCutSites P).card + 1 := by
  have hwp := pdWidth_pos P
  refine vz_shield_law (pdVZpos P hk) (pdCutSites P) (pdVZpos_noCut P hk hne0 hne1)
    0 ((pdWidth P : ℤ) - 1) (by omega) ?_ ?_ (pd_hoc P)
  · intro z hz; exact (pdCutSites_interior P hz).1
  · intro z hz; have := (pdCutSites_interior P hz).2; omega

/-- The existential form: a real configuration's walk graph has exactly `|Z| + 1`
components. -/
theorem pd_shield_exists_pos (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    ∃ E : WalkGraph.Data (VEndpt (pdWidth P) (pdMm P)),
      WalkGraph.walkCount E = (pdCutSites P).card + 1 :=
  ⟨_, pd_shield_law_pos P hk hne0 hne1⟩

end PathDataInstance

/-! ### The mirror, for negative travel

For `kstar < 0` the travel interval is `[kstar, 0)`, so the span sits below the origin
and the two virtual tags swap sides: `Sum.inr false` (the virtual arrival, at site
`-A`) is now the HIGH one, which is what `bl = true` records. -/

section PathDataInstanceNeg

open SiteCost

/-- **The odd-span configuration of a `PathData` with negative travel.** -/
noncomputable def pdVZneg (P : SiteCost.PathData) (hk : P.kstar < 0) :
    VZ (pdWidth P) (pdMm P) where
  lo := (P.kstar - P.A).toNat
  hi := (-P.A).toNat
  bl := true
  hlh := by have := A_le_kstar P hk; omega
  hhn := by have := P.hA; have := P.hB; have := pdWidth_cast P; omega
  hodd := by
    intro e h1 h2
    have hak := A_le_kstar P hk
    have hc1 : ((((P.kstar - P.A).toNat : ℕ)) : ℤ) ≤ ((e : ℕ) : ℤ) := by exact_mod_cast h1
    have hc2 : ((e : ℕ) : ℤ) < ((((-P.A).toNat : ℕ)) : ℤ) := by exact_mod_cast h2
    have := P.hA
    exact pdMm_odd_of_travel P e (Or.inr ⟨by omega, by omega⟩)
  heven := by
    intro e h
    refine pdMm_even_of_no_travel P e ?_
    have he0 : (0 : ℤ) ≤ ((e : ℕ) : ℤ) := Int.natCast_nonneg _
    have hA := P.hA
    have hak := A_le_kstar P hk
    have hlo : ((((P.kstar - P.A).toNat : ℕ)) : ℤ) = P.kstar - P.A := by omega
    have hhi : ((((-P.A).toNat : ℕ)) : ℤ) = -P.A := by omega
    have h' : ¬ (((((P.kstar - P.A).toNat : ℕ)) : ℤ) ≤ ((e : ℕ) : ℤ)
        ∧ ((e : ℕ) : ℤ) < ((((-P.A).toNat : ℕ)) : ℤ)) := by
      rintro ⟨g1, g2⟩
      exact h ⟨by exact_mod_cast g1, by exact_mod_cast g2⟩
    rw [hlo, hhi] at h'
    omega

@[simp] theorem pdVZneg_lo (P : SiteCost.PathData) (hk : P.kstar < 0) :
    (pdVZneg P hk).lo = (P.kstar - P.A).toNat := rfl
@[simp] theorem pdVZneg_hi (P : SiteCost.PathData) (hk : P.kstar < 0) :
    (pdVZneg P hk).hi = (-P.A).toNat := rfl

theorem pdVZneg_noCut (P : SiteCost.PathData) (hk : P.kstar < 0)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    NoCut (pdVZneg P hk) (pdCutSites P) := by
  rintro z hz ⟨h1, h2⟩
  have hA := P.hA
  have hak := A_le_kstar P hk
  have hlo : (((pdVZneg P hk).lo : ℕ) : ℤ) = P.kstar - P.A := by
    simp only [pdVZneg_lo]; omega
  have hhi : (((pdVZneg P hk).hi : ℕ) : ℤ) = -P.A := by simp only [pdVZneg_hi]; omega
  rw [hlo] at h1
  rw [hhi] at h2
  have hcut : P.cut (P.A + z) := ((mem_pdCutSites P z).mp hz).2
  rcases lt_trichotomy (P.A + z) P.kstar with h | h | h
  · omega
  · exact hne1 (by rw [show (P.kstar - P.A) = z from by omega]; exact hz)
  · rcases lt_trichotomy (P.A + z) 0 with hh | hh | hh
    · exact no_cut_in_neg_travel P (P.A + z) h hh hcut
    · exact hne0 (by rw [show (-P.A) = z from by omega]; exact hz)
    · omega

/-- **THE SHIELD LAW FOR A REAL CONFIGURATION** (negative travel). -/
theorem pd_shield_law_neg (P : SiteCost.PathData) (hk : P.kstar < 0)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    WalkGraph.walkCount
        (vzData (pdVZneg P hk) (pdCutSites P) (pdVZneg_noCut P hk hne0 hne1))
      = (pdCutSites P).card + 1 := by
  have hwp := pdWidth_pos P
  refine vz_shield_law (pdVZneg P hk) (pdCutSites P) (pdVZneg_noCut P hk hne0 hne1)
    0 ((pdWidth P : ℤ) - 1) (by omega) ?_ ?_ (pd_hoc P)
  · intro z hz; exact (pdCutSites_interior P hz).1
  · intro z hz; have := (pdCutSites_interior P hz).2; omega

/-- **Both signs at once**, in existential form.  `kstar = 0` is excluded and must be:
there the two virtual points sit at the same site, `VEndpt.partner` no longer changes
site, and no `WalkGraph.Data` of this shape exists. -/
theorem pd_shield_exists (P : SiteCost.PathData) (hk : P.kstar ≠ 0)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    ∃ E : WalkGraph.Data (VEndpt (pdWidth P) (pdMm P)),
      WalkGraph.walkCount E = (pdCutSites P).card + 1 := by
  rcases lt_trichotomy P.kstar 0 with h | h | h
  · exact ⟨_, pd_shield_law_neg P h hne0 hne1⟩
  · exact absurd h hk
  · exact ⟨_, pd_shield_law_pos P h hne0 hne1⟩

/-- **And for a group element.**  `Elt.toPathData` is the bridge named in BLOCK 330;
the cut count is the element's `|Z|` in absolute coordinates by
`EltBridge.pdCutSites_card_eq_abs`. -/
theorem Elt_shield_exists (g : Elt) (hk : g.toPathData.kstar ≠ 0)
    (hne0 : (-g.toPathData.A) ∉ pdCutSites g.toPathData)
    (hne1 : (g.toPathData.kstar - g.toPathData.A) ∉ pdCutSites g.toPathData) :
    ∃ E : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
      WalkGraph.walkCount E
        = ((Finset.Ioo g.toPathData.A (g.toPathData.B + 1)).filter
            g.toPathData.cut).card + 1 := by
  obtain ⟨E, hE⟩ := pd_shield_exists g.toPathData hk hne0 hne1
  exact ⟨E, by rw [hE, pdCutSites_card_eq_abs]⟩

end PathDataInstanceNeg

/-! ### Non-vacuity at the `Elt` level

`EltBridge.witNeg` is a genuine group element with `kstar = -1`, span `[-1, 2]`, ONE cut
site, and neither virtual site cut -- so every hypothesis above holds of it and the
whole chain runs.  Its widths are odd on the shifted span `[0, 1)` and even off it, so
neither `EltBridge.shield_law` nor `EltBridge.zz_shield_law` can state this. -/

theorem witNeg_kstar_neg : witNeg.toPathData.kstar < 0 := by rw [witNeg_pd_kstar]; norm_num

theorem witNeg_hne0 : (-witNeg.toPathData.A) ∉ pdCutSites witNeg.toPathData := by
  rw [witNeg_cutSites, witNeg_pd_A, Finset.mem_singleton]
  norm_num

theorem witNeg_hne1 :
    (witNeg.toPathData.kstar - witNeg.toPathData.A) ∉ pdCutSites witNeg.toPathData := by
  rw [witNeg_cutSites, witNeg_pd_A, witNeg_pd_kstar, Finset.mem_singleton]
  norm_num

/-- **The whole chain, on a real group element with a non-empty cut set.** -/
theorem witNeg_shield :
    WalkGraph.walkCount
        (vzData (pdVZneg witNeg.toPathData witNeg_kstar_neg) (pdCutSites witNeg.toPathData)
          (pdVZneg_noCut witNeg.toPathData witNeg_kstar_neg witNeg_hne0 witNeg_hne1))
      = 2 := by
  rw [pd_shield_law_neg witNeg.toPathData witNeg_kstar_neg witNeg_hne0 witNeg_hne1,
    witNeg_cutSites]
  simp


/-! ## The defect identification, the two virtual sites, and `kstar = 0`

BLOCK 341 built the datum and computed its walk count.  Three things were left open and
are settled here.

1. **The walk count IS the element's defect.**  `ConfigLoop.defect D = walkCount D - 1`
   and `EltBridge.Elt.c g = (pdCutSites g.toPathData).card`, so the shield law says
   exactly `defect = c` on the constructed datum.  Stated as a named theorem rather than
   left for the reader to assemble.  The identification is made on the NAMED datum
   `vzData`/`zzData`, not on the existential `pd_shield_exists`: an existential over an
   unconstrained `WalkGraph.Data` is weak (any fixed-point-free involution pair is one),
   so the content lives in the construction.

2. **The two hypotheses `hne0`, `hne1` are characterised exactly.**
   `mem_pdCutSites_zero` and `mem_pdCutSites_kstar` reduce them to `P.cut 0` and
   `P.cut P.kstar` plus interiority, and the read-offs then say:

   | | site `0` | site `kstar` |
   |---|---|---|
   | `kstar > 0` | never cut (`Phi = 1`) | cut iff `!delta`, `d(k-1) = -eps`, `d(k) = 0` |
   | `kstar = 0` | cut iff `!delta`, `d(-1) = 1 - eps`, `d(0) = 0` | (same site) |
   | `kstar < 0` | cut iff `d(-1) = 1`, `d(0) = 0` | cut iff `delta`, `d(k-1) = 0`, `d(k) = eps` |

   (`kstar < 0` is `EltBridge.cut_at_zero_iff` / `cut_at_kstar_iff`; the other two rows
   are `not_cut_at_zero_pos`, `cut_at_kstar_iff_pos`, `cut_at_zero_iff_zero` here.)
   So `hne0` is FREE for `kstar > 0`, `hne1` is FREE for `kstar > 0 & delta` and for
   `kstar < 0 & !delta`, and the remaining two cases are genuine: `witCut0` and `witCutK`
   below are group elements where the respective hypothesis FAILS and `NoCut` is FALSE,
   so this route's construction does not apply to them.

3. **`kstar = 0` needs no hypotheses at all.**  `travel 0 = 0`, so `mu j` is even and at
   least `2` at every edge: the widths of a zero-travel element satisfy
   `EltBridge.EvenWidths`, there are no virtual points, and `EltBridge.zz_shield_law`
   (BLOCK 339) applies with NO exclusions.  This removes BLOCK 341's `kstar /= 0`
   exclusion entirely.

Every read-off above was checked first in Rust
(`code/zeta_probe/tools/nogap/src/bin/pdcut_check.rs`: 33 372 legal `(kstar, eps, delta, d)`
with `kstar` in `[-3,3]` and `d : [-3,3] -> [-2,2]`, 0 failures), together with the widths
and cut sets of the three new witnesses and a 680-configuration sweep of the even-width
turn. -/

section DefectAndZero

open SiteCost

/-! ### The two virtual sites, as membership conditions

`pdCutSites` filters the shifted window `Ioo 0 (pdWidth P)`, so a virtual site is a cut
site only if it is INTERIOR.  These two lemmas strip the interiority off and leave the
bare `P.cut` condition, which the read-offs then evaluate. -/

/-- **Site `0` is a cut site of the shifted window iff `A < 0` and `P.cut 0`.**  The upper
interiority bound is automatic, since `-A < pdWidth = B - A + 1` reduces to `0 ≤ B`. -/
theorem mem_pdCutSites_zero (P : SiteCost.PathData) :
    (-P.A) ∈ pdCutSites P ↔ (P.A < 0 ∧ P.cut 0) := by
  rw [mem_pdCutSites]
  have hw := pdWidth_cast P
  have hA := P.hA
  have hB := P.hB
  constructor
  · rintro ⟨⟨h1, h2⟩, hcut⟩
    refine ⟨by omega, ?_⟩
    unfold pdCutAt at hcut
    rwa [show P.A + -P.A = (0 : ℤ) by ring] at hcut
  · rintro ⟨h1, hcut⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    unfold pdCutAt
    rwa [show P.A + -P.A = (0 : ℤ) by ring]

/-- **Site `kstar` is a cut site of the shifted window iff `A < kstar ≤ B` and
`P.cut P.kstar`.** -/
theorem mem_pdCutSites_kstar (P : SiteCost.PathData) :
    (P.kstar - P.A) ∈ pdCutSites P ↔ (P.A < P.kstar ∧ P.kstar ≤ P.B ∧ P.cut P.kstar) := by
  rw [mem_pdCutSites]
  have hw := pdWidth_cast P
  constructor
  · rintro ⟨⟨h1, h2⟩, hcut⟩
    refine ⟨by omega, by omega, ?_⟩
    unfold pdCutAt at hcut
    rwa [show P.A + (P.kstar - P.A) = P.kstar by ring] at hcut
  · rintro ⟨h1, h2, hcut⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    unfold pdCutAt
    rwa [show P.A + (P.kstar - P.A) = P.kstar by ring]

/-! ### The read-offs for `kstar ≥ 0`

`EltBridge.cut_at_zero_iff` and `EltBridge.cut_at_kstar_iff` do the `kstar < 0` half.
These are the missing rows, and they are not the mirror image: for positive travel the
travel indicator sits on `[0, kstar)`, so it is site `0` whose `Phi` is forced non-zero
and site `kstar` that can be cut -- the exact opposite of `kstar < 0`. -/

/-- **For positive travel site `0` is NEVER cut.**  `f(-1) = 0` there, so
`Phi(0) = 0 + 1 - 0 = 1`.  (For `kstar < 0` the same computation gives `-1 + 1 - 0 = 0`,
which is why `cut_at_zero_iff` has content.) -/
theorem not_cut_at_zero_pos (P : SiteCost.PathData) (hk : 0 < P.kstar) : ¬ P.cut 0 := by
  rintro ⟨-, -, hc⟩
  have hvD : P.vD 0 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (by omega)]
  have hf : P.f (0 - 1) = 0 := by
    unfold SiteCost.PathData.f travel
    rw [if_neg (by omega), if_neg (by omega)]
  have hvL : P.vL 0 = 0 := by
    unfold SiteCost.PathData.vL; rw [hvD]; split_ifs <;> rfl
  unfold SiteCost.PathData.PhiAt SiteCost.vArr at hc
  rw [hf, hvL, if_pos rfl] at hc
  norm_num at hc

/-- **For positive travel site `kstar` is cut exactly when `delta` is CLEAR and the two
read-offs hold.**  `f(kstar - 1) = 1` there, so `Phi = 1 - vL(kstar)` vanishes only when
the virtual departure is on the LEFT -- the mirror of `cut_at_kstar_iff`. -/
theorem cut_at_kstar_iff_pos (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    P.cut P.kstar ↔
      (P.delta = false ∧ P.d (P.kstar - 1) = -P.eps ∧ P.d P.kstar = 0) := by
  have hvA : SiteCost.vArr P.kstar = 0 := by
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  have hvD : P.vD P.kstar = 1 := by
    unfold SiteCost.PathData.vD; rw [if_pos rfl]
  have hf : P.f (P.kstar - 1) = 1 := by
    unfold SiteCost.PathData.f travel
    rw [if_pos (by omega)]
  constructor
  · rintro ⟨ha, hb, hc⟩
    unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL at hc
    rw [hvA, hvD, hf] at hc
    have hd : P.delta = false := by
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      rw [hcon] at hc; norm_num at hc
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL at ha
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR at hb
    rw [hvA, hvD, hd] at ha
    rw [hvD, hd] at hb
    norm_num at ha hb
    exact ⟨hd, by omega, by omega⟩
  · rintro ⟨hd, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL
      rw [hvA, hvD, hd]
      norm_num
      omega
    · unfold SiteCost.PathData.betaAt SiteCost.PathData.vR
      rw [hvD, hd]
      norm_num
      exact h2
    · unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL
      rw [hvA, hvD, hd, hf]
      norm_num

/-- **For zero travel the two virtual sites coincide at `0`**, and it is cut exactly when
`delta` is clear and the two read-offs hold.  `f(-1) = 0` and the virtual departure sits
at `0` too, so `Phi(0) = 0 + 1 - vL(0)`. -/
theorem cut_at_zero_iff_zero (P : SiteCost.PathData) (hk : P.kstar = 0) :
    P.cut 0 ↔ (P.delta = false ∧ P.d (-1) = 1 - P.eps ∧ P.d 0 = 0) := by
  have hvA : SiteCost.vArr (0 : ℤ) = 1 := by
    unfold SiteCost.vArr; rw [if_pos rfl]
  have hvD : P.vD 0 = 1 := by
    unfold SiteCost.PathData.vD; rw [if_pos (by omega)]
  have hf : P.f (0 - 1) = 0 := by
    unfold SiteCost.PathData.f
    rw [hk, travel_of_kstar_zero]
  constructor
  · rintro ⟨ha, hb, hc⟩
    unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL at hc
    rw [hvA, hvD, hf] at hc
    have hd : P.delta = false := by
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      rw [hcon] at hc; norm_num at hc
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL at ha
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR at hb
    rw [hvA, hvD, hd] at ha
    rw [hvD, hd] at hb
    norm_num at ha hb
    exact ⟨hd, by omega, by omega⟩
  · rintro ⟨hd, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL
      rw [hvA, hvD, hd]
      norm_num
      omega
    · unfold SiteCost.PathData.betaAt SiteCost.PathData.vR
      rw [hvD, hd]
      norm_num
      exact h2
    · unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL
      rw [hvA, hvD, hd, hf]
      norm_num

/-! ### Discharging the hypotheses where they are free -/

/-- **`hne0` is automatic for positive travel.** -/
theorem pd_hne0_of_pos (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    (-P.A) ∉ pdCutSites P := by
  rw [mem_pdCutSites_zero]
  rintro ⟨-, hc⟩
  exact not_cut_at_zero_pos P hk hc

/-- **`hne1` is automatic for positive travel with `delta` set.** -/
theorem pd_hne1_of_pos_delta (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hd : P.delta = true) : (P.kstar - P.A) ∉ pdCutSites P := by
  rw [mem_pdCutSites_kstar]
  rintro ⟨-, -, hc⟩
  rw [cut_at_kstar_iff_pos P hk, hd] at hc
  exact absurd hc.1 (by simp)

/-- **`hne1` is automatic for negative travel with `delta` clear.** -/
theorem pd_hne1_of_neg_not_delta (P : SiteCost.PathData) (hk : P.kstar < 0)
    (hd : P.delta = false) : (P.kstar - P.A) ∉ pdCutSites P := by
  rw [mem_pdCutSites_kstar]
  rintro ⟨-, -, hc⟩
  rw [cut_at_kstar_iff P hk, hd] at hc
  exact absurd hc.1 (by simp)

/-- **`hne0` for negative travel, as an explicit read-off.**  Not free: this is a genuine
condition on the deposits, and `witCut0` below violates it. -/
theorem pd_hne0_neg_iff (P : SiteCost.PathData) (hk : P.kstar < 0) :
    (-P.A) ∈ pdCutSites P ↔ (P.A < 0 ∧ P.d (-1) = 1 ∧ P.d 0 = 0) := by
  rw [mem_pdCutSites_zero, cut_at_zero_iff P hk]

/-- **`hne1` for positive travel, as an explicit read-off.**  Not free either;
`witCutK` below violates it. -/
theorem pd_hne1_pos_iff (P : SiteCost.PathData) (hk : 0 < P.kstar) :
    (P.kstar - P.A) ∈ pdCutSites P ↔
      (P.A < P.kstar ∧ P.kstar ≤ P.B ∧ P.delta = false ∧
        P.d (P.kstar - 1) = -P.eps ∧ P.d P.kstar = 0) := by
  rw [mem_pdCutSites_kstar, cut_at_kstar_iff_pos P hk]

/-! ### `kstar = 0`: the excluded case, closed with no hypotheses

`travel 0 j = 0` for every `j`, so `mu j = 2` wherever `d j = 0` and `|d j|` otherwise --
and `hpar` makes every `d j` even.  So all widths are even and at least `2`, there are no
odd-width edges and hence no virtual points, and BLOCK 339's `EltBridge.zz_shield_law`
applies verbatim.  It carries NO exclusion hypotheses, so the `kstar = 0` case of the
shield law is unconditional. -/

/-- **A zero-travel element has all widths even.** -/
theorem pdMm_evenWidths_of_kstar_zero (P : SiteCost.PathData) (hk : P.kstar = 0) :
    EvenWidths (pdMm P) := by
  intro e
  refine pdMm_even_of_no_travel P e ?_
  rw [hk]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

/-- **THE SHIELD LAW FOR A REAL CONFIGURATION** (zero travel).  No `hne0`, no `hne1`:
the two virtual points do not exist in this case, so nothing has to avoid them. -/
theorem pd_shield_law_zero (P : SiteCost.PathData) (hk : P.kstar = 0) :
    WalkGraph.walkCount (zzData (pdCutSites P) (pdMm_evenWidths_of_kstar_zero P hk))
      = (pdCutSites P).card + 1 := by
  have hwp := pdWidth_pos P
  refine zz_shield_law (pdCutSites P) (pdMm_evenWidths_of_kstar_zero P hk)
    0 ((pdWidth P : ℤ) - 1) (by omega) ?_ ?_ (pd_hoc P) ?_
  · intro z hz; exact (pdCutSites_interior P hz).1
  · intro z hz; have := (pdCutSites_interior P hz).2; omega
  · obtain ⟨x, -⟩ := pd_hoc P 0 le_rfl (by omega)
    exact ⟨x⟩

/-! ### The defect identification

`ConfigLoop.defect D = walkCount D - 1` by definition, so each shield law above is a
statement about the defect of an explicitly named datum.  `EltBridge.Elt.c g` is
`(pdCutSites g.toPathData).card`, so at the level of a group element these read
`c = defect`. -/

/-- **`defect = |Z|` for positive travel**, on the constructed datum. -/
theorem pd_defect_pos (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    ConfigLoop.defect (vzData (pdVZpos P hk) (pdCutSites P) (pdVZpos_noCut P hk hne0 hne1))
      = (pdCutSites P).card := by
  unfold ConfigLoop.defect
  rw [pd_shield_law_pos P hk hne0 hne1]
  omega

/-- **`defect = |Z|` for negative travel**, on the constructed datum. -/
theorem pd_defect_neg (P : SiteCost.PathData) (hk : P.kstar < 0)
    (hne0 : (-P.A) ∉ pdCutSites P) (hne1 : (P.kstar - P.A) ∉ pdCutSites P) :
    ConfigLoop.defect (vzData (pdVZneg P hk) (pdCutSites P) (pdVZneg_noCut P hk hne0 hne1))
      = (pdCutSites P).card := by
  unfold ConfigLoop.defect
  rw [pd_shield_law_neg P hk hne0 hne1]
  omega

/-- **`defect = |Z|` for zero travel**, on the constructed datum, with no hypotheses. -/
theorem pd_defect_zero (P : SiteCost.PathData) (hk : P.kstar = 0) :
    ConfigLoop.defect (zzData (pdCutSites P) (pdMm_evenWidths_of_kstar_zero P hk))
      = (pdCutSites P).card := by
  unfold ConfigLoop.defect
  rw [pd_shield_law_zero P hk]
  omega

/-! ### At the level of a group element -/

/-- **`Elt.c g = defect` for positive travel.**  This is the identification BLOCK 341
explicitly did not claim. -/
theorem Elt_c_eq_defect_pos (g : Elt) (hk : 0 < g.toPathData.kstar)
    (hne0 : (-g.toPathData.A) ∉ pdCutSites g.toPathData)
    (hne1 : (g.toPathData.kstar - g.toPathData.A) ∉ pdCutSites g.toPathData) :
    Elt.c g = ConfigLoop.defect
      (vzData (pdVZpos g.toPathData hk) (pdCutSites g.toPathData)
        (pdVZpos_noCut g.toPathData hk hne0 hne1)) :=
  (pd_defect_pos g.toPathData hk hne0 hne1).symm

/-- **`Elt.c g = defect` for negative travel.** -/
theorem Elt_c_eq_defect_neg (g : Elt) (hk : g.toPathData.kstar < 0)
    (hne0 : (-g.toPathData.A) ∉ pdCutSites g.toPathData)
    (hne1 : (g.toPathData.kstar - g.toPathData.A) ∉ pdCutSites g.toPathData) :
    Elt.c g = ConfigLoop.defect
      (vzData (pdVZneg g.toPathData hk) (pdCutSites g.toPathData)
        (pdVZneg_noCut g.toPathData hk hne0 hne1)) :=
  (pd_defect_neg g.toPathData hk hne0 hne1).symm

/-- **`Elt.c g = defect` for zero travel**, with NO hypotheses at all. -/
theorem Elt_c_eq_defect_zero (g : Elt) (hk : g.toPathData.kstar = 0) :
    Elt.c g = ConfigLoop.defect
      (zzData (pdCutSites g.toPathData) (pdMm_evenWidths_of_kstar_zero g.toPathData hk)) :=
  (pd_defect_zero g.toPathData hk).symm

/-! ### The hypothesis-free classes -/

/-- **Positive travel with `delta` set: the shield law with no side conditions.** -/
theorem pd_shield_law_pos_delta (P : SiteCost.PathData) (hk : 0 < P.kstar)
    (hd : P.delta = true) :
    WalkGraph.walkCount (vzData (pdVZpos P hk) (pdCutSites P)
        (pdVZpos_noCut P hk (pd_hne0_of_pos P hk) (pd_hne1_of_pos_delta P hk hd)))
      = (pdCutSites P).card + 1 :=
  pd_shield_law_pos P hk (pd_hne0_of_pos P hk) (pd_hne1_of_pos_delta P hk hd)

/-- **Negative travel with `delta` clear: only `hne0` survives.** -/
theorem pd_shield_law_neg_not_delta (P : SiteCost.PathData) (hk : P.kstar < 0)
    (hd : P.delta = false) (hne0 : (-P.A) ∉ pdCutSites P) :
    WalkGraph.walkCount (vzData (pdVZneg P hk) (pdCutSites P)
        (pdVZneg_noCut P hk hne0 (pd_hne1_of_neg_not_delta P hk hd)))
      = (pdCutSites P).card + 1 :=
  pd_shield_law_neg P hk hne0 (pd_hne1_of_neg_not_delta P hk hd)

/-! ### One theorem for ALL elements

The two cases live on different end types -- `kstar = 0` needs no virtual points and its
datum is a `Data (Endpt ...)`, while `kstar /= 0` needs both and its datum is a
`Data (VEndpt ...)`.  There is no single type to state them over: pushing the `kstar = 0`
datum into `VEndpt` would add the virtual pair as its OWN component (`VEndpt.partner` and
any turn both swap the two virtual tags, which at `kstar = 0` sit at the same site),
giving `defect = |Z| + 1`, not `|Z|`.  So the honest single statement is the disjunction,
with the hypotheses stated conditionally on `kstar /= 0` -- which is what makes the
`kstar = 0` branch unconditional. -/

/-- **The defect identification for EVERY group element.**  For `kstar = 0` the
hypotheses are vacuous, so this covers all zero-travel elements outright. -/
theorem Elt_defect_eq_c (g : Elt)
    (hne0 : g.toPathData.kstar ≠ 0 → (-g.toPathData.A) ∉ pdCutSites g.toPathData)
    (hne1 : g.toPathData.kstar ≠ 0 →
      (g.toPathData.kstar - g.toPathData.A) ∉ pdCutSites g.toPathData) :
    (∃ E : WalkGraph.Data (Endpt (pdWidth g.toPathData) (pdMm g.toPathData)),
        ConfigLoop.defect E = Elt.c g)
      ∨ (∃ E : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
        ConfigLoop.defect E = Elt.c g) := by
  rcases lt_trichotomy g.toPathData.kstar 0 with h | h | h
  · exact Or.inr ⟨_, (Elt_c_eq_defect_neg g h (hne0 (by omega)) (hne1 (by omega))).symm⟩
  · exact Or.inl ⟨_, (Elt_c_eq_defect_zero g h).symm⟩
  · exact Or.inr ⟨_, (Elt_c_eq_defect_pos g h (hne0 (by omega)) (hne1 (by omega))).symm⟩

/-- **The hypothesis-free class.**  `kstar = 0`, or `kstar > 0` with `delta` set: no side
condition on the element whatsoever. -/
theorem Elt_defect_eq_c_free (g : Elt) (hk : 0 ≤ g.toPathData.kstar)
    (hd : g.toPathData.kstar = 0 ∨ g.toPathData.delta = true) :
    (∃ E : WalkGraph.Data (Endpt (pdWidth g.toPathData) (pdMm g.toPathData)),
        ConfigLoop.defect E = Elt.c g)
      ∨ (∃ E : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
        ConfigLoop.defect E = Elt.c g) := by
  rcases eq_or_lt_of_le hk with h | h
  · exact Or.inl ⟨_, (Elt_c_eq_defect_zero g h.symm).symm⟩
  · have hdd : g.toPathData.delta = true := by
      rcases hd with h0 | h0
      · omega
      · exact h0
    exact Or.inr ⟨_, (Elt_c_eq_defect_pos g h (pd_hne0_of_pos _ h)
      (pd_hne1_of_pos_delta _ h hdd)).symm⟩

end DefectAndZero

/-! ## Non-vacuity, and the sharpness of `hne0` / `hne1`

Three new witnesses, all genuine `Elt`s, all computed in Rust first.

* `witZero` -- `kstar = 0`, deposits `2` at edges `-1` and `2`.  Span `[-1, 2]`, widths
  `(2,2,2,2)`, one interior cut site.  Exercises the whole `kstar = 0` route, which
  BLOCK 341 could not state at all.
* `witCut0` -- `kstar = -1`, deposit `1` at edge `-1`.  Span `[-1, 0]`, widths `(1,2)`,
  and its ONE cut site is `-A`: `hne0` FAILS and `NoCut` is FALSE.
* `witCutK` -- `kstar = 1`, deposits `-1` at edge `0` and `2` at edge `2`.  Span `[0, 2]`,
  widths `(1,2,2)`, and its ONE cut site is `kstar - A`: `hne1` FAILS and `NoCut` is
  FALSE. -/

section Sharpness

open SiteCost

/-! ### `witZero`: the `kstar = 0` route is non-vacuous -/

/-- A zero-travel element with a genuine interior cut site. -/
noncomputable def witZero : Elt where
  kstar := 0
  eps := 1
  delta := true
  heps := Or.inl rfl
  d := fun j => if j = -1 then 2 else if j = 2 then 2 else 0
  hpar := by
    intro j
    rw [travel_of_kstar_zero]
    by_cases h1 : j = -1
    · subst h1; norm_num
    · by_cases h2 : j = 2
      · subst h2; simp [h1]
      · simp [h1, h2]
  supp := {-1, 2}
  hsupp := by
    intro j hj
    have h1 : j ≠ -1 := by intro hc; exact hj (by simp [hc])
    have h2 : j ≠ 2 := by intro hc; exact hj (by simp [hc])
    exact ⟨by simp [h1, h2], travel_of_kstar_zero j⟩

@[simp] theorem witZero_pd_kstar : witZero.toPathData.kstar = 0 := rfl
@[simp] theorem witZero_pd_delta : witZero.toPathData.delta = true := rfl

theorem witZero_pd_d (j : ℤ) :
    witZero.toPathData.d j = if j = -1 then 2 else if j = 2 then 2 else 0 := rfl

theorem witZero_pd_f (j : ℤ) : witZero.toPathData.f j = 0 := by
  unfold SiteCost.PathData.f
  rw [witZero_pd_kstar, travel_of_kstar_zero]

theorem witZero_occ : witZero.occ = {-1, 0, 2} := by
  classical
  unfold Elt.occ
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · simp [h]
    · have : x = -1 ∨ x = 2 := by simpa [witZero] using h
      rcases this with h | h <;> simp [h]
  · rintro (h | h | h) <;> subst h
    · exact Or.inr ⟨by simp [witZero], Or.inl (by simp [witZero])⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by simp [witZero], Or.inl (by simp [witZero])⟩

theorem witZero_A : witZero.A = -1 := by
  have hm : witZero.A ∈ witZero.occ := Finset.min'_mem _ _
  have hle : witZero.A ≤ -1 := Finset.min'_le _ _ (by rw [witZero_occ]; simp)
  rw [witZero_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem witZero_B : witZero.B = 2 := by
  have hm : witZero.B ∈ witZero.occ := Finset.max'_mem _ _
  have hle : (2 : ℤ) ≤ witZero.B := Finset.le_max' _ _ (by rw [witZero_occ]; simp)
  rw [witZero_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

@[simp] theorem witZero_pd_A : witZero.toPathData.A = -1 := witZero_A
@[simp] theorem witZero_pd_B : witZero.toPathData.B = 2 := witZero_B

theorem witZero_width : pdWidth witZero.toPathData = 4 := by
  unfold pdWidth
  rw [witZero_pd_A, witZero_pd_B]
  rfl

/-- **The cut set of `witZero` is a single site.**  Of the three interior shifted sites
`1, 2, 3` (absolute `0, 1, 2`): the first is the virtual site and `delta` is SET there so
it is not cut, the second is cut, the third carries the deposit `2`. -/
theorem witZero_cutSites : pdCutSites witZero.toPathData = {2} := by
  classical
  ext z
  rw [mem_pdCutSites, Finset.mem_singleton, witZero_width]
  constructor
  · rintro ⟨⟨h1, h2⟩, hcut⟩
    interval_cases z
    · exfalso
      unfold pdCutAt at hcut
      rw [witZero_pd_A, show (-1 : ℤ) + 1 = 0 by ring,
        cut_at_zero_iff_zero _ witZero_pd_kstar, witZero_pd_delta] at hcut
      exact absurd hcut.1 (by simp)
    · rfl
    · exfalso
      rw [pdCutAt_iff witZero.toPathData 3 (by rw [witZero_pd_A]; norm_num)
        (by rw [witZero_pd_A, witZero_pd_kstar]; norm_num)] at hcut
      obtain ⟨-, hdd, -⟩ := hcut
      rw [witZero_pd_A, show (-1 : ℤ) + 3 = 2 by ring, witZero_pd_d] at hdd
      norm_num at hdd
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rw [pdCutAt_iff witZero.toPathData 2 (by rw [witZero_pd_A]; norm_num)
      (by rw [witZero_pd_A, witZero_pd_kstar]; norm_num)]
    rw [witZero_pd_A, show (-1 : ℤ) + 2 = 1 by ring]
    refine ⟨?_, ?_, witZero_pd_f _⟩
    · rw [show (1 : ℤ) - 1 = 0 by ring, witZero_pd_d]; norm_num
    · rw [witZero_pd_d]; norm_num

/-- **The whole `kstar = 0` chain, on a real group element with a non-empty cut set.**
`walkCount = 2`, i.e. `defect = c = 1`, and NO hypotheses were needed. -/
theorem witZero_shield :
    WalkGraph.walkCount (zzData (pdCutSites witZero.toPathData)
        (pdMm_evenWidths_of_kstar_zero witZero.toPathData witZero_pd_kstar))
      = 2 := by
  rw [pd_shield_law_zero witZero.toPathData witZero_pd_kstar, witZero_cutSites]
  simp

/-- **And as a defect identity**: `c = 1` is realised by an explicit datum. -/
theorem witZero_defect :
    Elt.c witZero = ConfigLoop.defect (zzData (pdCutSites witZero.toPathData)
        (pdMm_evenWidths_of_kstar_zero witZero.toPathData witZero_pd_kstar)) :=
  Elt_c_eq_defect_zero witZero witZero_pd_kstar

theorem witZero_c : Elt.c witZero = 1 := by
  unfold Elt.c
  rw [witZero_cutSites]
  simp

/-! ### `witCut0`: `hne0` cannot be dropped -/

/-- A negative-travel element whose virtual arrival site IS a cut site. -/
noncomputable def witCut0 : Elt where
  kstar := -1
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun j => if j = -1 then 1 else 0
  hpar := by
    intro j
    unfold travel
    by_cases h1 : j = -1
    · subst h1; norm_num
    · simp only [h1, if_false]
      split_ifs <;> omega
  supp := {-1}
  hsupp := by
    intro j hj
    have h1 : j ≠ -1 := by intro hc; exact hj (by simp [hc])
    refine ⟨by simp [h1], ?_⟩
    unfold travel
    split_ifs <;> omega

@[simp] theorem witCut0_pd_kstar : witCut0.toPathData.kstar = -1 := rfl

theorem witCut0_pd_d (j : ℤ) :
    witCut0.toPathData.d j = if j = -1 then 1 else 0 := rfl

theorem witCut0_kstar_neg : witCut0.toPathData.kstar < 0 := by
  rw [witCut0_pd_kstar]; norm_num

theorem witCut0_occ : witCut0.occ = {-1, 0} := by
  classical
  unfold Elt.occ
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · simp [h]
    · have : x = -1 := by simpa [witCut0] using h
      simp [this]
  · rintro (h | h) <;> subst h
    · exact Or.inr ⟨by simp [witCut0], Or.inl (by simp [witCut0])⟩
    · exact Or.inl rfl

theorem witCut0_A : witCut0.A = -1 := by
  have hm : witCut0.A ∈ witCut0.occ := Finset.min'_mem _ _
  have hle : witCut0.A ≤ -1 := Finset.min'_le _ _ (by rw [witCut0_occ]; simp)
  rw [witCut0_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem witCut0_B : witCut0.B = 0 := by
  have hm : witCut0.B ∈ witCut0.occ := Finset.max'_mem _ _
  have hle : (0 : ℤ) ≤ witCut0.B := Finset.le_max' _ _ (by rw [witCut0_occ]; simp)
  rw [witCut0_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

@[simp] theorem witCut0_pd_A : witCut0.toPathData.A = -1 := witCut0_A
@[simp] theorem witCut0_pd_B : witCut0.toPathData.B = 0 := witCut0_B

/-- **`hne0` FAILS for `witCut0`.**  Its virtual arrival site `-A = 1` is a cut site:
`d(-1) = 1` and `d(0) = 0`, exactly `cut_at_zero_iff`'s condition. -/
theorem witCut0_hne0_fails :
    (-witCut0.toPathData.A) ∈ pdCutSites witCut0.toPathData := by
  rw [pd_hne0_neg_iff _ witCut0_kstar_neg]
  refine ⟨by rw [witCut0_pd_A]; norm_num, ?_, ?_⟩
  · rw [witCut0_pd_d]; norm_num
  · rw [witCut0_pd_d]; norm_num

/-- **So `NoCut` is FALSE for it**, and `pd_shield_law_neg`'s construction does not apply:
there is no `vzData` to build.

What this does NOT show is that the EXISTENTIAL `pd_shield_exists` fails for `witCut0`.
That existential quantifies over an arbitrary `WalkGraph.Data`, with no constraint beyond
its two involutions, so it is satisfiable for almost any configuration and refuting it is
a different question.  The content of the shield law is in the NAMED datum, and it is the
named datum that `hne0` is needed for.  That is the sharp form of "this hypothesis cannot
be removed" available here. -/
theorem witCut0_noCut :
    ¬ NoCut (pdVZneg witCut0.toPathData witCut0_kstar_neg)
        (pdCutSites witCut0.toPathData) := by
  intro h
  refine h (-witCut0.toPathData.A) witCut0_hne0_fails ⟨?_, ?_⟩
  · simp only [pdVZneg_lo, witCut0_pd_A, witCut0_pd_kstar]
    norm_num
  · simp only [pdVZneg_hi, witCut0_pd_A]
    norm_num

/-! ### `witCutK`: `hne1` cannot be dropped either -/

/-- A positive-travel element whose virtual departure site IS a cut site. -/
noncomputable def witCutK : Elt where
  kstar := 1
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun j => if j = 0 then -1 else if j = 2 then 2 else 0
  hpar := by
    intro j
    unfold travel
    by_cases h1 : j = 0
    · subst h1; norm_num
    · by_cases h2 : j = 2
      · subst h2
        simp only [h1, if_false, if_true]
        split_ifs <;> omega
      · simp only [h1, h2, if_false]
        split_ifs <;> omega
  supp := {0, 2}
  hsupp := by
    intro j hj
    have h1 : j ≠ 0 := by intro hc; exact hj (by simp [hc])
    have h2 : j ≠ 2 := by intro hc; exact hj (by simp [hc])
    refine ⟨by simp [h1, h2], ?_⟩
    unfold travel
    split_ifs <;> omega

@[simp] theorem witCutK_pd_kstar : witCutK.toPathData.kstar = 1 := rfl
@[simp] theorem witCutK_pd_eps : witCutK.toPathData.eps = 1 := rfl
@[simp] theorem witCutK_pd_delta : witCutK.toPathData.delta = false := rfl

theorem witCutK_pd_d (j : ℤ) :
    witCutK.toPathData.d j = if j = 0 then -1 else if j = 2 then 2 else 0 := rfl

theorem witCutK_kstar_pos : 0 < witCutK.toPathData.kstar := by
  rw [witCutK_pd_kstar]; norm_num

theorem witCutK_occ : witCutK.occ = {0, 2} := by
  classical
  unfold Elt.occ
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · simp [h]
    · have : x = 0 ∨ x = 2 := by simpa [witCutK] using h
      rcases this with h | h <;> simp [h]
  · rintro (h | h) <;> subst h
    · exact Or.inl rfl
    · exact Or.inr ⟨by simp [witCutK], Or.inl (by simp [witCutK])⟩

theorem witCutK_A : witCutK.A = 0 := by
  have hm : witCutK.A ∈ witCutK.occ := Finset.min'_mem _ _
  have hle : witCutK.A ≤ 0 := Finset.min'_le _ _ (by rw [witCutK_occ]; simp)
  rw [witCutK_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem witCutK_B : witCutK.B = 2 := by
  have hm : witCutK.B ∈ witCutK.occ := Finset.max'_mem _ _
  have hle : (2 : ℤ) ≤ witCutK.B := Finset.le_max' _ _ (by rw [witCutK_occ]; simp)
  rw [witCutK_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

@[simp] theorem witCutK_pd_A : witCutK.toPathData.A = 0 := witCutK_A
@[simp] theorem witCutK_pd_B : witCutK.toPathData.B = 2 := witCutK_B

/-- **`hne1` FAILS for `witCutK`.**  Its virtual departure site `kstar - A = 1` is a cut
site: `delta` is clear, `d(0) = -1 = -eps` and `d(1) = 0`, exactly
`cut_at_kstar_iff_pos`'s condition. -/
theorem witCutK_hne1_fails :
    (witCutK.toPathData.kstar - witCutK.toPathData.A) ∈ pdCutSites witCutK.toPathData := by
  rw [pd_hne1_pos_iff _ witCutK_kstar_pos]
  refine ⟨by rw [witCutK_pd_A, witCutK_pd_kstar]; norm_num,
    by rw [witCutK_pd_B, witCutK_pd_kstar]; norm_num, witCutK_pd_delta, ?_, ?_⟩
  · rw [witCutK_pd_kstar, witCutK_pd_eps, show (1 : ℤ) - 1 = 0 by ring, witCutK_pd_d]
    norm_num
  · rw [witCutK_pd_kstar, witCutK_pd_d]
    norm_num

/-- **So `NoCut` is FALSE for it too.**  Same caveat as `witCut0_noCut`: what fails is
the construction, not the existential. -/
theorem witCutK_noCut :
    ¬ NoCut (pdVZpos witCutK.toPathData witCutK_kstar_pos)
        (pdCutSites witCutK.toPathData) := by
  intro h
  refine h (witCutK.toPathData.kstar - witCutK.toPathData.A) witCutK_hne1_fails ⟨?_, ?_⟩
  · simp only [pdVZpos_lo, witCutK_pd_A, witCutK_pd_kstar]
    norm_num
  · simp only [pdVZpos_hi, witCutK_pd_A, witCutK_pd_kstar]
    norm_num

/-! ### Item 4: how this relates to `ConfigLoop.c_le_Z_final` / `shield_law_runs`

`ConfigLoop.shield_law_runs` proves `walkCount = |Z| + 1` on `Endpt n m` from `RunInv`
(a cost-minimality-flavoured invariant), `hruns` (every run carries an end) and

    hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf

-- "cut sites carry no arrivals".  `ConfigLoop.shield_final_hyps_incompatible` already
records that `hZ` is incompatible with balance plus an occupancy hypothesis.  The point
here is that a REAL configuration always supplies both: `pd_hoc` says every edge of the
span carries an end (`pdMm_pos`: `mu ≥ 1` everywhere on the span), and balance at a cut
site is automatic because a cut site has zero travel on both adjacent edges.  So `hZ` is
FALSE for every real configuration with a cut site away from the two virtual sites, and
outright false for every zero-travel configuration with any cut site at all.

That settles the comparison honestly: for this application the two routes are not
alternatives.  `shield_law_runs` cannot be instantiated at a real configuration with a
non-empty `Z`, because its `hZ` fails there; the zigzag route asks instead for `hturn`
(the turn BOUNCES at a cut site rather than there being no end there), which is
satisfiable and is what the explicit construction supplies.  The zigzag route therefore
supersedes it here rather than duplicating it.  What the zigzag route does NOT give, and
`shield_law_runs` does, is any relation to cost-minimality: `vzData`/`zzData` are not
claimed to be `MergesMin`. -/

/-- **A real configuration is balanced at a cut site away from the two virtual sites.**
A cut site has `f = 0` on its left edge (`pdCutAt_iff`), and `travel` is constant away
from `0` and `kstar`, so both adjacent edges carry the same signed travel. -/
theorem pd_balanced_at_cut (P : SiteCost.PathData) (z : ℤ) (hz : z ∈ pdCutSites P)
    (h0 : P.A + z ≠ 0) (hkz : P.A + z ≠ P.kstar) (e1 e2 : Fin (pdWidth P))
    (h1 : ((e1 : ℕ) : ℤ) = z - 1) (h2 : ((e2 : ℕ) : ℤ) = z) :
    (EndType.arrAt (m := pdMm P) (pdUp P) z).card
      = (EndType.depAt (m := pdMm P) (pdUp P) z).card := by
  refine (ConfigLoop.balance_iff_tr (m := pdMm P) (pdUp P) z e1 e2 h1 h2).mpr ?_
  rw [pd_tr_eq, pd_tr_eq, h1, h2]
  unfold travelS
  rw [show P.A + (z - 1) = P.A + z - 1 by ring]
  exact travel_const_off P.kstar (P.A + z) h0 hkz

/-- **A zero-travel configuration is balanced everywhere**, with no side condition. -/
theorem pd_balanced_of_kstar_zero (P : SiteCost.PathData) (hk : P.kstar = 0) (s : ℤ)
    (e1 e2 : Fin (pdWidth P)) (h1 : ((e1 : ℕ) : ℤ) = s - 1) (h2 : ((e2 : ℕ) : ℤ) = s) :
    (EndType.arrAt (m := pdMm P) (pdUp P) s).card
      = (EndType.depAt (m := pdMm P) (pdUp P) s).card := by
  refine (ConfigLoop.balance_iff_tr (m := pdMm P) (pdUp P) s e1 e2 h1 h2).mpr ?_
  rw [pd_tr_eq, pd_tr_eq]
  unfold travelS
  rw [hk, travel_of_kstar_zero, travel_of_kstar_zero]

/-- **`ConfigLoop`'s `hZ` is FALSE at a real cut site away from the virtual sites.** -/
theorem hZ_false_at_cut (P : SiteCost.PathData) (z : ℤ) (hz : z ∈ pdCutSites P)
    (h0 : P.A + z ≠ 0) (hkz : P.A + z ≠ P.kstar) :
    ¬ (∀ x : Endpt (pdWidth P) (pdMm P),
        EndType.isArrOf (pdUp P) x = true → EndType.siteOf x ∉ pdCutSites P) := by
  intro hZ
  obtain ⟨hlo, hhi⟩ := pdCutSites_interior P hz
  have hw := pdWidth_cast P
  have he1 : (z - 1).toNat < pdWidth P := by omega
  have he2 : z.toNat < pdWidth P := by omega
  have hc1 : (((⟨(z - 1).toNat, he1⟩ : Fin (pdWidth P)) : ℕ) : ℤ) = z - 1 := by
    show (((z - 1).toNat : ℕ) : ℤ) = z - 1; omega
  have hc2 : (((⟨z.toNat, he2⟩ : Fin (pdWidth P)) : ℕ) : ℤ) = z := by
    show ((z.toNat : ℕ) : ℤ) = z; omega
  have hbal := pd_balanced_at_cut P z hz h0 hkz ⟨(z - 1).toNat, he1⟩ ⟨z.toNat, he2⟩ hc1 hc2
  have hzero := ConfigLoop.empty_edges_at_arrivalfree (m := pdMm P) (pdUp P) z hbal
    (fun y hy hs => hZ y hy (hs ▸ hz)) ⟨z.toNat, he2⟩ (Or.inl hc2)
  have hpos := pdMm_pos P ⟨z.toNat, he2⟩
    (by show P.A ≤ P.A + ((z.toNat : ℕ) : ℤ); omega)
    (by show P.A + ((z.toNat : ℕ) : ℤ) ≤ P.B; omega)
  omega

/-- **And for zero travel it is false as soon as there is any cut site at all.**  So the
`RunInv` route of `ConfigLoop.shield_law_runs` cannot reach the very case the zigzag
route closes unconditionally. -/
theorem hZ_false_of_kstar_zero (P : SiteCost.PathData) (hk : P.kstar = 0)
    (hne : (pdCutSites P).Nonempty) :
    ¬ (∀ x : Endpt (pdWidth P) (pdMm P),
        EndType.isArrOf (pdUp P) x = true → EndType.siteOf x ∉ pdCutSites P) := by
  intro hZ
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hlo, hhi⟩ := pdCutSites_interior P hz
  have hw := pdWidth_cast P
  have he1 : (z - 1).toNat < pdWidth P := by omega
  have he2 : z.toNat < pdWidth P := by omega
  have hc1 : (((⟨(z - 1).toNat, he1⟩ : Fin (pdWidth P)) : ℕ) : ℤ) = z - 1 := by
    show (((z - 1).toNat : ℕ) : ℤ) = z - 1; omega
  have hc2 : (((⟨z.toNat, he2⟩ : Fin (pdWidth P)) : ℕ) : ℤ) = z := by
    show ((z.toNat : ℕ) : ℤ) = z; omega
  have hbal := pd_balanced_of_kstar_zero P hk z ⟨(z - 1).toNat, he1⟩ ⟨z.toNat, he2⟩ hc1 hc2
  have hzero := ConfigLoop.empty_edges_at_arrivalfree (m := pdMm P) (pdUp P) z hbal
    (fun y hy hs => hZ y hy (hs ▸ hz)) ⟨z.toNat, he2⟩ (Or.inl hc2)
  have hpos := pdMm_pos P ⟨z.toNat, he2⟩
    (by show P.A ≤ P.A + ((z.toNat : ℕ) : ℤ); omega)
    (by show P.A + ((z.toNat : ℕ) : ℤ) ≤ P.B; omega)
  omega

/-- **Non-vacuous**: `witZero` is a real element with a cut site, so `hZ` fails for it. -/
theorem witZero_hZ_false :
    ¬ (∀ x : Endpt (pdWidth witZero.toPathData) (pdMm witZero.toPathData),
        EndType.isArrOf (pdUp witZero.toPathData) x = true →
          EndType.siteOf x ∉ pdCutSites witZero.toPathData) := by
  refine hZ_false_of_kstar_zero witZero.toPathData witZero_pd_kstar ?_
  rw [witZero_cutSites]
  exact ⟨2, by simp⟩

end Sharpness

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
#print axioms VZigzag.link_of_turn_gen
#print axioms VZigzag.allJoined_step_gen
#print axioms VZigzag.allJoined_biUnion_gen
#print axioms VZigzag.hrun_of_allJoined_gen
#print axioms VZigzag.vbot_eq_or_partner
#print axioms VZigzag.vzC_step
#print axioms VZigzag.vChain_joined
#print axioms VZigzag.vz_spine_pass
#print axioms VZigzag.vz_spine_virt
#print axioms VZigzag.vz_virt_spine
#print axioms VZigzag.vz_spine_bounce
#print axioms VZigzag.vz_virt_bounce
#print axioms VZigzag.vz_chain_pass
#print axioms VZigzag.vz_run_joined
#print axioms VZigzag.vz_cover
#print axioms VZigzag.vz_runs_connected
#print axioms VZigzag.vz_hsep
#print axioms VZigzag.vz_hvirt
#print axioms VZigzag.vz_hruns
#print axioms VZigzag.vz_shield_law
#print axioms VZigzag.vz_shield_law_exists
#print axioms VZigzag.C3_noCut
#print axioms VZigzag.vz_witness_shield
#print axioms VZigzag.pdWidth_cast
#print axioms VZigzag.kstar_le_B
#print axioms VZigzag.A_le_kstar
#print axioms VZigzag.pdMm_odd_of_travel
#print axioms VZigzag.pdMm_even_of_no_travel
#print axioms VZigzag.pdVZpos
#print axioms VZigzag.pdVZpos_noCut
#print axioms VZigzag.pd_hoc
#print axioms VZigzag.pd_shield_law_pos
#print axioms VZigzag.pd_shield_exists_pos
#print axioms VZigzag.pdVZneg
#print axioms VZigzag.pdVZneg_noCut
#print axioms VZigzag.pd_shield_law_neg
#print axioms VZigzag.pd_shield_exists
#print axioms VZigzag.Elt_shield_exists
#print axioms VZigzag.witNeg_hne0
#print axioms VZigzag.witNeg_hne1
#print axioms VZigzag.witNeg_shield

#print axioms VZigzag.mem_pdCutSites_zero
#print axioms VZigzag.mem_pdCutSites_kstar
#print axioms VZigzag.not_cut_at_zero_pos
#print axioms VZigzag.cut_at_kstar_iff_pos
#print axioms VZigzag.cut_at_zero_iff_zero
#print axioms VZigzag.pd_hne0_of_pos
#print axioms VZigzag.pd_hne1_of_pos_delta
#print axioms VZigzag.pd_hne1_of_neg_not_delta
#print axioms VZigzag.pd_hne0_neg_iff
#print axioms VZigzag.pd_hne1_pos_iff
#print axioms VZigzag.pdMm_evenWidths_of_kstar_zero
#print axioms VZigzag.pd_shield_law_zero
#print axioms VZigzag.pd_defect_pos
#print axioms VZigzag.pd_defect_neg
#print axioms VZigzag.pd_defect_zero
#print axioms VZigzag.Elt_c_eq_defect_pos
#print axioms VZigzag.Elt_c_eq_defect_neg
#print axioms VZigzag.Elt_c_eq_defect_zero
#print axioms VZigzag.pd_shield_law_pos_delta
#print axioms VZigzag.pd_shield_law_neg_not_delta
#print axioms VZigzag.Elt_defect_eq_c
#print axioms VZigzag.Elt_defect_eq_c_free
#print axioms VZigzag.witZero
#print axioms VZigzag.witZero_occ
#print axioms VZigzag.witZero_width
#print axioms VZigzag.witZero_cutSites
#print axioms VZigzag.witZero_shield
#print axioms VZigzag.witZero_defect
#print axioms VZigzag.witZero_c
#print axioms VZigzag.witCut0
#print axioms VZigzag.witCut0_occ
#print axioms VZigzag.witCut0_hne0_fails
#print axioms VZigzag.witCut0_noCut
#print axioms VZigzag.witCutK
#print axioms VZigzag.witCutK_occ
#print axioms VZigzag.witCutK_hne1_fails
#print axioms VZigzag.witCutK_noCut
#print axioms VZigzag.pd_balanced_at_cut
#print axioms VZigzag.pd_balanced_of_kstar_zero
#print axioms VZigzag.hZ_false_at_cut
#print axioms VZigzag.hZ_false_of_kstar_zero
#print axioms VZigzag.witZero_hZ_false
