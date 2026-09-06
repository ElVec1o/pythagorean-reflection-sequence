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
