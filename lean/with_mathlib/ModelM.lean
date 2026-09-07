/-
  ModelM.lean
  ===========
  The status of the transfer model `(M)` -- "item 1" -- pinned to actual theorems.

  `paper2.tex:2244` states `(M)` in three parts, and `paper2.tex:2270-2290` gives their
  status.  This file records which parts are Lean-verified, and makes the obstruction on
  the third part citable, because it is not merely "unproved".

  (M1)  LOCAL COST LAW -- PROVED, and Lean-verified.
        `SiteCost.MarkedSite.cost_interior`, `cost_marker_near`, `cost_marker_far_left`,
        `cost_marker_far_right`, `cost_indep` (MarkedSite.lean:217-257), i.e. the paper's
        `cor:localcost` + `cor:marker`, the marker clause in its corrected form.

  (M2)  SHIELD LAW -- half proved.
        The gap-run cost and `c >= L-1` per interior run: `SiteCost.PathData.gap_run_cut`
        (Realisation.lean:603) with `cor:lRclosed` and `prop:cut`.
        The REVERSE inequality `c <= L-1` is not proved in general; it holds on the
        gap-free elements (`thm:nogap`).  This is the same reverse shield inequality
        tracked elsewhere in this repo as the `c <= |Z|` crux.

  (M3)  DECOMPOSITION `eq:assembly` -- NOT proved, and the natural contract for it is
        VACUOUS.  `EltBridge.IsAssembly` is the degree-wise form of `eq:assembly`, and
        `EltBridge.isAssembly_of_any` proves it holds for ARBITRARY `W` and `W0`
        (witness `n = 1`, `T = (X^2)`, `mu = 1`, `lam = (W - W0)(1 - X^2)`).
        `AssemblyContract.isAssemblyAll_of_any` shows removing the truncation does not
        help either: the defect is the existential over `T, lam, mu` alone.

        CONSEQUENCE, and the point of this file: a proof of `(M3)` in the existentially
        quantified form would establish NOTHING about `W`.  Anyone "finishing item 1" has
        to prove the NAMED form -- `AssemblyContract.IsMaxAssembly`, which comes with
        `isMaxAssembly_existsUnique` (it determines its subject) and
        `not_forall_isMaxAssembly` (it is not vacuous).

  So `(M)` is not finishable today: `(M1)` is done, `(M2)` is half done, and `(M3)` needs
  the named contract plus the identification of `W` with the site-kernel resolvent, which
  is open (see `wcount.rs`: `W`'s series is NOT the bulk resolvent's, so the marker-fibre
  correction carries most of the count).

  No `sorry`.
-/

import EltBridge
import AssemblyContract

namespace ModelM

/-- **(M3)'s contract, as written, is vacuous.**  Restated in the `(M)` context so it can
be cited directly: for any `W`, `W0` there are `n`, `T`, `lam`, `mu` satisfying
`EltBridge.IsAssembly`.  Hence the existential reading of `eq:assembly` is not a
statement about `W`. -/
theorem M3_contract_vacuous (W W0 : PowerSeries ℤ) :
    ∃ (n : ℕ) (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
      (lam mu : Fin 4 → Fin n → PowerSeries ℤ), EltBridge.IsAssembly W W0 T lam mu :=
  ⟨1, _, _, _, EltBridge.isAssembly_of_any W W0⟩

/-- **And the named replacement is not vacuous**, so it is the form `(M3)` must take:
it has a unique solution, hence determines `W` rather than admitting any. -/
theorem M3_named_contract_determines (M : ℕ) :
    ∃! W : PowerSeries ℤ, AssemblyContract.IsMaxAssembly (PowerSeries.X : PowerSeries ℤ) M W :=
  AssemblyContract.isMaxAssembly_existsUnique M

end ModelM

#print axioms ModelM.M3_contract_vacuous
#print axioms ModelM.M3_named_contract_determines
