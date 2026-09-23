import PhiLipschitz
/-! metricAll: word length = lRTrue + 2 cTrue for every element (reachability via reaches_of_phiZ). -/
theorem allReach (g : EltBridge.Elt) : EltBridge.Elt.Reachable g := ⟨_, PhiLipschitz.reaches_of_phiZ g⟩
theorem metricAll (g : EltBridge.Elt) : (EltBridge.Elt.wordLength g : ℤ) = (CorrectedSpan.lRTrue g : ℤ) + 2 * (CorrectedSpan.cTrue g : ℤ) := PhiLipschitz.wordLength_eq_lRTrue_add_two_cTrue (allReach g)
#print axioms metricAll
