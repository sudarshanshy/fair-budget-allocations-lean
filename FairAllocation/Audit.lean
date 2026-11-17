import FairAllocation.Main
import FairAllocation.PaperStatements
import FairAllocation.Examples

set_option autoImplicit false

/-! Axiom audit of the exported results and the executable counterexample. -/

#print axioms FairAllocation.densestGreedy_correct
#print axioms FairAllocation.densestGreedy_correct_finset
#print axioms FairAllocation.exists_feasible_ef2
#print axioms FairAllocation.ef2_removal_witnesses
#print axioms FairAllocation.charity_removal_witness
#print axioms FairAllocation.densestGreedy_iterations_le
#print axioms FairAllocation.densestGreedy_comparisons_le
#print axioms FairAllocation.Examples.tight_not_fair_one
