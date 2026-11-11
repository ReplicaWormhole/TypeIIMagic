import FiniteFiber.FiniteRegionFullPauliMultiplication

/-!
# Axiom audit for the finite-region full-Pauli multiplication theorems

Run with `lake env lean tests/FullPauliMultiplicationAxiomAudit.lean`.  The
expected output contains only Lean's standard logical axioms (`propext`,
`Classical.choice`, and `Quot.sound`), and no project-local axioms.
-/

#print axioms FiniteFiber.normalFormOneSiteMatrix_mul
#print axioms FiniteFiber.finiteRegionTensorMatrix_mul
#print axioms FiniteFiber.finiteRegionNormalFormMatrix_mul
#print axioms FiniteFiber.binaryDot_eq_sum_of_support_subset
#print axioms FiniteFiber.cocycle_eq_finiteRegionNormalFormCocycle
#print axioms FiniteFiber.fullPauliRegionMatrix_mul
#print axioms FiniteFiber.fullPauliRegionMatrix_one
#print axioms FiniteFiber.fullPauliRegionMatrix_negativeIdentity
