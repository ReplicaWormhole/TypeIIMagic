import FiniteFiber.FiniteDensity

/-!
# Compatible finite signed-Pauli expressions

This file packages the exact partial-trace identity for normalized finite
signed-Pauli expressions.  A single ambient type indexes the large and small
term families; `survivor_eq` says precisely that the large terms which are
identity on the discarded subsystem are the small terms.  It is an explicit
hypothesis because Pauli tracelessness proves only which terms survive, not
their identification with a particular local subgroup.

No group law, positivity, or trace-one property is hidden in this structure.
Consequently its expressions are not called density matrices.  A later
lattice/stabilizer layer must construct this data from actual finite local
subgroups of a global consistent stabilizer group and identify the resulting
expressions with the positive trace-one stabilizer densities.
-/

namespace FiniteFiber

/--
Finite signed-Pauli expression data for two nested finite regions, written as
a left subsystem of `n` qubits and a discarded right subsystem of `m` qubits.
No field asserts that either finite term family is a group.
-/
structure CompatibleSignedPauliExpressionData (K : Type*) (n m : ℕ) where
  /-- Terms in the larger normalized signed-Pauli expression. -/
  largeTerms : Finset K
  /-- Terms in the smaller normalized signed-Pauli expression. -/
  smallTerms : Finset K
  /-- The Hermitian Pauli sign of an ambient term. -/
  negative : K → Bool
  /-- Its restriction to the retained qubits. -/
  left : K → Fin n → PauliLabel
  /-- Its restriction to the traced-out qubits. -/
  right : K → Fin m → PauliLabel
  /-- Exactly the terms trivial on the right are the smaller local terms. -/
  survivor_eq :
    largeTerms.filter (fun g => IsIdentityPauliString (right g)) = smallTerms

namespace CompatibleSignedPauliExpressionData

variable {K : Type*} {n m : ℕ}

/-- The normalized signed-Pauli expression on the larger finite region. -/
noncomputable def largeExpression (D : CompatibleSignedPauliExpressionData K n m) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  normalisedSignedBipartitePauliSum D.largeTerms D.negative D.left D.right

/-- The normalized signed-Pauli expression on the retained finite region. -/
noncomputable def smallExpression (D : CompatibleSignedPauliExpressionData K n m) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  normalisedSignedPauliSum D.smallTerms D.negative D.left

/--
The large and small normalized signed-Pauli expressions are compatible under
the finite partial trace.  This is the algebraic survivor step in the
manuscript's calculation, with all sign and survivor conditions visible in the
data.  It is not, by itself, a theorem about positive trace-one density
matrices.
-/
theorem partialTrace_largeExpression (D : CompatibleSignedPauliExpressionData K n m) :
    partialTraceRight D.largeExpression = D.smallExpression := by
  exact partialTraceRight_normalisedSignedBipartitePauliSum_eq_of_survivors
    D.largeTerms D.smallTerms D.negative D.left D.right D.survivor_eq

end CompatibleSignedPauliExpressionData

end FiniteFiber
