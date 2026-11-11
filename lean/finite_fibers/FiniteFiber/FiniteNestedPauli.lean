import FiniteFiber.FinitePauliStabilizer
import FiniteFiber.FiniteLocalPauli

/-!
# Nested finite Pauli stabilizer densities

This file closes the finite-group bridge between an actual larger stabilizer
group and an actual smaller stabilizer group.  The contract records a chosen
tensor-product coordinate factorization, an injective inclusion of the smaller
group, and the exact statement that the elements trivial on the discarded
factor are precisely the included smaller group.

Unlike `CompatibleSignedPauliExpressionData`, this interface starts from two
actual `FinitePauliStabilizerData` instances.  Its compatibility theorem will
therefore identify the normalized signed-Pauli expressions with positive,
trace-one stabilizer density matrices.
-/

namespace FiniteFiber

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

/--
Actual nested finite stabilizer-group data for a retained `n`-qubit factor and
a discarded `m`-qubit factor.

The coordinate equivalence is explicit because `QubitIndex (n + m)` is only
canonically equivalent, not definitionally equal, to
`QubitIndex n × QubitIndex m`.
-/
structure NestedFinitePauliStabilizerData
    (G H : Type*) [Group G] [Group H] (n m : ℕ) where
  /-- The actual stabilizer group on the larger `n + m` qubit region. -/
  large : FinitePauliStabilizerData G (n + m)
  /-- The actual stabilizer group on the retained `n`-qubit region. -/
  small : FinitePauliStabilizerData H n
  /-- The chosen tensor-product coordinate factorization of the larger block. -/
  coordinateEquiv : QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m
  /-- Signed-Pauli phase of a larger-group element in tensor coordinates. -/
  negative : G → Bool
  /-- Its Pauli labels on the retained factor. -/
  left : G → Fin n → PauliLabel
  /-- Its Pauli labels on the discarded factor. -/
  right : G → Fin m → PauliLabel
  /-- Each larger stabilizer is a signed bipartite Pauli term in these coordinates. -/
  large_decomposes : ∀ g : G,
    Matrix.reindex coordinateEquiv coordinateEquiv (large.representation g) =
      signedBipartitePauliTerm (negative g) (left g) (right g)
  /-- Inclusion of the smaller local stabilizer group into the larger one. -/
  inclusion : H →* G
  /-- It is an actual subgroup inclusion. -/
  inclusion_injective : Function.Injective inclusion
  /-- Exactly the terms trivial on the discarded factor come from the smaller group. -/
  survivor_iff : ∀ g : G,
    IsIdentityPauliString (right g) ↔ ∃ h : H, inclusion h = g
  /-- The inclusion preserves the signed Pauli phase. -/
  negative_compat : ∀ h : H, negative (inclusion h) = small.negative h
  /-- The inclusion preserves retained Pauli labels. -/
  left_compat : ∀ h : H, left (inclusion h) = small.labels h

namespace NestedFinitePauliStabilizerData

variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/-- The larger actual density matrix expressed in tensor-product coordinates. -/
noncomputable def reindexedLargeDensity [Fintype G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ D.coordinateEquiv D.coordinateEquiv)
    D.large.stabilizerDensity

/--
The actual nested-group data instantiate the generic signed-Pauli expression
interface.  The preceding group, inclusion, and decomposition fields certify
that this is an instance coming from stabilizer groups rather than an arbitrary
finite family of signed terms.
-/
noncomputable def toCompatibleSignedPauliExpressionData
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    CompatibleSignedPauliExpressionData G n m where
  largeTerms := Finset.univ
  smallTerms := Finset.univ.image D.inclusion
  negative := D.negative
  left := D.left
  right := D.right
  survivor_eq := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact D.survivor_iff g

/--
The tensor-coordinate form of the actual larger stabilizer density is the
normalized signed-Pauli expression determined by its decomposed group
elements.
-/
theorem reindexedLargeDensity_eq_normalisedSignedBipartitePauliSum [Fintype G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    D.reindexedLargeDensity =
      normalisedSignedBipartitePauliSum Finset.univ D.negative D.left D.right := by
  unfold reindexedLargeDensity FinitePauliStabilizerData.stabilizerDensity
  rw [map_smul]
  unfold FinitePauliStabilizerData.stabilizerSum
    normalisedSignedBipartitePauliSum signedBipartitePauliSum
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact D.large_decomposes g

/-- Reindexing the larger finite stabilizer density preserves positive semidefiniteness. -/
theorem reindexedLargeDensity_posSemidef [Fintype G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    D.reindexedLargeDensity.PosSemidef := by
  unfold reindexedLargeDensity
  change (D.large.stabilizerDensity.submatrix D.coordinateEquiv.symm
    D.coordinateEquiv.symm).PosSemidef
  exact (Matrix.posSemidef_submatrix_equiv D.coordinateEquiv.symm).mpr
    D.large.stabilizerDensity_posSemidef

/-- The right-identity terms of the larger group are exactly the included smaller group. -/
theorem survivor_finset_eq_image [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    Finset.univ.filter (fun g => IsIdentityPauliString (D.right g)) =
      Finset.univ.image D.inclusion := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  exact D.survivor_iff g

/--
The normalized expression over the included smaller group is its actual
stabilizer density matrix.
-/
theorem normalisedSignedPauliSum_image_inclusion_eq_smallDensity
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    normalisedSignedPauliSum (Finset.univ.image D.inclusion) D.negative D.left =
      D.small.stabilizerDensity := by
  rw [D.small.stabilizerDensity_eq_normalisedSignedPauliSum]
  unfold normalisedSignedPauliSum signedPauliSum
  congr 1
  rw [Finset.sum_image]
  · simp_rw [D.negative_compat, D.left_compat]
  · exact Set.injOn_of_injective D.inclusion_injective

/--
In tensor-product coordinates, the included smaller stabilizer acts as the
smaller stabilizer tensor the identity on the discarded factor.
-/
theorem reindex_inclusion_representation
    (D : NestedFinitePauliStabilizerData G H n m) (h : H) :
    Matrix.reindex D.coordinateEquiv D.coordinateEquiv
      (D.large.representation (D.inclusion h)) =
      D.small.representation h ⊗ₖ 1 := by
  have hright : IsIdentityPauliString (D.right (D.inclusion h)) := by
    exact (D.survivor_iff (D.inclusion h)).mpr ⟨h, rfl⟩
  have hright_eq : D.right (D.inclusion h) = fun _ : Fin m => PauliLabel.I := by
    funext i
    exact hright i
  rw [D.large_decomposes, D.negative_compat, D.left_compat, hright_eq]
  rw [signedBipartitePauliTerm_right_all_I]
  rw [D.small.representation_eq h,
    FinitePauliStabilizerData.signedPauliStringMatrix_eq_signedPauliTerm]

/--
The actual nested finite stabilizer densities satisfy the manuscript's
partial-trace compatibility equation in the chosen tensor coordinates.
-/
theorem partialTrace_reindexedLargeDensity_eq_smallDensity
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    partialTraceRight D.reindexedLargeDensity = D.small.stabilizerDensity := by
  rw [D.reindexedLargeDensity_eq_normalisedSignedBipartitePauliSum]
  rw [partialTraceRight_normalisedSignedBipartitePauliSum]
  rw [D.survivor_finset_eq_image]
  exact D.normalisedSignedPauliSum_image_inclusion_eq_smallDensity

/-- The tensor-coordinate larger density remains trace-normalized. -/
theorem reindexedLargeDensity_trace [Fintype G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    D.reindexedLargeDensity.trace = 1 := by
  unfold reindexedLargeDensity
  change (Matrix.reindex D.coordinateEquiv D.coordinateEquiv
    D.large.stabilizerDensity).trace = 1
  rw [trace_reindex]
  exact D.large.stabilizerDensity_trace

/-- The generic large expression instantiated by the nested groups is the actual larger density. -/
theorem compatible_largeExpression_eq_reindexedLargeDensity
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    (D.toCompatibleSignedPauliExpressionData).largeExpression =
      D.reindexedLargeDensity := by
  change normalisedSignedBipartitePauliSum Finset.univ D.negative D.left D.right =
    D.reindexedLargeDensity
  exact D.reindexedLargeDensity_eq_normalisedSignedBipartitePauliSum.symm

/-- The generic small expression instantiated by the nested groups is the actual smaller density. -/
theorem compatible_smallExpression_eq_smallDensity
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    (D.toCompatibleSignedPauliExpressionData).smallExpression =
      D.small.stabilizerDensity := by
  change normalisedSignedPauliSum (Finset.univ.image D.inclusion) D.negative D.left =
    D.small.stabilizerDensity
  exact D.normalisedSignedPauliSum_image_inclusion_eq_smallDensity

/-- The generic expression compatibility theorem specializes exactly to the actual density theorem. -/
theorem compatible_partialTrace_largeExpression_eq_smallExpression
    [Fintype G] [Fintype H] [DecidableEq G]
    (D : NestedFinitePauliStabilizerData G H n m) :
    partialTraceRight (D.toCompatibleSignedPauliExpressionData).largeExpression =
      (D.toCompatibleSignedPauliExpressionData).smallExpression :=
  (D.toCompatibleSignedPauliExpressionData).partialTrace_largeExpression

end NestedFinitePauliStabilizerData

end FiniteFiber
