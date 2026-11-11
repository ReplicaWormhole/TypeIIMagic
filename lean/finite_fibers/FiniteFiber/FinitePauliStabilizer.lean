import FiniteFiber.FiniteStabilizerTrace
import FiniteFiber.FiniteDensity
import FiniteFiber.FinitePauli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite stabilizer groups realized by Pauli strings

This file connects an actual finite-dimensional Pauli-string realization to
the tracelessness hypothesis used by the finite stabilizer density formula.
The phase convention is explicit: a represented group element is a signed
Pauli string, the representation is faithful, and no element is `-1`.

These are the exact finite-volume conditions that rule out a nonidentity
traceful stabilizer element.  The infinite-lattice local-group construction is
still a later layer.
-/

namespace FiniteFiber

open scoped BigOperators ComplexOrder Matrix MatrixOrder

/-- A sign times a tensor-product Pauli string. -/
def signedPauliStringMatrix {n : ℕ} (negative : Bool)
    (labels : Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  if negative then -pauliStringMatrix labels else pauliStringMatrix labels

/--
A faithful finite stabilizer group represented by signed Pauli strings.

`no_negative_identity` is the finite consistency condition excluding `-\id`.
It is deliberately stated on the actual represented matrices rather than
silently inferred from a choice of generators.
-/
structure FinitePauliStabilizerData (G : Type*) [Group G] (n : ℕ) where
  representation : G →* Matrix (QubitIndex n) (QubitIndex n) ℂ
  negative : G → Bool
  labels : G → Fin n → PauliLabel
  representation_eq : ∀ g : G,
    representation g = signedPauliStringMatrix (negative g) (labels g)
  injective : Function.Injective representation
  no_negative_identity : ∀ g : G,
    representation g ≠ (-1 : Matrix (QubitIndex n) (QubitIndex n) ℂ)

namespace FinitePauliStabilizerData

variable {G : Type*} [Group G] {n : ℕ}

/-- A nonidentity stabilizer cannot have the all-identity Pauli label. -/
theorem exists_nonidentity_label_of_ne_one
    (D : FinitePauliStabilizerData G n) {g : G} (hg : g ≠ 1) :
    ∃ i, D.labels g i ≠ PauliLabel.I := by
  classical
  by_contra h
  push_neg at h
  have hlabels : D.labels g = fun _ : Fin n => PauliLabel.I := by
    funext i
    exact h i
  cases hnegative : D.negative g with
  | false =>
      have hrep : D.representation g = D.representation 1 := by
        calc
          D.representation g =
              signedPauliStringMatrix (D.negative g) (D.labels g) :=
            D.representation_eq g
          _ = 1 := by simp [hnegative, hlabels, signedPauliStringMatrix,
            pauliStringMatrix_all_I]
          _ = D.representation 1 := D.representation.map_one.symm
      exact hg (D.injective hrep)
  | true =>
      apply D.no_negative_identity g
      calc
        D.representation g =
            signedPauliStringMatrix (D.negative g) (D.labels g) :=
          D.representation_eq g
        _ = -1 := by simp [hnegative, hlabels, signedPauliStringMatrix,
          pauliStringMatrix_all_I]

/-- Every nonidentity stabilizer is traceless in the finite Pauli realization. -/
theorem representation_trace_eq_zero_of_ne_one
    (D : FinitePauliStabilizerData G n) {g : G} (hg : g ≠ 1) :
    (D.representation g).trace = 0 := by
  obtain hlabel := D.exists_nonidentity_label_of_ne_one hg
  rw [D.representation_eq g, signedPauliStringMatrix]
  cases D.negative g <;>
    simp [Matrix.trace_neg,
      pauliStringMatrix_trace_eq_zero_of_exists_ne_I _ hlabel]

/-- The signed Pauli realization supplies self-adjoint stabilizer matrices. -/
theorem representation_isSelfAdjoint
    (D : FinitePauliStabilizerData G n) (g : G) :
    IsSelfAdjoint (D.representation g) := by
  rw [D.representation_eq g, signedPauliStringMatrix]
  cases D.negative g
  · exact pauliStringMatrix_isSelfAdjoint (D.labels g)
  · exact (pauliStringMatrix_isSelfAdjoint (D.labels g)).neg

/-- The unnormalized finite stabilizer sum. -/
noncomputable def stabilizerSum [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ∑ g : G, D.representation g

/-- The normalized group-average code projector. -/
noncomputable def stabilizerProjector [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • D.stabilizerSum

/-- The finite stabilizer density-matrix expression. -/
noncomputable def stabilizerDensity [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ((2 : ℂ) ^ n)⁻¹ • D.stabilizerSum

/-- Every represented stabilizer fixes the group-average projector on the left. -/
theorem representation_mul_stabilizerProjector_left [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.representation g * D.stabilizerProjector = D.stabilizerProjector := by
  simp only [stabilizerProjector, stabilizerSum, mul_smul_comm, Finset.mul_sum]
  rw [show (fun h : G => D.representation g * D.representation h) =
      fun h : G => D.representation (g * h) by
    funext h
    exact (D.representation.map_mul g h).symm]
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) D.representation]

/-- Every represented stabilizer fixes the group-average projector on the right. -/
theorem stabilizerProjector_mul_representation_right [Fintype G]
    (D : FinitePauliStabilizerData G n) (g : G) :
    D.stabilizerProjector * D.representation g = D.stabilizerProjector := by
  simp only [stabilizerProjector, stabilizerSum, smul_mul_assoc, Finset.sum_mul]
  rw [show (fun h : G => D.representation h * D.representation g) =
      fun h : G => D.representation (h * g) by
    funext h
    exact (D.representation.map_mul h g).symm]
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) D.representation]

/-- The finite stabilizer group average is idempotent. -/
theorem stabilizerProjector_isIdempotent [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerProjector * D.stabilizerProjector = D.stabilizerProjector := by
  nth_rewrite 1 [stabilizerProjector]
  rw [smul_mul_assoc, stabilizerSum, Finset.sum_mul]
  simp_rw [D.representation_mul_stabilizerProjector_left]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- The finite stabilizer group average is self-adjoint. -/
theorem stabilizerProjector_isSelfAdjoint [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    IsSelfAdjoint D.stabilizerProjector := by
  change star D.stabilizerProjector = D.stabilizerProjector
  rw [stabilizerProjector, stabilizerSum, star_smul]
  have hscalar : star ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ := by
    norm_num
  rw [hscalar]
  rw [star_sum]
  have hself (g : G) : star (D.representation g) = D.representation g :=
    (D.representation_isSelfAdjoint g).star_eq
  simp_rw [hself]

/-- The finite stabilizer group average is a self-adjoint projection. -/
theorem stabilizerProjector_isStarProjection [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    IsStarProjection D.stabilizerProjector :=
  ⟨D.stabilizerProjector_isIdempotent, D.stabilizerProjector_isSelfAdjoint⟩

/-- The unnormalized stabilizer sum has only the identity trace contribution. -/
theorem stabilizerSum_trace [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    (D.stabilizerSum).trace = (2 : ℂ) ^ n := by
  rw [stabilizerSum]
  calc
    (∑ g : G, D.representation g).trace = ∑ g : G, (D.representation g).trace := by
      simp
    _ = (D.representation 1).trace := by
      exact Fintype.sum_eq_single 1 (fun g hg => D.representation_trace_eq_zero_of_ne_one hg)
    _ = (2 : ℂ) ^ n := by
      rw [D.representation.map_one, Matrix.trace_one, qubitIndex_card]
      norm_cast

/-- The group-average projector has the manuscript's finite-volume trace. -/
theorem stabilizerProjector_trace [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    (D.stabilizerProjector).trace =
      (Fintype.card G : ℂ)⁻¹ * (2 : ℂ) ^ n := by
  rw [stabilizerProjector, Matrix.trace_smul, stabilizerSum_trace]
  rfl

/-- The finite stabilizer density expression has trace one. -/
theorem stabilizerDensity_trace [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    (D.stabilizerDensity).trace = 1 := by
  rw [stabilizerDensity, Matrix.trace_smul, stabilizerSum_trace]
  change ((2 : ℂ) ^ n)⁻¹ * (2 : ℂ) ^ n = 1
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

/-- The density expression is the group-average projector divided by its trace. -/
theorem stabilizerDensity_eq_trace_normalized_projector [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerDensity = (D.stabilizerProjector.trace)⁻¹ • D.stabilizerProjector := by
  rw [stabilizerDensity, stabilizerProjector, Matrix.trace_smul,
    stabilizerSum_trace, smul_smul]
  congr 1
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hdim : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  simp [hcard]

/-- The finite density is supported on its stabilizer code projector. -/
theorem stabilizerDensity_mul_projector [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerDensity * D.stabilizerProjector = D.stabilizerDensity := by
  rw [D.stabilizerDensity_eq_trace_normalized_projector, smul_mul_assoc,
    D.stabilizerProjector_isStarProjection.1]

/-- The two signed-Pauli conventions used by the finite layers coincide. -/
theorem signedPauliStringMatrix_eq_signedPauliTerm (negative : Bool)
    (labels : Fin n → PauliLabel) :
    signedPauliStringMatrix negative labels = signedPauliTerm negative labels := by
  cases negative <;> simp [signedPauliStringMatrix, signedPauliTerm, pauliSign]

/--
The concrete stabilizer density is exactly the normalized finite signed-Pauli
sum.  This identifies the group-average formula with one instance of the
generic normalized signed-Pauli expression layer; it does not identify two
nested local groups or prove their survivor condition.
-/
theorem stabilizerDensity_eq_normalisedSignedPauliSum [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerDensity =
      normalisedSignedPauliSum Finset.univ D.negative D.labels := by
  rw [stabilizerDensity, stabilizerSum, normalisedSignedPauliSum, signedPauliSum]
  congr 1
  change (∑ g : G, D.representation g) =
    ∑ g : G, signedPauliTerm (D.negative g) (D.labels g)
  apply Finset.sum_congr rfl
  intro g hg
  rw [D.representation_eq]
  exact signedPauliStringMatrix_eq_signedPauliTerm _ _

/-- The finite code projector is positive semidefinite. -/
theorem stabilizerProjector_posSemidef [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerProjector.PosSemidef := by
  have hprojection := D.stabilizerProjector_isStarProjection
  have hstar : D.stabilizerProjectorᴴ = D.stabilizerProjector := by
    simpa only [Matrix.star_eq_conjTranspose] using hprojection.2.star_eq
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self D.stabilizerProjector
  rw [hstar, hprojection.1] at hpositive
  exact hpositive

/-- The stabilizer density is a positive scalar multiple of its code projector. -/
theorem stabilizerDensity_eq_projector_scalar [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerDensity =
      ((Fintype.card G : ℂ) * ((2 : ℂ) ^ n)⁻¹) • D.stabilizerProjector := by
  rw [stabilizerDensity, stabilizerProjector, smul_smul]
  congr 1
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The finite stabilizer density matrix is positive semidefinite. -/
theorem stabilizerDensity_posSemidef [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerDensity.PosSemidef := by
  rw [D.stabilizerDensity_eq_projector_scalar]
  apply Matrix.PosSemidef.smul D.stabilizerProjector_posSemidef
  positivity

/-- The finite-volume functional defined by the stabilizer density matrix. -/
noncomputable def stabilizerStateFunctional [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →ₗ[ℂ] ℂ where
  toFun A := (D.stabilizerDensity * A).trace
  map_add' A B := by
    simp [mul_add]
  map_smul' c A := by
    simp

/-- The finite-volume stabilizer functional is normalized. -/
theorem stabilizerStateFunctional_one [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerStateFunctional 1 = 1 := by
  simp [stabilizerStateFunctional, D.stabilizerDensity_trace]

/-- The finite stabilizer state assigns expectation one to its code projector. -/
theorem stabilizerStateFunctional_projector [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerStateFunctional D.stabilizerProjector = 1 := by
  change (D.stabilizerDensity * D.stabilizerProjector).trace = 1
  rw [D.stabilizerDensity_mul_projector, D.stabilizerDensity_trace]

/-- The finite-volume stabilizer functional is positive on elements `a^* a`. -/
theorem stabilizerStateFunctional_star_mul_self_nonneg [Fintype G]
    (D : FinitePauliStabilizerData G n)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    0 ≤ D.stabilizerStateFunctional (star A * A) := by
  change 0 ≤ (D.stabilizerDensity * (Aᴴ * A)).trace
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (D.stabilizerDensity_posSemidef.mul_mul_conjTranspose_same A).trace_nonneg

/-- The finite-volume stabilizer functional is nonnegative on every positive matrix. -/
theorem stabilizerStateFunctional_nonneg [Fintype G]
    (D : FinitePauliStabilizerData G n)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) (hA : 0 ≤ A) :
    0 ≤ D.stabilizerStateFunctional A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  change 0 ≤ (D.stabilizerDensity * A).trace
  rw [hB, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (D.stabilizerDensity_posSemidef.mul_mul_conjTranspose_same B).trace_nonneg

/-- The finite stabilizer density defines a positive complex-linear functional. -/
noncomputable def stabilizerPositiveFunctional [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ D.stabilizerStateFunctional
    (fun A hA => D.stabilizerStateFunctional_nonneg A hA)

/-- The bundled finite stabilizer functional remains normalized. -/
theorem stabilizerPositiveFunctional_one [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerPositiveFunctional 1 = 1 :=
  D.stabilizerStateFunctional_one

/--
The finite matrix trace is tracial after compression by any idempotent matrix.
This is stated in the exact five-factor form used by the code-projector
calculation below.
-/
theorem projector_compressed_trace_comm
    {k : Type*} [Fintype k] [DecidableEq k]
    (P A B : Matrix k k ℂ) (hP : P * P = P) :
    ((P * A * P) * (P * B * P)).trace =
      ((P * B * P) * (P * A * P)).trace := by
  calc
    ((P * A * P) * (P * B * P)).trace =
        (P * A * (P * P) * B * P).trace := by
      congr 1
      noncomm_ring
    _ = (P * A * P * B * P).trace := by rw [hP]
    _ = (P * (A * P * B * P)).trace := by
      congr 1
      noncomm_ring
    _ = ((A * P * B * P) * P).trace := Matrix.trace_mul_comm _ _
    _ = (A * P * B * P).trace := by
      congr 1
      calc
        (A * P * B * P) * P = A * P * B * (P * P) := by noncomm_ring
        _ = A * P * B * P := by rw [hP]
    _ = (A * (P * B * P)).trace := by
      congr 1
      noncomm_ring
    _ = ((P * B * P) * A).trace := Matrix.trace_mul_comm _ _
    _ = (P * ((P * B * P) * A)).trace := by
      congr 1
      calc
        (P * B * P) * A = P * B * P * A := by noncomm_ring
        _ = (P * P) * B * P * A := by rw [hP]
        _ = P * ((P * B * P) * A) := by noncomm_ring
    _ = (((P * B * P) * A) * P).trace := Matrix.trace_mul_comm _ _
    _ = ((P * B * P) * (P * A * P)).trace := by
      congr 1
      calc
        ((P * B * P) * A) * P = P * B * P * A * P := by noncomm_ring
        _ = P * B * (P * P) * A * P := by rw [hP]
        _ = (P * B * P) * (P * A * P) := by noncomm_ring

/--
The finite stabilizer state is tracial on the code-space corner.  This is the
finite-dimensional matrix-trace step used before the manuscript takes strong
limits and invokes density.
-/
theorem stabilizerStateFunctional_compress_mul_comm [Fintype G]
    (D : FinitePauliStabilizerData G n)
    (A B : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    D.stabilizerStateFunctional
        ((D.stabilizerProjector * A * D.stabilizerProjector) *
          (D.stabilizerProjector * B * D.stabilizerProjector)) =
      D.stabilizerStateFunctional
        ((D.stabilizerProjector * B * D.stabilizerProjector) *
          (D.stabilizerProjector * A * D.stabilizerProjector)) := by
  change (D.stabilizerDensity *
    ((D.stabilizerProjector * A * D.stabilizerProjector) *
      (D.stabilizerProjector * B * D.stabilizerProjector))).trace =
    (D.stabilizerDensity *
      ((D.stabilizerProjector * B * D.stabilizerProjector) *
        (D.stabilizerProjector * A * D.stabilizerProjector))).trace
  rw [D.stabilizerDensity_eq_trace_normalized_projector]
  rw [smul_mul_assoc, Matrix.trace_smul, smul_mul_assoc, Matrix.trace_smul]
  have hleft : D.stabilizerProjector *
      ((D.stabilizerProjector * A * D.stabilizerProjector) *
        (D.stabilizerProjector * B * D.stabilizerProjector)) =
      (D.stabilizerProjector * A * D.stabilizerProjector) *
        (D.stabilizerProjector * B * D.stabilizerProjector) := by
    calc
      D.stabilizerProjector *
          ((D.stabilizerProjector * A * D.stabilizerProjector) *
            (D.stabilizerProjector * B * D.stabilizerProjector)) =
          (D.stabilizerProjector * D.stabilizerProjector) * A *
            D.stabilizerProjector *
            (D.stabilizerProjector * B * D.stabilizerProjector) := by
              noncomm_ring
      _ = (D.stabilizerProjector * A * D.stabilizerProjector) *
            (D.stabilizerProjector * B * D.stabilizerProjector) := by
              rw [D.stabilizerProjector_isStarProjection.1]
  have hright : D.stabilizerProjector *
      ((D.stabilizerProjector * B * D.stabilizerProjector) *
        (D.stabilizerProjector * A * D.stabilizerProjector)) =
      (D.stabilizerProjector * B * D.stabilizerProjector) *
        (D.stabilizerProjector * A * D.stabilizerProjector) := by
    calc
      D.stabilizerProjector *
          ((D.stabilizerProjector * B * D.stabilizerProjector) *
            (D.stabilizerProjector * A * D.stabilizerProjector)) =
          (D.stabilizerProjector * D.stabilizerProjector) * B *
            D.stabilizerProjector *
            (D.stabilizerProjector * A * D.stabilizerProjector) := by
              noncomm_ring
      _ = (D.stabilizerProjector * B * D.stabilizerProjector) *
            (D.stabilizerProjector * A * D.stabilizerProjector) := by
              rw [D.stabilizerProjector_isStarProjection.1]
  rw [hleft, hright]
  exact congrArg (fun x : ℂ => (D.stabilizerProjector.trace)⁻¹ * x)
    (projector_compressed_trace_comm D.stabilizerProjector A B
      D.stabilizerProjector_isStarProjection.1)

/--
Transport a finite Pauli stabilizer representation through any unital
star-algebra representation.  This is the precise form needed when the
finite matrix algebra is represented on a later GNS Hilbert space.
-/
noncomputable def actionInRepresentation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : FinitePauliStabilizerData G n)
    (π : Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    SelfAdjointFiniteGroupAction (H := H) (G := G) where
  representation :=
    { toFun := fun g => π (D.representation g)
      map_one' := by
        simp
      map_mul' := by
        intro g h
        simp }
  selfAdjoint := fun g => (D.representation_isSelfAdjoint g).map π

/-- A represented finite group average is the representation of the code projector. -/
theorem actionInRepresentation_average_eq [Fintype G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : FinitePauliStabilizerData G n)
    (π : Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (D.actionInRepresentation π).average = π D.stabilizerProjector := by
  change (Fintype.card G : ℂ)⁻¹ • ∑ g : G, π (D.representation g) =
    π ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, D.representation g)
  rw [map_smul, map_sum]

/--
The concrete Pauli matrices act on the finite Euclidean qubit Hilbert space.
This is the exact bridge from the matrix realization to the abstract
finite-group-average layer; it does not yet assert an infinite-volume GNS
realization.
-/
noncomputable def operatorAction
    (D : FinitePauliStabilizerData G n) :
    SelfAdjointFiniteGroupAction
      (H := EuclideanSpace ℂ (QubitIndex n)) (G := G) where
  representation :=
    { toFun := fun g => Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)
        (D.representation g)
      map_one' := by
        simp
      map_mul' := by
        intro g h
        simp }
  selfAdjoint := fun g =>
    (D.representation_isSelfAdjoint g).map
      (Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ))

/-- The abstract average of `operatorAction` is exactly the matrix code projector. -/
theorem operatorAction_average_eq_stabilizerProjector [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.operatorAction.average =
      Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)
        D.stabilizerProjector := by
  change (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
      Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ) (D.representation g) =
    Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)
      ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, D.representation g)
  rw [map_smul, map_sum]

/-- The operator trace of a represented Pauli stabilizer is its ordinary matrix trace. -/
theorem operatorAction_operatorTrace_eq_matrixTrace
    (D : FinitePauliStabilizerData G n) (g : G) :
    finiteGroupOperatorTrace (D.operatorAction.representation g) =
      (D.representation g).trace := by
  unfold finiteGroupOperatorTrace
  change LinearMap.trace ℂ (EuclideanSpace ℂ (QubitIndex n))
    ((Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)
      (D.representation g)).toLinearMap) = (D.representation g).trace
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rw [show (Matrix.toEuclideanLin :
      Matrix (QubitIndex n) (QubitIndex n) ℂ ≃ₗ[ℂ]
        (EuclideanSpace ℂ (QubitIndex n) →ₗ[ℂ] EuclideanSpace ℂ (QubitIndex n))) =
      Matrix.toLin (EuclideanSpace.basisFun (QubitIndex n) ℂ).toBasis
        (EuclideanSpace.basisFun (QubitIndex n) ℂ).toBasis from
        Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq _ _

/-- Nonidentity elements of the concrete operator action are traceless. -/
theorem operatorAction_traceless_of_ne_one
    (D : FinitePauliStabilizerData G n) {g : G} (hg : g ≠ 1) :
    finiteGroupOperatorTrace (D.operatorAction.representation g) = 0 := by
  rw [D.operatorAction_operatorTrace_eq_matrixTrace]
  exact D.representation_trace_eq_zero_of_ne_one hg

/-- The finite matrix code projector is nonzero, by its explicit nonzero trace. -/
theorem stabilizerProjector_ne_zero [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.stabilizerProjector ≠ 0 := by
  intro hzero
  have htrace := D.stabilizerProjector_trace
  rw [hzero] at htrace
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hdim : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_ne_zero (inv_ne_zero hcard) hdim) (by simpa using htrace.symm)

/-- The corresponding abstract finite-group average is nonzero as well. -/
theorem operatorAction_average_ne_zero [Fintype G]
    (D : FinitePauliStabilizerData G n) :
    D.operatorAction.average ≠ 0 := by
  intro hzero
  apply D.stabilizerProjector_ne_zero
  apply (Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)).injective
  calc
    (Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)).toRingEquiv
        D.stabilizerProjector = D.operatorAction.average :=
      D.operatorAction_average_eq_stabilizerProjector.symm
    _ = 0 := hzero
    _ = (Matrix.toEuclideanCLM (n := QubitIndex n) (𝕜 := ℂ)).toRingEquiv 0 := by simp

end FinitePauliStabilizerData

end FiniteFiber
