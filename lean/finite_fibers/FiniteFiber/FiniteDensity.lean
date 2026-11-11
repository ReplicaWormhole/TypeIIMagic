import FiniteFiber.FinitePauli
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-dimensional signed-Pauli reductions

This file supplies the finite-matrix partial trace used by the manuscript's
compatibility calculation.  The key checked identity is that tracing out the
right tensor factor of a Kronecker product multiplies the left factor by the
ordinary trace of the right factor.  Its generic finite sums are normalized
signed-Pauli expressions; density-matrix properties enter only when a later
stabilizer-group layer supplies them.

The later stabilizer layer must still prove that the surviving Pauli terms of a
larger local group are exactly the terms of the smaller local group.
-/

namespace FiniteFiber

open scoped BigOperators Kronecker

/-- The finite-dimensional partial trace over the right matrix index. -/
noncomputable def partialTraceRight {α β : Type*} [Fintype β] :
    Matrix (α × β) (α × β) ℂ →ₗ[ℂ] Matrix α α ℂ where
  toFun A := fun i j => ∑ k : β, A (i, k) (j, k)
  map_add' A B := by
    ext i j
    simp [Finset.sum_add_distrib]
  map_smul' c A := by
    ext i j
    change (∑ k : β, c * A (i, k) (j, k)) = c * ∑ k : β, A (i, k) (j, k)
    rw [Finset.mul_sum]

/-- Partial trace of a simple tensor is the left factor times the right trace. -/
theorem partialTraceRight_kronecker
    {α β : Type*} [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    partialTraceRight (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [partialTraceRight, Matrix.trace, Finset.mul_sum, mul_comm]

/-- Taking the ordinary trace after the right partial trace preserves the trace. -/
theorem trace_partialTraceRight
    {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix (α × β) (α × β) ℂ) :
    (partialTraceRight A).trace = A.trace := by
  change (∑ i : α, ∑ k : β, A (i, k) (i, k)) =
    ∑ x : α × β, A x x
  rw [Fintype.sum_prod_type]

/-- Reindexing a square finite matrix along an equivalence preserves its trace. -/
theorem trace_reindex
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix α α ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  change (∑ i : β, A (e.symm i) (e.symm i)) = ∑ i : α, A i i
  exact e.symm.sum_comp fun i => A i i

/-- A finite Pauli label assignment acts trivially on every qubit. -/
def IsIdentityPauliString {n : ℕ} (a : Fin n → PauliLabel) : Prop :=
  ∀ i, a i = PauliLabel.I

/-- Decidability is needed only to filter a finite family of Pauli terms. -/
noncomputable instance isIdentityPauliStringDecidable
    {n : ℕ} (a : Fin n → PauliLabel) : Decidable (IsIdentityPauliString a) :=
  Classical.propDecidable _

/-- A bipartite tensor-product Pauli term. -/
def bipartitePauliTerm {n m : ℕ}
    (left : Fin n → PauliLabel) (right : Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  pauliStringMatrix left ⊗ₖ pauliStringMatrix right

/-- The scalar phase allowed for a Hermitian signed Pauli string. -/
def pauliSign (negative : Bool) : ℂ :=
  if negative then -1 else 1

/-- A signed bipartite Pauli term, including the stabilizer's `+` or `-` phase. -/
def signedBipartitePauliTerm {n m : ℕ} (negative : Bool)
    (left : Fin n → PauliLabel) (right : Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  pauliSign negative • bipartitePauliTerm left right

/-- A signed Pauli term on one finite subsystem. -/
def signedPauliTerm {n : ℕ} (negative : Bool)
    (labels : Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  pauliSign negative • pauliStringMatrix labels

/-- A signed term trivial on the right factor is the left signed term tensored with identity. -/
theorem signedBipartitePauliTerm_right_all_I
    {n m : ℕ} (negative : Bool) (left : Fin n → PauliLabel) :
    signedBipartitePauliTerm negative left (fun _ : Fin m => PauliLabel.I) =
      signedPauliTerm negative left ⊗ₖ 1 := by
  unfold signedBipartitePauliTerm signedPauliTerm bipartitePauliTerm
  rw [pauliStringMatrix_all_I]
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  simp [Matrix.kroneckerMap]
  ring

/-- Tracing a Pauli tensor term kills every term nontrivial on the right. -/
theorem partialTraceRight_bipartitePauliTerm
    {n m : ℕ} (left : Fin n → PauliLabel) (right : Fin m → PauliLabel) :
    partialTraceRight (bipartitePauliTerm left right) =
      if IsIdentityPauliString right then
        (2 : ℂ) ^ m • pauliStringMatrix left
      else 0 := by
  rw [bipartitePauliTerm, partialTraceRight_kronecker]
  by_cases hright : IsIdentityPauliString right
  · rw [if_pos hright]
    have hright_eq : right = fun _ : Fin m => PauliLabel.I := by
      funext i
      exact hright i
    rw [hright_eq, pauliStringMatrix_trace_all_I]
  · rw [if_neg hright]
    have hnontrivial : ∃ i, right i ≠ PauliLabel.I := by
      by_contra h
      apply hright
      push_neg at h
      exact h
    rw [pauliStringMatrix_trace_eq_zero_of_exists_ne_I right hnontrivial]
    simp

/-- Partial trace preserves the sign of every surviving Pauli term. -/
theorem partialTraceRight_signedBipartitePauliTerm
    {n m : ℕ} (negative : Bool)
    (left : Fin n → PauliLabel) (right : Fin m → PauliLabel) :
    partialTraceRight (signedBipartitePauliTerm negative left right) =
      if IsIdentityPauliString right then
        (2 : ℂ) ^ m • signedPauliTerm negative left
      else 0 := by
  unfold signedBipartitePauliTerm signedPauliTerm
  rw [map_smul, partialTraceRight_bipartitePauliTerm]
  by_cases hright : IsIdentityPauliString right
  · rw [if_pos hright]
    rw [if_pos hright]
    simp only [smul_smul]
    congr 1
    ring
  · rw [if_neg hright]
    simp [hright]

/-- A finite sum of bipartite Pauli tensor terms. -/
noncomputable def bipartitePauliSum {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  ∑ g ∈ terms, bipartitePauliTerm (left g) (right g)

/-- The unnormalized Pauli sum on a finite left subsystem. -/
noncomputable def pauliSum {γ : Type*} {n : ℕ}
    (terms : Finset γ) (labels : γ → Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ∑ g ∈ terms, pauliStringMatrix (labels g)

/-- The normalization used by a finite `n`-qubit Pauli density expression. -/
noncomputable def normalisedPauliSum {γ : Type*} {n : ℕ}
    (terms : Finset γ) (labels : γ → Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ((2 : ℂ) ^ n)⁻¹ • pauliSum terms labels

/-- The normalization used by a bipartite `n + m` qubit Pauli density expression. -/
noncomputable def normalisedBipartitePauliSum {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  ((2 : ℂ) ^ (n + m))⁻¹ • bipartitePauliSum terms left right

/-- A finite sum of signed bipartite Pauli tensor terms. -/
noncomputable def signedBipartitePauliSum {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  ∑ g ∈ terms, signedBipartitePauliTerm (negative g) (left g) (right g)

/-- A finite sum of signed Pauli terms on a finite left subsystem. -/
noncomputable def signedPauliSum {γ : Type*} {n : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (labels : γ → Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ∑ g ∈ terms, signedPauliTerm (negative g) (labels g)

/-- The normalization used by a finite signed-Pauli density expression. -/
noncomputable def normalisedSignedPauliSum {γ : Type*} {n : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (labels : γ → Fin n → PauliLabel) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  ((2 : ℂ) ^ n)⁻¹ • signedPauliSum terms negative labels

/-- The normalization used by a bipartite finite signed-Pauli density expression. -/
noncomputable def normalisedSignedBipartitePauliSum {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    Matrix (QubitIndex n × QubitIndex m) (QubitIndex n × QubitIndex m) ℂ :=
  ((2 : ℂ) ^ (n + m))⁻¹ • signedBipartitePauliSum terms negative left right

/-- The finite partial trace retains exactly the terms trivial on the discarded qubits. -/
theorem partialTraceRight_bipartitePauliSum
    {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    partialTraceRight (bipartitePauliSum terms left right) =
      (2 : ℂ) ^ m •
        ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
          pauliStringMatrix (left g) := by
  classical
  rw [bipartitePauliSum, map_sum]
  calc
    ∑ g ∈ terms, partialTraceRight (bipartitePauliTerm (left g) (right g)) =
        ∑ g ∈ terms,
          if IsIdentityPauliString (right g) then
            (2 : ℂ) ^ m • pauliStringMatrix (left g)
          else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [partialTraceRight_bipartitePauliTerm]
    _ = ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
          (2 : ℂ) ^ m • pauliStringMatrix (left g) := by
      simp only [Finset.sum_filter]
    _ = (2 : ℂ) ^ m •
        ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
          pauliStringMatrix (left g) := by
      rw [Finset.smul_sum]

/-- The normalized Pauli expression is preserved by partial trace. -/
theorem partialTraceRight_normalisedBipartitePauliSum
    {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    partialTraceRight (normalisedBipartitePauliSum terms left right) =
      normalisedPauliSum
        (terms.filter (fun g => IsIdentityPauliString (right g))) left := by
  rw [normalisedBipartitePauliSum, map_smul,
    partialTraceRight_bipartitePauliSum, normalisedPauliSum, pauliSum]
  rw [smul_smul]
  congr 1
  rw [pow_add]
  field_simp

/-- Partial trace retains exactly the signed terms trivial on the discarded qubits. -/
theorem partialTraceRight_signedBipartitePauliSum
    {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    partialTraceRight (signedBipartitePauliSum terms negative left right) =
      (2 : ℂ) ^ m •
        ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
          signedPauliTerm (negative g) (left g) := by
  classical
  rw [signedBipartitePauliSum, map_sum]
  calc
    ∑ g ∈ terms,
        partialTraceRight (signedBipartitePauliTerm (negative g) (left g) (right g)) =
      ∑ g ∈ terms,
        if IsIdentityPauliString (right g) then
          (2 : ℂ) ^ m • signedPauliTerm (negative g) (left g)
        else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [partialTraceRight_signedBipartitePauliTerm]
    _ = ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
        (2 : ℂ) ^ m • signedPauliTerm (negative g) (left g) := by
      simp only [Finset.sum_filter]
    _ = (2 : ℂ) ^ m •
        ∑ g ∈ terms.filter (fun g => IsIdentityPauliString (right g)),
          signedPauliTerm (negative g) (left g) := by
      rw [Finset.smul_sum]

/-- The normalized signed-Pauli expression is preserved by partial trace. -/
theorem partialTraceRight_normalisedSignedBipartitePauliSum
    {γ : Type*} {n m : ℕ}
    (terms : Finset γ) (negative : γ → Bool)
    (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel) :
    partialTraceRight (normalisedSignedBipartitePauliSum terms negative left right) =
      normalisedSignedPauliSum
        (terms.filter (fun g => IsIdentityPauliString (right g))) negative left := by
  rw [normalisedSignedBipartitePauliSum, map_smul,
    partialTraceRight_signedBipartitePauliSum, normalisedSignedPauliSum,
    signedPauliSum]
  rw [smul_smul]
  congr 1
  rw [pow_add]
  field_simp

/--
If the surviving large-region terms are exactly the small-region terms,
partial trace gives the small normalized signed-Pauli expression.

The equality hypothesis is deliberately explicit: it is the formal version of
the survivor portion of the manuscript's local-group restriction claim, rather
than an inference from Pauli tracelessness alone.  It does not make arbitrary
term families into stabilizer groups or density matrices.
-/
theorem partialTraceRight_normalisedSignedBipartitePauliSum_eq_of_survivors
    {γ : Type*} {n m : ℕ}
    (largeTerms smallTerms : Finset γ) (negative : γ → Bool)
    (left : γ → Fin n → PauliLabel)
    (right : γ → Fin m → PauliLabel)
    (hsurvivors :
      largeTerms.filter (fun g => IsIdentityPauliString (right g)) = smallTerms) :
    partialTraceRight
      (normalisedSignedBipartitePauliSum largeTerms negative left right) =
      normalisedSignedPauliSum smallTerms negative left := by
  rw [partialTraceRight_normalisedSignedBipartitePauliSum, hsurvivors]

end FiniteFiber
