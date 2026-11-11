import FiniteFiber.FinitePauliGNS
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Finite tensor-matrix embeddings

The manuscript identifies a smaller finite qubit algebra with the tensor
factor `A ⊗ 1` inside a larger finite algebra.  This file constructs that
embedding for the package's recursive `QubitIndex` basis.  It gives a
recursive coordinate equivalence

`QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m`

and then transports the Kronecker embedding through it.  The result is a
unital star-algebra homomorphism, injective and norm preserving for the
operator-norm C-star structures already used by the finite GNS layer.

The concrete `qubitIndexAppendEquiv` below recurses on the added block.  With
the present recursive `QubitIndex` convention, it regards the retained block
as the tail tensor factor; it is not yet proved to agree with a physical
initial-segment split of the `Fin n` labels used by `pauliStringMatrix`.
Accordingly, the coordinate-independent statements in this file may be used
with an explicitly supplied local coordinate equivalence, whereas the
specialized `embedRight` is only a recursive-basis convention until that
separate lattice-coordinate bridge is constructed.

This is the finite-algebra part of the eventual quasilocal inductive system.
It does not yet prove compatibility of different successive embeddings, build
the norm-closed quasilocal algebra, or construct the compatible state.
-/

namespace FiniteFiber

open scoped BigOperators Kronecker TensorProduct
open scoped FiniteFiber.FiniteQubitMatrix

/-- The recursive qubit basis is nonempty at every finite volume. -/
def qubitIndexNonempty : ∀ n : ℕ, Nonempty (QubitIndex n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 =>
      let ⟨x⟩ := qubitIndexNonempty n
      ⟨(0, x)⟩

/--
The recursive tail-block tensor-coordinate equivalence for the recursive
qubit basis.  The recursion is on the added block, so `QubitIndex n` appears
as the tail factor in the raw recursive coordinates.  This is an algebraic
coordinate convention, not yet the manuscript's `Fin n` initial-segment
identification.
-/
def qubitIndexAppendEquiv (n : ℕ) : (m : ℕ) →
    QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m
  | 0 =>
      { toFun := fun x => (x, PUnit.unit)
        invFun := fun x => x.1
        left_inv := by
          intro x
          rfl
        right_inv := by
          intro x
          cases x.2
          rfl }
  | m + 1 =>
      let e := qubitIndexAppendEquiv n m
      { toFun := fun x =>
          let y := e x.2
          (y.1, (x.1, y.2))
        invFun := fun x =>
          (x.2.1, e.symm (x.1, x.2.2))
        left_inv := by
          intro x
          rcases x with ⟨i, x⟩
          change (i, e.symm (e x)) = (i, x)
          rw [e.symm_apply_apply]
        right_inv := by
          intro x
          rcases x with ⟨y, ⟨i, z⟩⟩
          change ((e (e.symm (y, z))).1, (i, (e (e.symm (y, z))).2)) =
            (y, (i, z))
          rw [e.apply_symm_apply] }

/--
The recursive qubit basis written as a function on the usual `Fin n` site
labels.  Coordinate zero is the outer recursive factor and successor labels
belong to the recursive tail.
-/
def qubitIndexFinEquiv : ∀ n : ℕ, QubitIndex n ≃ (Fin n → Fin 2)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro f
          funext i
          exact Fin.elim0 i }
  | n + 1 =>
      let e := qubitIndexFinEquiv n
      { toFun := fun x i => Fin.cases x.1 (fun j => e x.2 j) i
        invFun := fun f => (f 0, e.symm (fun j => f j.succ))
        left_inv := by
          intro x
          rcases x with ⟨a, b⟩
          apply Prod.ext
          · rfl
          · apply e.injective
            rw [e.apply_symm_apply]
            funext j
            simp
        right_inv := by
          intro f
          funext i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            change e (e.symm (fun j => f j.succ)) j = f j.succ
            rw [e.apply_symm_apply] }

/-- Splitting a finite bit-string into its initial `n` and final `m` coordinates. -/
def finFunctionAppendEquiv (n m : ℕ) :
    (Fin (n + m) → Fin 2) ≃ (Fin n → Fin 2) × (Fin m → Fin 2) :=
  { toFun := fun f =>
      (fun i => f (Fin.castAdd m i), fun j => f (Fin.natAdd n j))
    invFun := fun f => Fin.addCases f.1 f.2
    left_inv := by
      intro f
      exact Fin.addCases_castAdd_natAdd f
    right_inv := by
      intro f
      rcases f with ⟨u, v⟩
      apply Prod.ext
      · funext i
        change Fin.addCases u v (Fin.castAdd m i) = u i
        exact Fin.addCases_left i
      · funext j
        change Fin.addCases u v (Fin.natAdd n j) = v j
        exact Fin.addCases_right j }

/--
The tensor-coordinate equivalence matching the usual `Fin (n + m)` split:
the first component is the initial `Fin n` block and the second is the final
`Fin m` block.  Unlike `qubitIndexAppendEquiv`, this equivalence is explicitly
aligned with the site-label convention of `pauliStringMatrix`.
-/
noncomputable def qubitIndexInitialSegmentEquiv (n m : ℕ) :
    QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m :=
  (qubitIndexFinEquiv (n + m)).trans
    ((finFunctionAppendEquiv n m).trans
      (Equiv.prodCongr (qubitIndexFinEquiv n).symm (qubitIndexFinEquiv m).symm))

/-- The first initial-segment coordinate is restriction to `Fin.castAdd m`. -/
theorem qubitIndexInitialSegmentEquiv_left (n m : ℕ) (x : QubitIndex (n + m)) :
    qubitIndexFinEquiv n (qubitIndexInitialSegmentEquiv n m x).1 =
      fun i => qubitIndexFinEquiv (n + m) x (Fin.castAdd m i) := by
  simp [qubitIndexInitialSegmentEquiv, finFunctionAppendEquiv, Equiv.trans_apply]

/-- The second initial-segment coordinate is restriction to `Fin.natAdd n`. -/
theorem qubitIndexInitialSegmentEquiv_right (n m : ℕ) (x : QubitIndex (n + m)) :
    qubitIndexFinEquiv m (qubitIndexInitialSegmentEquiv n m x).2 =
      fun j => qubitIndexFinEquiv (n + m) x (Fin.natAdd n j) := by
  simp [qubitIndexInitialSegmentEquiv, finFunctionAppendEquiv, Equiv.trans_apply]

/--
The matrix entry of a finite Pauli string is the product of the one-site
entries evaluated in the literal `Fin n` coordinate order.  This connects the
recursive definition of `pauliStringMatrix` with the physical site labels.
-/
theorem pauliStringMatrix_apply_qubitIndexFinEquiv : ∀ {n : ℕ}
    (a : Fin n → PauliLabel) (x y : QubitIndex n),
    pauliStringMatrix a x y = ∏ i : Fin n,
      PauliLabel.matrix (a i) (qubitIndexFinEquiv n x i)
        (qubitIndexFinEquiv n y i) := by
  intro n
  induction n with
  | zero =>
      intro a x y
      cases x
      cases y
      simp [pauliStringMatrix, qubitIndexFinEquiv]
  | succ n ih =>
      intro a x y
      rcases x with ⟨x₀, x'⟩
      rcases y with ⟨y₀, y'⟩
      rw [pauliStringMatrix]
      rw [Matrix.kronecker_apply]
      rw [ih (fun i => a i.succ) x' y']
      rw [Fin.prod_univ_succ]
      rfl

/--
Inverting the physical initial-segment coordinate equivalence concatenates
the two bit strings in `Fin n` then `Fin m` order.
-/
theorem qubitIndexInitialSegmentEquiv_symm_finCoordinates (n m : ℕ)
    (u : QubitIndex n) (v : QubitIndex m) :
    qubitIndexFinEquiv (n + m)
      ((qubitIndexInitialSegmentEquiv n m).symm (u, v)) =
        Fin.addCases (qubitIndexFinEquiv n u) (qubitIndexFinEquiv m v) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    have h := congrFun (qubitIndexInitialSegmentEquiv_left n m
      ((qubitIndexInitialSegmentEquiv n m).symm (u, v))) i
    simpa using h.symm
  · intro j
    have h := congrFun (qubitIndexInitialSegmentEquiv_right n m
      ((qubitIndexInitialSegmentEquiv n m).symm (u, v))) j
    simpa using h.symm

/--
An actual finite Pauli string factorizes under the physical initial/final
coordinate split.  This is the matrix-level locality bridge absent from the
raw recursive tail-coordinate convention.
-/
theorem pauliStringMatrix_reindex_initialSegment (n m : ℕ)
    (a : Fin (n + m) → PauliLabel) :
    Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
      (qubitIndexInitialSegmentEquiv n m) (pauliStringMatrix a) =
      pauliStringMatrix (fun i : Fin n => a (Fin.castAdd m i)) ⊗ₖ
        pauliStringMatrix (fun j : Fin m => a (Fin.natAdd n j)) := by
  ext u v
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rw [Matrix.reindex_apply]
  change pauliStringMatrix a
      ((qubitIndexInitialSegmentEquiv n m).symm (u₁, u₂))
      ((qubitIndexInitialSegmentEquiv n m).symm (v₁, v₂)) = _
  rw [pauliStringMatrix_apply_qubitIndexFinEquiv]
  rw [Fin.prod_univ_add]
  rw [qubitIndexInitialSegmentEquiv_symm_finCoordinates,
    qubitIndexInitialSegmentEquiv_symm_finCoordinates]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← pauliStringMatrix_apply_qubitIndexFinEquiv]
  rw [← pauliStringMatrix_apply_qubitIndexFinEquiv]
  rw [Matrix.kronecker_apply]

/--
The same physical factorization holds for the signed Hermitian Pauli terms
used by finite stabilizer data.
-/
theorem signedPauliStringMatrix_reindex_initialSegment (n m : ℕ)
    (negative : Bool) (a : Fin (n + m) → PauliLabel) :
    Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
      (qubitIndexInitialSegmentEquiv n m) (signedPauliStringMatrix negative a) =
      signedBipartitePauliTerm negative
        (fun i : Fin n => a (Fin.castAdd m i))
        (fun j : Fin m => a (Fin.natAdd n j)) := by
  cases negative with
  | false =>
      change Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
        (qubitIndexInitialSegmentEquiv n m) (pauliStringMatrix a) = _
      rw [pauliStringMatrix_reindex_initialSegment]
      simp [signedBipartitePauliTerm, bipartitePauliTerm, pauliSign]
  | true =>
      change Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
        (qubitIndexInitialSegmentEquiv n m) (-pauliStringMatrix a) = _
      change -(Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
        (qubitIndexInitialSegmentEquiv n m) (pauliStringMatrix a)) = _
      rw [pauliStringMatrix_reindex_initialSegment]
      simp [signedBipartitePauliTerm, bipartitePauliTerm, pauliSign]

/-- The left tensor-factor inclusion into an algebraic tensor product is star preserving. -/
noncomputable def tensorIncludeLeftStarAlgHom (A B : Type*)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    Matrix A A ℂ →⋆ₐ[ℂ] Matrix A A ℂ ⊗[ℂ] Matrix B B ℂ :=
  StarAlgHom.mk Algebra.TensorProduct.includeLeft (by
    intro a
    simp [Algebra.TensorProduct.includeLeft_apply])

/-- The raw Kronecker embedding `a ↦ a ⊗ 1` as a star-algebra homomorphism. -/
noncomputable def kroneckerRightStarAlgHom (A B : Type*)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    Matrix A A ℂ →⋆ₐ[ℂ] Matrix (A × B) (A × B) ℂ :=
  (StarAlgHomClass.toStarAlgHom (Matrix.kroneckerStarAlgEquiv A B ℂ)).comp
    (tensorIncludeLeftStarAlgHom A B)

/-- The raw right-tensor-factor embedding is injective whenever the right index is nonempty. -/
theorem kroneckerRightStarAlgHom_injective (A B : Type*)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B] :
    Function.Injective (kroneckerRightStarAlgHom A B) := by
  intro a b hab
  change a ⊗ₖ (1 : Matrix B B ℂ) = b ⊗ₖ (1 : Matrix B B ℂ) at hab
  ext i j
  let k : B := Classical.arbitrary B
  have hentry := congrFun (congrFun hab (i, k)) (j, k)
  simpa [Matrix.kronecker_apply] using hentry

/-- Reindexing square matrices along an equivalence is a star-algebra equivalence. -/
noncomputable def reindexMatrixStarAlgEquiv (A B : Type*)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B) :
    Matrix A A ℂ ≃⋆ₐ[ℂ] Matrix B B ℂ :=
  CStarMatrix.reindexₐ ℂ ℂ e

/--
The right-tensor inclusion transported through an explicitly supplied finite
coordinate factorization.  This is the coordinate-independent form used when
a local lattice region is identified with a retained and discarded block.
-/
noncomputable def coordinateEmbedRight (I J K : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (e : K ≃ I × J) :
    Matrix I I ℂ →⋆ₐ[ℂ] Matrix K K ℂ :=
  (StarAlgHomClass.toStarAlgHom (reindexMatrixStarAlgEquiv _ _ e.symm)).comp
    (kroneckerRightStarAlgHom _ _)

/-- The coordinate inclusion is literally the reindexed Kronecker inclusion. -/
theorem coordinateEmbedRight_apply (I J K : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (e : K ≃ I × J)
    (a : Matrix I I ℂ) :
    coordinateEmbedRight I J K e a =
      Matrix.reindex e.symm e.symm (a ⊗ₖ (1 : Matrix J J ℂ)) :=
  rfl

/-- An explicit coordinate inclusion is injective when the discarded factor is nonempty. -/
theorem coordinateEmbedRight_injective (I J K : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty J] (e : K ≃ I × J) :
    Function.Injective (coordinateEmbedRight I J K e) := by
  intro a b hab
  apply kroneckerRightStarAlgHom_injective I J
  apply (reindexMatrixStarAlgEquiv _ _ e.symm).injective
  exact hab

/--
The tensor inclusion for the literal initial/final `Fin`-label split of a
finite qubit block.  It is the physical-coordinate alternative to the
recursive tail-block convention `embedRight`.
-/
noncomputable def embedInitialSegment (n m : ℕ) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ]
      Matrix (QubitIndex (n + m)) (QubitIndex (n + m)) ℂ :=
  coordinateEmbedRight (QubitIndex n) (QubitIndex m) (QubitIndex (n + m))
    (qubitIndexInitialSegmentEquiv n m)

/-- The initial-segment inclusion is a reindexed `a tensor 1` in its explicit coordinates. -/
theorem embedInitialSegment_apply (n m : ℕ) (a : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    embedInitialSegment n m a =
      Matrix.reindex (qubitIndexInitialSegmentEquiv n m).symm
        (qubitIndexInitialSegmentEquiv n m).symm
        (a ⊗ₖ (1 : Matrix (QubitIndex m) (QubitIndex m) ℂ)) :=
  coordinateEmbedRight_apply _ _ _ _ _

/-- Extend an ordered Pauli label string by identity labels on a final block. -/
def appendIdentityPauliLabels {n : ℕ} (m : ℕ) (a : Fin n → PauliLabel) :
    Fin (n + m) → PauliLabel :=
  Fin.addCases (motive := fun _ => PauliLabel) a (fun _ => PauliLabel.I)

/-- Extending a label string by an empty block does nothing. -/
theorem appendIdentityPauliLabels_zero (n : ℕ) (a : Fin n → PauliLabel) :
    appendIdentityPauliLabels 0 a = a := by
  funext i
  exact Fin.addCases_left (m := n) (n := 0) (motive := fun _ => PauliLabel)
    (left := a) (right := fun _ : Fin 0 => PauliLabel.I) i

/--
An already identity-padded string agrees with the restriction of its padding
by one further final site.
-/
theorem appendIdentityPauliLabels_castAdd (n m : ℕ) (a : Fin n → PauliLabel)
    (j : Fin (n + m)) :
    appendIdentityPauliLabels m a j =
      appendIdentityPauliLabels (m + 1) a (Fin.castAdd 1 j) := by
  unfold appendIdentityPauliLabels
  apply Fin.addCases (m := n) (n := m)
    (motive := fun j =>
      Fin.addCases (motive := fun _ => PauliLabel) a
          (fun _ : Fin m => PauliLabel.I) j =
        Fin.addCases (motive := fun _ => PauliLabel) a
          (fun _ : Fin (m + 1) => PauliLabel.I) (Fin.castAdd 1 j))
  · intro i
    rw [show Fin.castAdd 1 (Fin.castAdd m i) = Fin.castAdd (m + 1) i by
      simpa using (Fin.castAdd_castAdd (n := m) (p := 1) i)]
    simp only [Fin.addCases_left]
  · intro i
    rw [show Fin.castAdd 1 (Fin.natAdd n i) = Fin.natAdd n (Fin.castAdd 1 i) by
      simpa using (Fin.natAdd_castAdd 1 n i).symm]
    simp only [Fin.addCases_right]

/--
Embedding a Pauli string into a larger physical initial segment extends its
site-label function by the identity Pauli on the newly added final block.
This gives the exact finite-volume operator-locality statement for these
Hermitian Pauli strings; it does not by itself construct a global Pauli group
or a quasilocal completion.
-/
theorem embedInitialSegment_pauliString (n m : ℕ)
    (a : Fin n → PauliLabel) :
    embedInitialSegment n m (pauliStringMatrix a) =
      pauliStringMatrix (Fin.addCases a (fun _ => PauliLabel.I)) := by
  rw [embedInitialSegment_apply]
  have h := pauliStringMatrix_reindex_initialSegment n m
    (Fin.addCases a (fun _ => PauliLabel.I))
  simp only [Fin.addCases_left, Fin.addCases_right] at h
  rw [pauliStringMatrix_all_I] at h
  have h' := congrArg
    (Matrix.reindex (qubitIndexInitialSegmentEquiv n m).symm
      (qubitIndexInitialSegmentEquiv n m).symm) h
  simpa using h'.symm

/-- The physical initial-segment embedding preserves the explicit Pauli sign. -/
theorem embedInitialSegment_signedPauliString (n m : ℕ)
    (negative : Bool) (a : Fin n → PauliLabel) :
    embedInitialSegment n m (signedPauliStringMatrix negative a) =
      signedPauliStringMatrix negative
        (Fin.addCases a (fun _ => PauliLabel.I)) := by
  cases negative <;>
    simp [signedPauliStringMatrix, embedInitialSegment_pauliString]

/-- The initial-segment tensor inclusion is injective. -/
theorem embedInitialSegment_injective (n m : ℕ) :
    Function.Injective (embedInitialSegment n m) := by
  letI : Nonempty (QubitIndex m) := qubitIndexNonempty m
  exact coordinateEmbedRight_injective (QubitIndex n) (QubitIndex m)
    (QubitIndex (n + m)) (qubitIndexInitialSegmentEquiv n m)

/--
The recursive-basis tensor inclusion from an `n`-qubit tail block into an
`n + m`-qubit block.  The physical `Fin` initial-segment convention is instead
provided by `embedInitialSegment`.  A further Pauli-string tensor-factorization
and operator-locality bridge remains to be proved.
-/
noncomputable def embedRight (n m : ℕ) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ]
      Matrix (QubitIndex (n + m)) (QubitIndex (n + m)) ℂ :=
  (StarAlgHomClass.toStarAlgHom
    (reindexMatrixStarAlgEquiv _ _ (qubitIndexAppendEquiv n m).symm)).comp
    (kroneckerRightStarAlgHom _ _)

/-- The recursive-basis embedding is literally a reindexed `a ⊗ 1`. -/
theorem embedRight_apply (n m : ℕ) (a : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    embedRight n m a =
      Matrix.reindex (qubitIndexAppendEquiv n m).symm
        (qubitIndexAppendEquiv n m).symm
        (a ⊗ₖ (1 : Matrix (QubitIndex m) (QubitIndex m) ℂ)) :=
  rfl

/-- The recursive-basis tensor embedding is injective. -/
theorem embedRight_injective (n m : ℕ) : Function.Injective (embedRight n m) := by
  letI : Nonempty (QubitIndex m) := qubitIndexNonempty m
  intro a b hab
  apply kroneckerRightStarAlgHom_injective (QubitIndex n) (QubitIndex m)
  apply (reindexMatrixStarAlgEquiv _ _ (qubitIndexAppendEquiv n m).symm).injective
  exact hab

/-- The recursive-basis tensor embedding preserves the operator norm. -/
theorem embedRight_norm (n m : ℕ) (a : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖embedRight n m a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (embedRight n m) (embedRight_injective n m) a

/-- Every qubit-coordinate tensor inclusion is isometric for the matrix operator norm. -/
theorem coordinateEmbedRight_qubit_norm (n m : ℕ)
    (e : QubitIndex (n + m) ≃ QubitIndex n × QubitIndex m)
    (a : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖coordinateEmbedRight (QubitIndex n) (QubitIndex m) (QubitIndex (n + m)) e a‖ =
      ‖a‖ := by
  letI : Nonempty (QubitIndex m) := qubitIndexNonempty m
  exact NonUnitalStarAlgHom.norm_map
    (coordinateEmbedRight (QubitIndex n) (QubitIndex m) (QubitIndex (n + m)) e)
    (coordinateEmbedRight_injective (QubitIndex n) (QubitIndex m)
      (QubitIndex (n + m)) e) a

/-- The initial-segment tensor inclusion preserves the operator norm. -/
theorem embedInitialSegment_norm (n m : ℕ)
    (a : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖embedInitialSegment n m a‖ = ‖a‖ := by
  exact coordinateEmbedRight_qubit_norm n m (qubitIndexInitialSegmentEquiv n m) a

/--
The finite-dimensional trace pairs a right-tensor inclusion with the right
partial trace.  This is the linear-algebraic identity needed to turn
compatible finite density matrices into compatible finite-volume states.
-/
theorem trace_mul_kronecker_one_eq_trace_partialTraceRight_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (R : Matrix (α × β) (α × β) ℂ) (A : Matrix α α ℂ) :
    (R * (A ⊗ₖ (1 : Matrix β β ℂ))).trace =
      (partialTraceRight R * A).trace := by
  classical
  change (∑ i : α × β, ∑ j : α × β,
      R i j * (A ⊗ₖ (1 : Matrix β β ℂ)) j i) =
    ∑ i : α, ∑ j : α, (∑ k : β, R (i, k) (j, k)) * A j i
  simp_rw [Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap, Matrix.one_apply, apply_ite, Matrix.of_apply,
    mul_one, mul_zero]
  simp_rw [Fintype.sum_ite_eq']
  calc
    ∑ x : α, ∑ k : β, ∑ j : α, R (x, k) (j, k) * A j x =
        ∑ x : α, ∑ j : α, ∑ k : β, R (x, k) (j, k) * A j x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i : α, ∑ j : α, (∑ k : β, R (i, k) (j, k)) * A j i := by
      simp_rw [← Finset.sum_mul]

/--
The trace/partial-trace identity transported through an arbitrary finite
coordinate factorization.  Unlike `embedRight`, this form applies directly to
the coordinate equivalence attached to nested local stabilizer data.
-/
theorem trace_mul_coordinateEmbedRight_eq_trace_partialTraceRight_reindex
    (I J K : Type*)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (e : K ≃ I × J)
    (R : Matrix K K ℂ) (A : Matrix I I ℂ) :
    (R * coordinateEmbedRight I J K e A).trace =
      (partialTraceRight (Matrix.reindex e e R) * A).trace := by
  have hembed :
      Matrix.reindex e e (coordinateEmbedRight I J K e A) =
        A ⊗ₖ (1 : Matrix J J ℂ) := by
    rw [coordinateEmbedRight_apply]
    ext i j
    simp [Matrix.reindex_apply]
  calc
    (R * coordinateEmbedRight I J K e A).trace =
        (Matrix.reindex e e (R * coordinateEmbedRight I J K e A)).trace := by
      symm
      exact trace_reindex e (R * coordinateEmbedRight I J K e A)
    _ = (Matrix.reindex e e R *
        Matrix.reindex e e (coordinateEmbedRight I J K e A)).trace := by
      congr 1
      simp
    _ = (partialTraceRight (Matrix.reindex e e R) * A).trace := by
      rw [hembed]
      exact trace_mul_kronecker_one_eq_trace_partialTraceRight_mul
        (Matrix.reindex e e R) A

/--
The trace/partial-trace relation for the literal initial/final `Fin`-label
split.  This is the finite-volume pairing identity to use once local lattice
regions are enumerated in that label order.
-/
theorem trace_mul_embedInitialSegment_eq_trace_partialTraceRight_reindex
    (n m : ℕ)
    (R : Matrix (QubitIndex (n + m)) (QubitIndex (n + m)) ℂ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    (R * embedInitialSegment n m A).trace =
      (partialTraceRight
        (Matrix.reindex (qubitIndexInitialSegmentEquiv n m)
          (qubitIndexInitialSegmentEquiv n m) R) * A).trace :=
  trace_mul_coordinateEmbedRight_eq_trace_partialTraceRight_reindex
    (QubitIndex n) (QubitIndex m) (QubitIndex (n + m))
    (qubitIndexInitialSegmentEquiv n m) R A

/--
After transporting the larger matrix to the recursive tail-block coordinates,
the trace pairing against `embedRight` is the pairing against the right
partial trace.  The coordinate-independent theorem above is the version used
for a manuscript region once its physical tensor coordinates are supplied.
-/
theorem trace_mul_embedRight_eq_trace_partialTraceRight_reindex
    (n m : ℕ)
    (R : Matrix (QubitIndex (n + m)) (QubitIndex (n + m)) ℂ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    (R * embedRight n m A).trace =
      (partialTraceRight
        (Matrix.reindex (qubitIndexAppendEquiv n m) (qubitIndexAppendEquiv n m) R) * A).trace := by
  let e := qubitIndexAppendEquiv n m
  have hembed :
      Matrix.reindex e e (embedRight n m A) =
        A ⊗ₖ (1 : Matrix (QubitIndex m) (QubitIndex m) ℂ) := by
    rw [embedRight_apply]
    ext i j
    simp [e, Matrix.reindex_apply]
  change (R * embedRight n m A).trace =
    (partialTraceRight (Matrix.reindex e e R) * A).trace
  calc
    (R * embedRight n m A).trace =
        (Matrix.reindex e e (R * embedRight n m A)).trace := by
      symm
      exact trace_reindex e (R * embedRight n m A)
    _ = (Matrix.reindex e e R * Matrix.reindex e e (embedRight n m A)).trace := by
      congr 1
      simp
    _ = (partialTraceRight (Matrix.reindex e e R) * A).trace := by
      rw [hembed]
      exact trace_mul_kronecker_one_eq_trace_partialTraceRight_mul
        (Matrix.reindex e e R) A

end FiniteFiber
