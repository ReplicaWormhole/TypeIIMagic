import Formalization.AlgebraicStarDirectLimit
import Formalization.TensorMatrixEquiv

/-!
# The algebraic dyadic tensor tower

This file constructs the finite stages of the infinite tracial qubit product
as a genuine directed system.  It is deliberately algebraic: its direct limit
is the UHF *-algebra before C-star completion and weak closure.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

/-- One qubit's full matrix algebra. -/
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Finite qubit algebras in iterated matrix-amplification form.  The preceding
`matrixTensorStarAlgEquiv` identifies each successor with the corresponding
algebraic tensor product `M₂(ℂ) ⊗ QubitTensorPower n`. -/
def QubitTensorPower : ℕ → Type
  | 0 => ℂ
  | n + 1 => Matrix (Fin 2) (Fin 2) (QubitTensorPower n)

/-- The algebraic structure carried by each finite matrix stage. -/
structure QubitTensorPowerData (A : Type) where
  semiring : Semiring A
  starRing : StarRing A
  algebra : Algebra ℂ A
  starModule : StarModule ℂ A

noncomputable def qubitTensorPowerData : (n : ℕ) → QubitTensorPowerData (QubitTensorPower n)
  | 0 => by
    change QubitTensorPowerData ℂ
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  | n + 1 => by
    change QubitTensorPowerData (Matrix (Fin 2) (Fin 2) (QubitTensorPower n))
    let data := qubitTensorPowerData n
    letI : Semiring (QubitTensorPower n) := data.semiring
    letI : StarRing (QubitTensorPower n) := data.starRing
    letI : Algebra ℂ (QubitTensorPower n) := data.algebra
    letI : StarModule ℂ (QubitTensorPower n) := data.starModule
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

noncomputable instance qubitTensorPowerSemiring (n : ℕ) : Semiring (QubitTensorPower n) :=
  (qubitTensorPowerData n).semiring

noncomputable instance qubitTensorPowerStarRing (n : ℕ) : StarRing (QubitTensorPower n) :=
  (qubitTensorPowerData n).starRing

noncomputable instance qubitTensorPowerAlgebra (n : ℕ) : Algebra ℂ (QubitTensorPower n) :=
  (qubitTensorPowerData n).algebra

noncomputable instance qubitTensorPowerStarModule (n : ℕ) : StarModule ℂ (QubitTensorPower n) :=
  (qubitTensorPowerData n).starModule

/-- Adjoin one qubit on the left by taking the diagonal matrix with the old
observable in each block.  Under `matrixTensorStarAlgEquiv`, this is
`1₂ ⊗ x`. -/
noncomputable def qubitTensorPowerSuccEmbedding (n : ℕ) :
    QubitTensorPower n →⋆ₐ[ℂ] QubitTensorPower (n + 1) :=
  { Matrix.scalarAlgHom (Fin 2) ℂ with
    map_star' := by
      intro x
      change Matrix.scalar (Fin 2) (star x) = star (Matrix.scalar (Fin 2) x)
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.scalar_apply, Matrix.star_apply]
      · have h' : j ≠ i := Ne.symm h
        simp [Matrix.scalar_apply, Matrix.star_apply, h, h'] }

/-- The unique normalized trace on the zero-qubit algebra `ℂ`. -/
noncomputable def scalarTrace : ℂ →ₗ[ℂ] ℂ := LinearMap.id

/-- The scalar trace is an algebraic tracial state. -/
theorem scalarTrace_isAlgebraicTracialState :
    IsAlgebraicTracialState scalarTrace := by
  refine
    { toIsAlgebraicState :=
        { map_one := by rfl
          positive := ?_ }
      cyclic := ?_ }
  · intro z
    refine ⟨Complex.normSq z, Complex.normSq_nonneg z, ?_⟩
    change star z * z = (Complex.normSq z : ℂ)
    exact Complex.normSq_eq_conj_mul_self.symm
  · intro x y
    exact mul_comm x y

/-- The normalized trace on the finite algebra of `n` qubits. -/
noncomputable def qubitTensorTrace : (n : ℕ) → QubitTensorPower n →ₗ[ℂ] ℂ
  | 0 => scalarTrace
  | n + 1 => normalizedMatrixTraceOver (Fin 2) (qubitTensorTrace n)

/-- Every finite qubit tensor power carries its normalized algebraic tracial
state. -/
theorem qubitTensorTrace_isAlgebraicTracialState (n : ℕ) :
    IsAlgebraicTracialState (qubitTensorTrace n) := by
  induction n with
  | zero => exact scalarTrace_isAlgebraicTracialState
  | succ n hn =>
    exact normalizedMatrixTraceOver_isAlgebraicTracialState (Fin 2)
      (qubitTensorTrace n) hn

/-- Adjoining an identity qubit preserves the normalized finite-stage trace. -/
theorem qubitTensorTrace_succ_embedding (n : ℕ) (x : QubitTensorPower n) :
    qubitTensorTrace (n + 1) (qubitTensorPowerSuccEmbedding n x) =
      qubitTensorTrace n x := by
  change normalizedMatrixTraceOver (Fin 2) (qubitTensorTrace n)
      (Matrix.scalar (Fin 2) x) = qubitTensorTrace n x
  rw [normalizedMatrixTraceOver_apply]
  simp [Matrix.scalar_apply]

/-- The canonical inclusion from a finite qubit stage into a later one.  It is
the iterated operation of adjoining identity qubits on the left. -/
noncomputable def qubitTensorPowerMap (n m : ℕ) (h : n ≤ m) :
    QubitTensorPower n →⋆ₐ[ℂ] QubitTensorPower m :=
  Nat.leRecOn h
    (fun {k} g => (qubitTensorPowerSuccEmbedding k).comp g)
    (StarAlgHom.id ℂ (QubitTensorPower n))

/-- The canonical inclusion from a finite qubit stage to itself is the
identity. -/
theorem qubitTensorPowerMap_self (n : ℕ) :
    qubitTensorPowerMap n n (Nat.le_refl n) = StarAlgHom.id ℂ (QubitTensorPower n) := by
  change Nat.leRecOn (C := fun m => QubitTensorPower n →⋆ₐ[ℂ] QubitTensorPower m)
      (Nat.le_refl n) (fun {k} g => (qubitTensorPowerSuccEmbedding k).comp g)
      (StarAlgHom.id ℂ (QubitTensorPower n)) = StarAlgHom.id ℂ (QubitTensorPower n)
  exact Nat.leRecOn_self _

/-- Iterated inclusion by one more qubit is the successor inclusion after the
previous iterated inclusion. -/
theorem qubitTensorPowerMap_succ (n m : ℕ) (h : n ≤ m) :
    qubitTensorPowerMap n (m + 1) (Nat.le_succ_of_le h) =
      (qubitTensorPowerSuccEmbedding m).comp (qubitTensorPowerMap n m h) := by
  change Nat.leRecOn (C := fun k => QubitTensorPower n →⋆ₐ[ℂ] QubitTensorPower k)
      (Nat.le_succ_of_le h) (fun {k} g => (qubitTensorPowerSuccEmbedding k).comp g)
      (StarAlgHom.id ℂ (QubitTensorPower n)) = _
  simpa [qubitTensorPowerMap] using
    (Nat.leRecOn_succ (C := fun k => QubitTensorPower n →⋆ₐ[ℂ] QubitTensorPower k)
      (next := fun {k} g => (qubitTensorPowerSuccEmbedding k).comp g) h
      (StarAlgHom.id ℂ (QubitTensorPower n)))

/-- The canonical finite-stage inclusions compose. -/
theorem qubitTensorPowerMap_comp (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    qubitTensorPowerMap n k (Nat.le_trans hnm hmk) =
      (qubitTensorPowerMap m k hmk).comp (qubitTensorPowerMap n m hnm) := by
  induction k, hmk using Nat.le_induction with
  | base =>
    rw [qubitTensorPowerMap_self]
    exact StarAlgHom.id_comp _
  | succ k hmk ih =>
    rw [qubitTensorPowerMap_succ n k (Nat.le_trans hnm hmk),
      qubitTensorPowerMap_succ m k hmk, ih, StarAlgHom.comp_assoc]

/-- The finite-stage normalized traces are compatible with every canonical
inclusion, not only with the one-step embedding. -/
theorem qubitTensorTrace_map (n m : ℕ) (h : n ≤ m) (x : QubitTensorPower n) :
    qubitTensorTrace m (qubitTensorPowerMap n m h x) = qubitTensorTrace n x := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [qubitTensorPowerMap_self]
    rfl
  | succ m h ih =>
    rw [qubitTensorPowerMap_succ n m h, StarAlgHom.comp_apply,
      qubitTensorTrace_succ_embedding]
    exact ih

/-- The finite qubit stages and their canonical inclusions form a directed
star-algebraic system. -/
noncomputable instance qubitTensorPowerDirectedSystem :
    DirectedSystem QubitTensorPower (qubitTensorPowerMap · · ·) where
  map_self := by
    intro n x
    change qubitTensorPowerMap n n (Nat.le_refl n) x = x
    rw [qubitTensorPowerMap_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    change qubitTensorPowerMap j k hjk (qubitTensorPowerMap i j hij x) =
      qubitTensorPowerMap i k (Nat.le_trans hij hjk) x
    rw [qubitTensorPowerMap_comp i j k hij hjk]
    rfl

/-- The algebraic infinite qubit product: the directed limit of all finite
qubit matrix algebras, before any norm or weak-operator completion. -/
noncomputable abbrev QubitUHFAlgebra : Type :=
  DirectLimit QubitTensorPower qubitTensorPowerMap

/-- The compatible finite-stage traces induce a trace on the algebraic UHF
direct limit. -/
noncomputable def qubitUHFTrace : QubitUHFAlgebra →ₗ[ℂ] ℂ :=
  algebraicLimitTrace qubitTensorTrace qubitTensorTrace_map

/-- Composed with each canonical stage map, the infinite-product trace is the
prescribed normalized trace on that finite qubit stage. -/
theorem qubitUHFTrace_of (n : ℕ) (x : QubitTensorPower n) :
    qubitUHFTrace
      (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
      qubitTensorTrace n x :=
  algebraicLimitTrace_of qubitTensorTrace qubitTensorTrace_map n x

/-- The algebraic infinite qubit product carries the normalized tracial state
induced from its finite tensor-product stages. -/
theorem qubitUHFTrace_isAlgebraicTracialState :
    IsAlgebraicTracialState qubitUHFTrace :=
  algebraicLimitTrace_isAlgebraicTracialState qubitTensorTrace
    qubitTensorTrace_map qubitTensorTrace_isAlgebraicTracialState

end StabilizerHyperfinite
