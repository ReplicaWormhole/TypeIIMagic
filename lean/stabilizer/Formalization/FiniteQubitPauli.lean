import Formalization.SingleQubitPauli
import Formalization.TensorMatrixEquiv

/-!
# Explicit finite-qubit Pauli word bases

The one-qubit word basis iterates through the matrix-tensor star equivalence
to give concrete Pauli word bases for every finite stage of the qubit tower.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

/-- Binary X/Z labels for a finite string of qubits. -/
def FiniteQubitPauliLabel : ℕ → Type
  | 0 => Fin 1
  | n + 1 => SingleQubitLabel × FiniteQubitPauliLabel n

/-- The finite Pauli labels form an additive group under componentwise binary
addition. -/
instance finiteQubitPauliLabelAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteQubitPauliLabel n) := by
  induction n with
  | zero =>
    change AddCommGroup (Fin 1)
    infer_instance
  | succ n ih =>
    change AddCommGroup (SingleQubitLabel × FiniteQubitPauliLabel n)
    infer_instance

/-- Embed a finite Pauli label after adjoining an identity qubit on the left. -/
noncomputable def finiteQubitPauliLabelSuccEmbedding (n : ℕ) :
    FiniteQubitPauliLabel n →+ FiniteQubitPauliLabel (n + 1) where
  toFun v := (0, v)
  map_zero' := by rfl
  map_add' v w := by rfl

/-- The ordered finite-qubit Pauli word at a stage of the dyadic tower. -/
noncomputable def finiteQubitPauliWord : (n : ℕ) →
    FiniteQubitPauliLabel n → QubitTensorPower n
  | 0 => fun _ => 1
  | n + 1 => fun label =>
      matrixTensorStarAlgEquiv (Fin 2)
        (singleQubitPauliWord label.1 ⊗ₜ[ℂ] finiteQubitPauliWord n label.2)

/-- The recursively accumulated multiplier of the ordered finite-qubit Pauli
word convention. -/
def finiteQubitPauliMultiplier : (n : ℕ) →
    FiniteQubitPauliLabel n → FiniteQubitPauliLabel n → ℂ
  | 0 => fun _ _ => 1
  | n + 1 => fun v w =>
      singleQubitMultiplier v.1 w.1 * finiteQubitPauliMultiplier n v.2 w.2

/-- The recursively accumulated involution multiplier of the ordered
finite-qubit Pauli word convention. -/
def finiteQubitPauliStarMultiplier : (n : ℕ) →
    FiniteQubitPauliLabel n → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun v =>
      singleQubitStarMultiplier v.1 * finiteQubitPauliStarMultiplier n v.2

/-- Under the canonical matrix-tensor equivalence, tensoring a finite-stage
word with the one-qubit identity is exactly the tower's scalar embedding. -/
theorem matrixTensorStarAlgEquiv_one_tmul (n : ℕ) (x : QubitTensorPower n) :
    matrixTensorStarAlgEquiv (Fin 2) ((1 : QubitMatrix) ⊗ₜ[ℂ] x) =
      Matrix.scalar (Fin 2) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixTensorStarAlgEquiv, matrixTensorAlgEquiv,
      Algebra.TensorProduct.comm_tmul, matrixEquivTensor_apply_symm,
      Matrix.scalar_apply]

/-- Adjoining an identity qubit carries a finite-stage Pauli word to the
word with a zero X/Z label on the new leftmost qubit. -/
theorem qubitTensorPowerSuccEmbedding_finiteQubitPauliWord
    (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitTensorPowerSuccEmbedding n (finiteQubitPauliWord n v) =
      finiteQubitPauliWord (n + 1) (finiteQubitPauliLabelSuccEmbedding n v) := by
  change Matrix.scalar (Fin 2) (finiteQubitPauliWord n v) =
    matrixTensorStarAlgEquiv (Fin 2)
      (singleQubitPauliWord (0, 0) ⊗ₜ[ℂ] finiteQubitPauliWord n v)
  rw [show singleQubitPauliWord (0, 0) = (1 : QubitMatrix) by
    simp [singleQubitPauliWord, pauliI_eq_one]]
  exact (matrixTensorStarAlgEquiv_one_tmul n (finiteQubitPauliWord n v)).symm

/-- The coherent label embedding from a finite qubit stage into any later
stage, obtained by repeatedly adding a zero leftmost label. -/
noncomputable def finiteQubitPauliLabelMap (n m : ℕ) (h : n ≤ m) :
    FiniteQubitPauliLabel n →+ FiniteQubitPauliLabel m :=
  Nat.leRecOn h
    (fun {k} g => (finiteQubitPauliLabelSuccEmbedding k).comp g)
    (AddMonoidHom.id (FiniteQubitPauliLabel n))

/-- The label inclusion at a fixed stage is the identity. -/
theorem finiteQubitPauliLabelMap_self (n : ℕ) :
    finiteQubitPauliLabelMap n n (Nat.le_refl n) =
      AddMonoidHom.id (FiniteQubitPauliLabel n) := by
  change Nat.leRecOn
      (C := fun m => FiniteQubitPauliLabel n →+ FiniteQubitPauliLabel m)
      (Nat.le_refl n) (fun {k} g => (finiteQubitPauliLabelSuccEmbedding k).comp g)
      (AddMonoidHom.id (FiniteQubitPauliLabel n)) = _
  exact Nat.leRecOn_self _

/-- Extending a coherent label inclusion by one stage adds one zero leftmost
label after the previous inclusion. -/
theorem finiteQubitPauliLabelMap_succ (n m : ℕ) (h : n ≤ m) :
    finiteQubitPauliLabelMap n (m + 1) (Nat.le_succ_of_le h) =
      (finiteQubitPauliLabelSuccEmbedding m).comp
        (finiteQubitPauliLabelMap n m h) := by
  change Nat.leRecOn
      (C := fun k => FiniteQubitPauliLabel n →+ FiniteQubitPauliLabel k)
      (Nat.le_succ_of_le h) (fun {k} g => (finiteQubitPauliLabelSuccEmbedding k).comp g)
      (AddMonoidHom.id (FiniteQubitPauliLabel n)) = _
  simpa [finiteQubitPauliLabelMap] using
    (Nat.leRecOn_succ
      (C := fun k => FiniteQubitPauliLabel n →+ FiniteQubitPauliLabel k)
      (next := fun {k} g => (finiteQubitPauliLabelSuccEmbedding k).comp g) h
      (AddMonoidHom.id (FiniteQubitPauliLabel n)))

/-- The canonical qubit-tower inclusion maps every finite Pauli word to its
coherently embedded later-stage Pauli word. -/
theorem qubitTensorPowerMap_finiteQubitPauliWord
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitTensorPowerMap n m h (finiteQubitPauliWord n v) =
      finiteQubitPauliWord m (finiteQubitPauliLabelMap n m h v) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [qubitTensorPowerMap_self, finiteQubitPauliLabelMap_self]
    rfl
  | succ m h ih =>
    rw [qubitTensorPowerMap_succ n m h, StarAlgHom.comp_apply, ih,
      finiteQubitPauliLabelMap_succ]
    exact qubitTensorPowerSuccEmbedding_finiteQubitPauliWord m
      (finiteQubitPauliLabelMap n m h v)

/-- The word multiplier is unchanged when zero labels are added at later
qubit stages. -/
theorem finiteQubitPauliMultiplier_map
    (n m : ℕ) (h : n ≤ m) (v w : FiniteQubitPauliLabel n) :
    finiteQubitPauliMultiplier m (finiteQubitPauliLabelMap n m h v)
      (finiteQubitPauliLabelMap n m h w) = finiteQubitPauliMultiplier n v w := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [finiteQubitPauliLabelMap_self]
    rfl
  | succ m h ih =>
    rw [finiteQubitPauliLabelMap_succ]
    change singleQubitMultiplier (0, 0) (0, 0) *
        finiteQubitPauliMultiplier m
          (finiteQubitPauliLabelMap n m h v)
          (finiteQubitPauliLabelMap n m h w) =
      finiteQubitPauliMultiplier n v w
    simp [singleQubitMultiplier, ih]

/-- The word involution multiplier is unchanged when zero labels are added at
later qubit stages. -/
theorem finiteQubitPauliStarMultiplier_map
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    finiteQubitPauliStarMultiplier m (finiteQubitPauliLabelMap n m h v) =
      finiteQubitPauliStarMultiplier n v := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [finiteQubitPauliLabelMap_self]
    rfl
  | succ m h ih =>
    rw [finiteQubitPauliLabelMap_succ]
    change singleQubitStarMultiplier (0, 0) *
        finiteQubitPauliStarMultiplier m
          (finiteQubitPauliLabelMap n m h v) =
      finiteQubitPauliStarMultiplier n v
    simp [singleQubitStarMultiplier, ih]

/-- The recursively defined finite-qubit words multiply with their stated
product multiplier. -/
theorem finiteQubitPauliWord_mul (n : ℕ) (v w : FiniteQubitPauliLabel n) :
    finiteQubitPauliWord n v * finiteQubitPauliWord n w =
      finiteQubitPauliMultiplier n v w • finiteQubitPauliWord n (v + w) := by
  induction n with
  | zero =>
    simp [finiteQubitPauliWord, finiteQubitPauliMultiplier]
  | succ n ih =>
    rcases v with ⟨a, v⟩
    rcases w with ⟨b, w⟩
    change
      matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v) *
        matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord b ⊗ₜ[ℂ] finiteQubitPauliWord n w) =
        (singleQubitMultiplier a b * finiteQubitPauliMultiplier n v w) •
          matrixTensorStarAlgEquiv (Fin 2)
            (singleQubitPauliWord (a + b) ⊗ₜ[ℂ]
              finiteQubitPauliWord n (v + w))
    calc
      matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v) *
        matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord b ⊗ₜ[ℂ] finiteQubitPauliWord n w) =
          matrixTensorStarAlgEquiv (Fin 2)
            ((singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v) *
              (singleQubitPauliWord b ⊗ₜ[ℂ] finiteQubitPauliWord n w)) :=
        (matrixTensorStarAlgEquiv (Fin 2)).map_mul _ _ |>.symm
      _ = matrixTensorStarAlgEquiv (Fin 2)
          ((singleQubitPauliWord a * singleQubitPauliWord b) ⊗ₜ[ℂ]
            (finiteQubitPauliWord n v * finiteQubitPauliWord n w)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]
      _ = matrixTensorStarAlgEquiv (Fin 2)
          ((singleQubitMultiplier a b • singleQubitPauliWord (a + b)) ⊗ₜ[ℂ]
            (finiteQubitPauliMultiplier n v w • finiteQubitPauliWord n (v + w))) := by
          rw [singleQubitPauliWord_mul, ih]
      _ = (singleQubitMultiplier a b * finiteQubitPauliMultiplier n v w) •
          matrixTensorStarAlgEquiv (Fin 2)
            (singleQubitPauliWord (a + b) ⊗ₜ[ℂ]
              finiteQubitPauliWord n (v + w)) := by
          rw [TensorProduct.smul_tmul, smul_smul, TensorProduct.tmul_smul,
            map_smul]

/-- The recursively defined finite-qubit words satisfy their stated
involution multiplier. -/
theorem finiteQubitPauliWord_star (n : ℕ) (v : FiniteQubitPauliLabel n) :
    star (finiteQubitPauliWord n v) =
      finiteQubitPauliStarMultiplier n v • finiteQubitPauliWord n (-v) := by
  induction n with
  | zero =>
    simp [finiteQubitPauliWord, finiteQubitPauliStarMultiplier]
  | succ n ih =>
    rcases v with ⟨a, v⟩
    change
      star (matrixTensorStarAlgEquiv (Fin 2)
        (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v)) =
        (singleQubitStarMultiplier a * finiteQubitPauliStarMultiplier n v) •
          matrixTensorStarAlgEquiv (Fin 2)
            (singleQubitPauliWord (-a) ⊗ₜ[ℂ] finiteQubitPauliWord n (-v))
    calc
      star (matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v)) =
          matrixTensorStarAlgEquiv (Fin 2)
            (star (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v)) := by
            rw [map_star]
      _ = matrixTensorStarAlgEquiv (Fin 2)
          (star (singleQubitPauliWord a) ⊗ₜ[ℂ]
            star (finiteQubitPauliWord n v)) := by
            rw [TensorProduct.star_tmul]
      _ = matrixTensorStarAlgEquiv (Fin 2)
          ((singleQubitStarMultiplier a • singleQubitPauliWord (-a)) ⊗ₜ[ℂ]
            (finiteQubitPauliStarMultiplier n v • finiteQubitPauliWord n (-v))) := by
            rw [singleQubitPauliWord_star, ih]
      _ = (singleQubitStarMultiplier a * finiteQubitPauliStarMultiplier n v) •
          matrixTensorStarAlgEquiv (Fin 2)
            (singleQubitPauliWord (-a) ⊗ₜ[ℂ] finiteQubitPauliWord n (-v)) := by
            rw [TensorProduct.smul_tmul, smul_smul, TensorProduct.tmul_smul,
              map_smul]

/-- Every finite qubit stage carries its concrete ordered Pauli-word star
system. -/
noncomputable def finiteQubitPauliSystem (n : ℕ) :
    PauliWordStarSystem (FiniteQubitPauliLabel n) (QubitTensorPower n) where
  word := finiteQubitPauliWord n
  multiplier := finiteQubitPauliMultiplier n
  word_mul := finiteQubitPauliWord_mul n
  star_multiplier := finiteQubitPauliStarMultiplier n
  word_star := finiteQubitPauliWord_star n


/-- The finite-qubit Pauli word basis obtained by iterating the tensor-product
basis and the canonical matrix-tensor star equivalence. -/
noncomputable def finiteQubitPauliBasis : (n : ℕ) →
    Module.Basis (FiniteQubitPauliLabel n) ℂ (QubitTensorPower n)
  | 0 => Module.Basis.singleton (Fin 1) ℂ
  | n + 1 =>
      (singleQubitPauliBasis.tensorProduct (finiteQubitPauliBasis n)).map
        (matrixTensorStarAlgEquiv (Fin 2)).toAlgEquiv.toLinearEquiv

/-- The recursively constructed basis vector is exactly the corresponding
ordered finite-qubit Pauli word. -/
theorem finiteQubitPauliBasis_apply (n : ℕ) (label : FiniteQubitPauliLabel n) :
    finiteQubitPauliBasis n label = finiteQubitPauliWord n label := by
  induction n with
  | zero =>
    change (Module.Basis.singleton (Fin 1) ℂ) label = 1
    exact Module.Basis.singleton_apply (Fin 1) ℂ label
  | succ n ih =>
    rcases label with ⟨u, v⟩
    change
      (singleQubitPauliBasis.tensorProduct (finiteQubitPauliBasis n)).map
          (matrixTensorStarAlgEquiv (Fin 2)).toAlgEquiv.toLinearEquiv (u, v) =
        matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord u ⊗ₜ[ℂ] finiteQubitPauliWord n v)
    rw [Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      singleQubitPauliBasis_apply, ih]
    rfl

/-- The qubit-tower inclusion carries each finite-stage Pauli basis vector to
the coherently labelled basis vector at the later stage. -/
theorem qubitTensorPowerMap_finiteQubitPauliBasis
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitTensorPowerMap n m h (finiteQubitPauliBasis n v) =
      finiteQubitPauliBasis m (finiteQubitPauliLabelMap n m h v) := by
  rw [finiteQubitPauliBasis_apply, finiteQubitPauliBasis_apply]
  exact qubitTensorPowerMap_finiteQubitPauliWord n m h v

end StabilizerHyperfinite
