import Formalization.QubitMatrixState
import Formalization.FiniteQubitPauli
import Formalization.AlgebraicLimitStateTransport

/-!
# Finite pure/mixed qubit product states

An adapted stabilizer coordinate system splits finite coordinates into pure
`|0⟩` factors and maximally mixed factors.  This file constructs that state on
the concrete finite stages of the dyadic qubit tower.  The direct-limit and
regional-identification steps remain separate.
-/

namespace StabilizerHyperfinite

/-- The expectation of an ordered one-qubit Pauli word in the pure
zero-vector state. -/
def singleQubitPureExpectation (v : SingleQubitLabel) : ℂ :=
  if v.1 = 0 then 1 else 0

/-- The expectation of an ordered one-qubit Pauli word in the normalized
trace. -/
def singleQubitMixedExpectation (v : SingleQubitLabel) : ℂ :=
  if v = 0 then 1 else 0

/-- The recursively factorized Pauli-word expectation for a finite pattern of
pure and maximally mixed qubit coordinates. -/
def qubitPureMixedPauliExpectation (pure : ℕ → Bool) : (n : ℕ) →
    FiniteQubitPauliLabel n → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun v =>
      (if pure n then singleQubitPureExpectation v.1
      else singleQubitMixedExpectation v.1) *
        qubitPureMixedPauliExpectation pure n v.2

/-- The finite Pauli words that survive the pure/mixed product-state
expectation.  A pure coordinate permits a Z-word but no X exponent, whereas a
mixed coordinate permits only the identity word. -/
def qubitPureMixedPauliAllowed (pure : ℕ → Bool) : (n : ℕ) →
    FiniteQubitPauliLabel n → Prop
  | 0 => fun _ => True
  | n + 1 => fun v =>
      (if pure n then v.1.1 = 0 else v.1 = 0) ∧
        qubitPureMixedPauliAllowed pure n v.2

/-- The complex-valued indicator of the Pauli words surviving a finite
pure/mixed product state. -/
noncomputable def qubitPureMixedPauliIndicator (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) : ℂ := by
  classical
  exact if qubitPureMixedPauliAllowed pure n v then 1 else 0

/-- The finite product-state expectation is one exactly on the allowed Pauli
words and vanishes on all other words. -/
theorem qubitPureMixedPauliExpectation_eq_indicator (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliExpectation pure n v =
      qubitPureMixedPauliIndicator pure n v := by
  induction n with
  | zero =>
    simp [qubitPureMixedPauliExpectation, qubitPureMixedPauliIndicator,
      qubitPureMixedPauliAllowed]
  | succ n ih =>
    rcases v with ⟨a, v⟩
    classical
    by_cases h : pure n
    · simp [qubitPureMixedPauliExpectation, qubitPureMixedPauliIndicator,
        qubitPureMixedPauliAllowed, h, ih]
      by_cases hv : qubitPureMixedPauliAllowed pure n v
      · by_cases ha : a.1 = 0 <;>
          simp [hv, ha, singleQubitPureExpectation]
      · simp [hv]
    · simp [qubitPureMixedPauliExpectation, qubitPureMixedPauliIndicator,
        qubitPureMixedPauliAllowed, h, ih]
      by_cases hv : qubitPureMixedPauliAllowed pure n v
      · by_cases ha : a = 0 <;>
          simp [hv, ha, singleQubitMixedExpectation]
      · simp [hv]

/-- The pure zero-vector expectation of a one-qubit Pauli word has the
expected X-exponent selection rule. -/
theorem singleQubitPauliWord_ketZero_apply (v : SingleQubitLabel) :
    singleQubitPauliWord v 0 0 = singleQubitPureExpectation v := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [singleQubitPauliWord, singleQubitPureExpectation,
      pauliI, pauliX, pauliZ, pauliXZ, Matrix.mul_fin_two]

/-- The normalized one-qubit trace of a Pauli word vanishes away from the
identity word. -/
theorem normalizedMatrixTrace_singleQubitPauliWord (v : SingleQubitLabel) :
    normalizedMatrixTrace (Fin 2) (singleQubitPauliWord v) =
      singleQubitMixedExpectation v := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [normalizedMatrixTrace_apply, singleQubitPauliWord,
      singleQubitMixedExpectation, pauliI, pauliX, pauliZ, pauliXZ,
      Matrix.mul_fin_two, Matrix.trace]

/-- The finite product state selected by a Boolean pure/mixed pattern.  At
stage `n + 1`, `pure n = true` selects the zero-vector state of the new
leftmost qubit; otherwise it selects the normalized trace of that qubit. -/
noncomputable def qubitPureMixedState (pure : ℕ → Bool) : (n : ℕ) →
    QubitTensorPower n →ₗ[ℂ] ℂ
  | 0 => scalarTrace
  | n + 1 =>
      if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
      else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n)

/-- Every finite pure/mixed coordinate product is an algebraic state. -/
theorem qubitPureMixedState_isAlgebraicState (pure : ℕ → Bool) (n : ℕ) :
    IsAlgebraicState (qubitPureMixedState pure n) := by
  induction n with
  | zero =>
    exact scalarTrace_isAlgebraicTracialState.toIsAlgebraicState
  | succ n ih =>
    change IsAlgebraicState
      (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
      else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
    split <;> rename_i h
    · simpa [h] using qubitKetZeroStateOver_isAlgebraicState
        (qubitPureMixedState pure n) ih
    · simpa [h] using normalizedQubitMatrixTraceOver_isAlgebraicState
        (qubitPureMixedState pure n) ih

/-- Adjoining an identity qubit preserves every finite pure/mixed product
state, independently of whether the new qubit is pure or maximally mixed. -/
theorem qubitPureMixedState_succ_embedding (pure : ℕ → Bool) (n : ℕ)
    (x : QubitTensorPower n) :
    qubitPureMixedState pure (n + 1) (qubitTensorPowerSuccEmbedding n x) =
      qubitPureMixedState pure n x := by
  change (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
    else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
      (Matrix.scalar (Fin 2) x) = qubitPureMixedState pure n x
  split <;> rename_i h
  · simpa [h] using qubitKetZeroStateOver_scalar (qubitPureMixedState pure n) x
  · exact normalizedQubitMatrixTraceOver_scalar
      (qubitPureMixedState pure n) x

/-- The finite pure/mixed product states are compatible with every canonical
embedding of the dyadic qubit tower. -/
theorem qubitPureMixedState_map (pure : ℕ → Bool) (n m : ℕ) (h : n ≤ m)
    (x : QubitTensorPower n) :
    qubitPureMixedState pure m (qubitTensorPowerMap n m h x) =
      qubitPureMixedState pure n x := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [qubitTensorPowerMap_self]
    rfl
  | succ m h ih =>
    rw [qubitTensorPowerMap_succ n m h, StarAlgHom.comp_apply,
      qubitPureMixedState_succ_embedding]
    exact ih

/-- The algebraic infinite-qubit product state associated to a prescribed
pure/mixed coordinate pattern. -/
noncomputable def qubitPureMixedUHFState (pure : ℕ → Bool) :
    QubitUHFAlgebra →ₗ[ℂ] ℂ :=
  algebraicLimitTrace (qubitPureMixedState pure) (qubitPureMixedState_map pure)

/-- The compatible finite pure/mixed product states induce an algebraic state
on the infinite qubit direct limit. -/
theorem qubitPureMixedUHFState_isAlgebraicState (pure : ℕ → Bool) :
    IsAlgebraicState (qubitPureMixedUHFState pure) :=
  algebraicLimitTrace_isAlgebraicState (qubitPureMixedState pure)
    (qubitPureMixedState_map pure) (qubitPureMixedState_isAlgebraicState pure)

/-- The infinite pure/mixed state evaluates a finite-stage representative by
the corresponding finite product state. -/
theorem qubitPureMixedUHFState_of (pure : ℕ → Bool) (n : ℕ)
    (x : QubitTensorPower n) :
    qubitPureMixedUHFState pure
      (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
        qubitPureMixedState pure n x :=
  algebraicLimitTrace_of (qubitPureMixedState pure) (qubitPureMixedState_map pure) n x

/-- Any coherent finite-stage identification with the concrete qubit tower
pulls the pure/mixed product state back to a source quasi-local algebraic
state.  This is the state-level interface required of a regional coordinate
construction. -/
theorem exists_pureMixedState_of_coherentQubitStages
    {A : ℕ → Type*}
    [∀ n, Semiring (A n)] [∀ n, StarRing (A n)] [∀ n, Algebra ℂ (A n)]
    {f : ∀ n m : ℕ, n ≤ m → A n →⋆ₐ[ℂ] A m}
    [DirectedSystem A (f · · ·)]
    (pure : ℕ → Bool)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (equivCompatible : ∀ n m (h : n ≤ m) x,
      e m (f n m h x) = qubitTensorPowerMap n m h (e n x)) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n x, omega (DirectLimit.Module.of ℂ ℕ A f n x) =
          qubitPureMixedState pure n (e n x) := by
  refine ⟨algebraicLimitStatePullback e equivCompatible
    (qubitPureMixedState pure) (qubitPureMixedState_map pure), ?_, ?_⟩
  · exact algebraicLimitStatePullback_isAlgebraicState e equivCompatible
      (qubitPureMixedState pure) (qubitPureMixedState_map pure)
      (qubitPureMixedState_isAlgebraicState pure)
  · intro n x
    exact algebraicLimitStatePullback_of e equivCompatible
      (qubitPureMixedState pure) (qubitPureMixedState_map pure) n x

/-- The concrete finite pure/mixed product state has the advertised value on
every ordered finite Pauli word. -/
theorem qubitPureMixedState_finiteQubitPauliWord (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure n (finiteQubitPauliWord n v) =
      qubitPureMixedPauliExpectation pure n v := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rcases v with ⟨a, v⟩
    change (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
      else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
        (matrixTensorStarAlgEquiv (Fin 2)
          (singleQubitPauliWord a ⊗ₜ[ℂ] finiteQubitPauliWord n v)) =
      (if pure n then singleQubitPureExpectation a
      else singleQubitMixedExpectation a) *
        qubitPureMixedPauliExpectation pure n v
    split <;> rename_i h
    · rw [qubitKetZeroStateOver_matrixTensor_tmul]
      rw [singleQubitPauliWord_ketZero_apply, ih]
    · rw [normalizedQubitMatrixTraceOver_matrixTensor_tmul]
      rw [normalizedMatrixTrace_singleQubitPauliWord, ih]

/-- Equivalently, a finite Pauli word has expectation one exactly when it
satisfies the pure/mixed stabilizer selection rule. -/
theorem qubitPureMixedState_finiteQubitPauliWord_eq_indicator
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure n (finiteQubitPauliWord n v) =
      qubitPureMixedPauliIndicator pure n v := by
  rw [qubitPureMixedState_finiteQubitPauliWord,
    qubitPureMixedPauliExpectation_eq_indicator]

/-- The infinite pure/mixed product state has the same explicit expectation
formula on every finite Pauli word embedded into the algebraic UHF limit. -/
theorem qubitPureMixedUHFState_finiteQubitPauliWord (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) :
    qubitPureMixedUHFState pure
      (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n
        (finiteQubitPauliWord n v)) =
      qubitPureMixedPauliExpectation pure n v := by
  rw [qubitPureMixedUHFState_of, qubitPureMixedState_finiteQubitPauliWord]

/-- The same selection rule holds for every finite Pauli word viewed in the
algebraic UHF direct limit. -/
theorem qubitPureMixedUHFState_finiteQubitPauliWord_eq_indicator
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedUHFState pure
      (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n
        (finiteQubitPauliWord n v)) =
      qubitPureMixedPauliIndicator pure n v := by
  rw [qubitPureMixedUHFState_finiteQubitPauliWord,
    qubitPureMixedPauliExpectation_eq_indicator]

/-- With no pure coordinates, the finite product state is exactly the
normalized finite-stage qubit trace. -/
theorem qubitPureMixedState_allMixed (n : ℕ) :
    qubitPureMixedState (fun _ => false) n = qubitTensorTrace n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp only [qubitPureMixedState, Bool.false_eq_true, ↓reduceIte,
      qubitTensorTrace, ih]

/-- The all-mixed infinite product state is the existing algebraic UHF trace. -/
theorem qubitPureMixedUHFState_allMixed :
    qubitPureMixedUHFState (fun _ => false) = qubitUHFTrace := by
  apply algebraicLimitTrace_unique qubitTensorTrace qubitTensorTrace_map
  intro n x
  rw [qubitPureMixedUHFState_of, qubitPureMixedState_allMixed]

/-- Already at one qubit, a pure product-state coordinate is not cyclic and
therefore cannot be a tracial state. -/
theorem onePureQubitState_not_isUnitalTracial :
    ¬ IsUnitalTracial (qubitPureMixedState (fun _ => true) 1) := by
  intro h
  let e01 : QubitTensorPower 1 := !![(0 : ℂ), 1; 0, 0]
  let e10 : QubitTensorPower 1 := !![(0 : ℂ), 0; 1, 0]
  have h_cyclic := h.cyclic e01 e10
  change (e01 * e10) 0 0 = (e10 * e01) 0 0 at h_cyclic
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h_cyclic
  norm_num [e01, e10] at h_cyclic
  have h_one_ne_zero : (1 : ℂ) ≠ 0 := by norm_num
  exact h_one_ne_zero h_cyclic

/-- In particular, the one-qubit pure product state is not an algebraic
tracial state. -/
theorem onePureQubitState_not_isAlgebraicTracialState :
    ¬ IsAlgebraicTracialState (qubitPureMixedState (fun _ => true) 1) := by
  intro h
  exact onePureQubitState_not_isUnitalTracial ⟨h.map_one, h.cyclic⟩

end StabilizerHyperfinite
