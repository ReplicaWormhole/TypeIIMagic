import Formalization.FinitePureMixedQubitState
import AristotleCandidates.InfiniteAlgebraicStateTransport

/-!
# Finite pure/mixed product-state coherence

**Context declaration.** Source basis: `main.tex:1927-1944`, where a pure/mixed
product density state is written down on an adapted coordinate system and then
used as the input of a direct-limit/GNS step.

This file formalizes only the *finite algebraic* half of that step: the
concrete finite-stage pure/mixed qubit product states of
`Formalization.FinitePureMixedQubitState` are shown to be coherent with the
dyadic finite-stage embeddings `qubitTensorPowerMap`, together with the
explicit Pauli-word expectation formula *after* an inclusion, and the whole
family is packaged as the compatible state family consumed by the algebraic
direct-limit state transport of
`AristotleCandidates.InfiniteAlgebraicStateTransport`.

## What is proved here

* `qubitPureMixedPauliExpectation_labelMap` and
  `qubitPureMixedPauliAllowed_labelMap`: padding a finite Pauli word with
  identity qubits changes neither its pure/mixed expectation nor its
  membership in the allowed (stabilizer selection rule) set — for *every*
  pure/mixed pattern, whether the padded coordinates are pure or maximally
  mixed.
* `qubitPureMixedState_map_finiteQubitPauliWord`: the explicit expectation
  formula after inclusion,
  `omega_m (iota_{n,m} (W_v)) = qubitPureMixedPauliExpectation pure n v`.
* `QubitTowerStateFamily`, a compatible family of algebraic states on the
  dyadic tower, its instance `pureMixedFamily` and the induced algebraic state
  `QubitTowerStateFamily.limitState` on the algebraic UHF limit.
* `QubitTowerCoordinates`, the *supplied* identification of the target stages
  of a P23 `RegionalLimitData` with dyadic qubit stages, and
  `QubitTowerCoordinates.targetStageStates`, which turns a
  `QubitTowerStateFamily` into a
  `InfiniteAlgebraicStateTransport.TargetStageStates`, i.e. exactly the
  compatible state family required by the algebraic transport, with its
  finite-stage and Pauli-word formulas.

## What is *not* claimed

Nothing here asserts a C⋆ norm, completion, or continuity of any of these
functionals, a GNS representation or GNS tensor factorization, normality, a
spatial tensor product, a von Neumann closure, or an identification of any of
these states with an actual regional state.  The identification data
`QubitTowerCoordinates` is a hypothesis, never constructed.  No gLU,
refinement, or layer-coherence assumption occurs.
-/

namespace AristotleCandidates

namespace FiniteProductStateCoherence

open StabilizerHyperfinite

/-! ### Coherence of the Pauli-word expectation with identity padding -/

/-- A one-qubit identity label has expectation `1` in the pure zero-vector
state. -/
@[simp]
theorem singleQubitPureExpectation_zero :
    singleQubitPureExpectation 0 = 1 := by
  simp [singleQubitPureExpectation]

/-- A one-qubit identity label has expectation `1` in the normalized trace. -/
@[simp]
theorem singleQubitMixedExpectation_zero :
    singleQubitMixedExpectation 0 = 1 := by
  simp [singleQubitMixedExpectation]

/-- Adjoining one identity qubit on the left leaves the pure/mixed Pauli-word
expectation unchanged, whatever the pattern prescribes for the new
coordinate. -/
theorem qubitPureMixedPauliExpectation_labelSuccEmbedding (pure : ℕ → Bool)
    (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliExpectation pure (n + 1)
        (finiteQubitPauliLabelSuccEmbedding n v) =
      qubitPureMixedPauliExpectation pure n v := by
  change (if pure n then singleQubitPureExpectation 0
      else singleQubitMixedExpectation 0) *
        qubitPureMixedPauliExpectation pure n v =
      qubitPureMixedPauliExpectation pure n v
  by_cases h : pure n <;> simp [h]

/-- The pure/mixed Pauli-word expectation is invariant under the coherent
label inclusion into any later stage of the dyadic tower. -/
theorem qubitPureMixedPauliExpectation_labelMap (pure : ℕ → Bool)
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliExpectation pure m (finiteQubitPauliLabelMap n m h v) =
      qubitPureMixedPauliExpectation pure n v := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [finiteQubitPauliLabelMap_self]
    rfl
  | succ m h ih =>
    rw [finiteQubitPauliLabelMap_succ n m h, AddMonoidHom.comp_apply,
      qubitPureMixedPauliExpectation_labelSuccEmbedding, ih]

/-- Adjoining one identity qubit does not change whether a Pauli word survives
the pure/mixed selection rule. -/
theorem qubitPureMixedPauliAllowed_labelSuccEmbedding (pure : ℕ → Bool)
    (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliAllowed pure (n + 1)
        (finiteQubitPauliLabelSuccEmbedding n v) ↔
      qubitPureMixedPauliAllowed pure n v := by
  change ((if pure n then (0 : SingleQubitLabel).1 = 0
      else (0 : SingleQubitLabel) = 0) ∧
        qubitPureMixedPauliAllowed pure n v) ↔ _
  by_cases h : pure n <;> simp [h]

/-- The pure/mixed selection rule is invariant under the coherent label
inclusion into any later stage of the dyadic tower. -/
theorem qubitPureMixedPauliAllowed_labelMap (pure : ℕ → Bool)
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliAllowed pure m (finiteQubitPauliLabelMap n m h v) ↔
      qubitPureMixedPauliAllowed pure n v := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [finiteQubitPauliLabelMap_self]
    exact Iff.rfl
  | succ m h ih =>
    rw [finiteQubitPauliLabelMap_succ n m h, AddMonoidHom.comp_apply,
      qubitPureMixedPauliAllowed_labelSuccEmbedding]
    exact ih

/-- The complex indicator of the selection rule is likewise invariant under
identity padding. -/
theorem qubitPureMixedPauliIndicator_labelMap (pure : ℕ → Bool)
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliIndicator pure m (finiteQubitPauliLabelMap n m h v) =
      qubitPureMixedPauliIndicator pure n v := by
  rw [← qubitPureMixedPauliExpectation_eq_indicator,
    ← qubitPureMixedPauliExpectation_eq_indicator,
    qubitPureMixedPauliExpectation_labelMap]

/-! ### The Pauli-word expectation formula after a finite-stage inclusion -/

/-- **Pauli-word formula after inclusion.**  A finite Pauli word included into
any later stage of the dyadic tower keeps its pure/mixed product-state
expectation. -/
theorem qubitPureMixedState_map_finiteQubitPauliWord (pure : ℕ → Bool)
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure m
        (qubitTensorPowerMap n m h (finiteQubitPauliWord n v)) =
      qubitPureMixedPauliExpectation pure n v := by
  rw [qubitPureMixedState_map, qubitPureMixedState_finiteQubitPauliWord]

/-- The same value, read off at the later stage: the included word is the
identity-padded word, and its later-stage expectation is the original one. -/
theorem qubitPureMixedState_finiteQubitPauliWord_labelMap (pure : ℕ → Bool)
    (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure m
        (finiteQubitPauliWord m (finiteQubitPauliLabelMap n m h v)) =
      qubitPureMixedPauliExpectation pure n v := by
  rw [← qubitTensorPowerMap_finiteQubitPauliWord,
    qubitPureMixedState_map_finiteQubitPauliWord]

/-- The selection-rule form of the formula after inclusion. -/
theorem qubitPureMixedState_map_finiteQubitPauliWord_eq_indicator
    (pure : ℕ → Bool) (n m : ℕ) (h : n ≤ m) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure m
        (qubitTensorPowerMap n m h (finiteQubitPauliWord n v)) =
      qubitPureMixedPauliIndicator pure n v := by
  rw [qubitPureMixedState_map_finiteQubitPauliWord,
    qubitPureMixedPauliExpectation_eq_indicator]

/-! ### The compatible state family on the dyadic tower -/

/-- A compatible family of algebraic states on the dyadic qubit tower: exactly
the data required to induce an algebraic state on the algebraic UHF limit. -/
structure QubitTowerStateFamily where
  /-- The finite-stage functionals. -/
  state : ∀ n, QubitTensorPower n →ₗ[ℂ] ℂ
  /-- Each finite-stage functional is unital and algebraically positive. -/
  isState : ∀ n, IsAlgebraicState (state n)
  /-- Exact compatibility with every canonical finite-stage embedding. -/
  compatible : ∀ (n m : ℕ) (h : n ≤ m) (x : QubitTensorPower n),
    state m (qubitTensorPowerMap n m h x) = state n x

namespace QubitTowerStateFamily

variable (F : QubitTowerStateFamily)

/-- The algebraic direct-limit state determined by a compatible family. -/
noncomputable def limitState : QubitUHFAlgebra →ₗ[ℂ] ℂ :=
  algebraicLimitTrace F.state F.compatible

@[simp]
theorem limitState_of (n : ℕ) (x : QubitTensorPower n) :
    F.limitState
        (DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
      F.state n x :=
  algebraicLimitTrace_of F.state F.compatible n x

theorem limitState_isAlgebraicState : IsAlgebraicState F.limitState :=
  algebraicLimitTrace_isAlgebraicState F.state F.compatible F.isState

end QubitTowerStateFamily

/-- **The concrete pure/mixed product family.**  For every Boolean pure/mixed
coordinate pattern, the finite-stage states of
`Formalization.FinitePureMixedQubitState` form a compatible family. -/
noncomputable def pureMixedFamily (pure : ℕ → Bool) : QubitTowerStateFamily where
  state := qubitPureMixedState pure
  isState := qubitPureMixedState_isAlgebraicState pure
  compatible := qubitPureMixedState_map pure

@[simp]
theorem pureMixedFamily_state (pure : ℕ → Bool) (n : ℕ) :
    (pureMixedFamily pure).state n = qubitPureMixedState pure n :=
  rfl

/-- The limit state of the pure/mixed family is the pure/mixed algebraic UHF
state already constructed on the tower. -/
theorem pureMixedFamily_limitState (pure : ℕ → Bool) :
    (pureMixedFamily pure).limitState = qubitPureMixedUHFState pure := rfl

/-- The Pauli-word formula for the family, at any stage. -/
theorem pureMixedFamily_finiteQubitPauliWord (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) :
    (pureMixedFamily pure).state n (finiteQubitPauliWord n v) =
      qubitPureMixedPauliExpectation pure n v :=
  qubitPureMixedState_finiteQubitPauliWord pure n v

/-! ### Packaging for the algebraic direct-limit state transport -/

open StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv
open AristotleCandidates.InfiniteAlgebraicStateTransport

/-- **Supplied** identification of the target stages of a P23
`RegionalLimitData` with dyadic qubit stages.  Every field is an input: the
qubit counts, the finite-stage star-algebra equivalences with the concrete
qubit matrix stages, the monotonicity of the qubit counts, and the exact
compatibility of the identification with the connecting maps on both sides.
No such identification is constructed here. -/
structure QubitTowerCoordinates (R : RegionalLimitData) where
  /-- The number of qubits used at each stage. -/
  qubits : R.Index → ℕ
  /-- The qubit counts increase along the index order. -/
  qubits_mono : ∀ i j : R.Index, i ≤ j → qubits i ≤ qubits j
  /-- The supplied finite-stage identification with the dyadic tower. -/
  ident : ∀ i, R.Target i ≃⋆ₐ[ℂ] QubitTensorPower (qubits i)
  /-- Exact compatibility of the identification with the connecting maps. -/
  ident_connecting : ∀ (i j : R.Index) (le : i ≤ j) (y : R.Target i),
    ident j (R.targetConnecting i j le y) =
      qubitTensorPowerMap (qubits i) (qubits j) (qubits_mono i j le) (ident i y)

namespace QubitTowerCoordinates

variable {R : RegionalLimitData} (T : QubitTowerCoordinates R)

/-- **The compatible target-stage state family.**  A compatible family of
states on the dyadic tower, read through a supplied stagewise identification,
is a compatible family of target-stage states in the sense required by the
algebraic direct-limit transport. -/
noncomputable def targetStageStates (F : QubitTowerStateFamily) :
    TargetStageStates R where
  omega i := pullback (T.ident i) (F.state (T.qubits i))
  compatible := by
    intro i j le y
    change F.state (T.qubits j) (T.ident j (R.targetConnecting i j le y)) =
      F.state (T.qubits i) (T.ident i y)
    rw [T.ident_connecting, F.compatible]

@[simp]
theorem targetStageStates_omega (F : QubitTowerStateFamily) (i : R.Index)
    (y : R.Target i) :
    (T.targetStageStates F).omega i y = F.state (T.qubits i) (T.ident i y) :=
  rfl

/-- Every supplied target stage carries an algebraic state. -/
theorem targetStageStates_isAlgebraicState (F : QubitTowerStateFamily)
    (i : R.Index) :
    IsAlgebraicState ((T.targetStageStates F).omega i) :=
  isAlgebraicState_pullback (T.ident i) (F.state (T.qubits i)) (F.isState _)

/-- Hence the transported functional on the source algebraic limit is an
algebraic state. -/
theorem pulledBackState_isAlgebraicState (F : QubitTowerStateFamily) :
    IsAlgebraicState (T.targetStageStates F).pulledBackState :=
  TargetStageStates.pulledBackState_isAlgebraicState _
    (T.targetStageStates_isAlgebraicState F)

/-- **The exact finite-stage formula for the transported state.**  On a finite
source stage the transported state is the finite-stage tower state of the
identified element. -/
theorem pulledBackState_sourceOf (F : QubitTowerStateFamily) (i : R.Index)
    (x : R.Source i) :
    (T.targetStageStates F).pulledBackState (R.sourceOf i x) =
      F.state (T.qubits i) (T.ident i (R.stageEquiv i x)) :=
  TargetStageStates.pulledBackState_sourceOf _ i x

/-- **The Pauli-word formula after inclusion, through the transport.**  If a
finite source element is identified with a finite Pauli word at stage `i`,
then the transported pure/mixed state takes on it the explicit pure/mixed
Pauli expectation — and the same value is obtained at every later stage at
which the element is realized. -/
theorem pulledBackState_sourceOf_pureMixed (pure : ℕ → Bool) (i : R.Index)
    (x : R.Source i) (v : FiniteQubitPauliLabel (T.qubits i))
    (hx : T.ident i (R.stageEquiv i x) = finiteQubitPauliWord (T.qubits i) v) :
    (T.targetStageStates (pureMixedFamily pure)).pulledBackState
        (R.sourceOf i x) =
      qubitPureMixedPauliExpectation pure (T.qubits i) v := by
  rw [T.pulledBackState_sourceOf, pureMixedFamily_state, hx,
    qubitPureMixedState_finiteQubitPauliWord]

/-- Stage independence of the Pauli-word value: realizing the same source
element at a later stage pads its word with identity qubits and leaves the
pure/mixed expectation unchanged. -/
theorem pulledBackState_sourceConnecting_pureMixed (pure : ℕ → Bool)
    (i j : R.Index) (le : i ≤ j) (x : R.Source i)
    (v : FiniteQubitPauliLabel (T.qubits i))
    (hx : T.ident i (R.stageEquiv i x) = finiteQubitPauliWord (T.qubits i) v) :
    (T.targetStageStates (pureMixedFamily pure)).pulledBackState
        (R.sourceOf j (R.sourceConnecting i j le x)) =
      qubitPureMixedPauliExpectation pure (T.qubits i) v := by
  rw [TargetStageStates.pulledBackState_sourceConnecting,
    T.pulledBackState_sourceOf_pureMixed pure i x v hx]

end QubitTowerCoordinates

end FiniteProductStateCoherence

end AristotleCandidates
