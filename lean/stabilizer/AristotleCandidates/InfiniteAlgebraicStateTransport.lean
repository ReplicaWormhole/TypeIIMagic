import AristotleCandidates.InfiniteAlgebraicRegionalEquiv
import AristotleCandidates.FiniteStabilizerProductState
import Formalization.AlgebraicLimitStateTransport

/-!
# Infinite algebraic state transport along the regional `alpha`

**Context declaration.** Source basis: `main.tex:1921-1944`.

This file transports a **supplied** compatible family of target-stage
algebraic states through the P23 algebraic direct-limit equivalence
`RegionalLimitData.alpha`.

## What is supplied

Everything is input data:

* a P23 `StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv.RegionalLimitData`
  object `R` — i.e. the two directed systems of finite complex star algebras,
  the finite-stage star-algebra equivalences `R.stageEquiv` and their exact
  compatibility `R.stageEquiv_connecting` with all connecting maps;
* a family `TargetStageStates R` of complex-linear target-stage functionals
  `omega i : R.Target i →ₗ[ℂ] ℂ` together with their exact compatibility
  `omega j (targetConnecting i j le y) = omega i y`; and
* for the optional stabilizer corollary, an explicitly supplied finite
  word/stabilizer realization at every stage (a P17
  `AristotleCandidates.FiniteStabilizerWordRealization`, a realizing element
  `wordElt i w : R.Source i` of every word, its compatibility with the
  connecting maps, and the identification of the transported target-stage
  expectation with the finite pure/mixed qubit product-state expectation).

## What is derived

* `pulledBackState`, the functional on the source algebraic limit obtained
  from `StabilizerHyperfinite.algebraicLimitStatePullback`, which is literally
  the target limit functional composed with `R.alpha`
  (`pulledBackState_eq_targetLimitState_alpha`);
* `pulledBackState_isAlgebraicState`: it is an algebraic state
  (`StabilizerHyperfinite.IsAlgebraicState`, i.e. unital and algebraically
  positive) as soon as every supplied `omega i` is one;
* the **exact finite-stage formula** `pulledBackState_sourceOf`:
  `pulledBackState S (R.sourceOf i x) = S.omega i (R.stageEquiv i x)`
  for every stage `i` and every `x : R.Source i`; and
* `pulledBackState_unique`: that formula determines the functional on the
  source limit uniquely.

The final section combines the above with P17's finite stabilizer indicator
formula: on a supplied finite word realization the limit state takes the value
`1` on stabilizer words and `0` otherwise, and the indicator is therefore
independent of the stage at which the word is realized.

## What is *not* claimed

The content is purely algebraic.  Nothing here asserts or uses a C⋆ norm,
completion or continuity, a GNS representation or GNS equivalence, a spatial
(or any) tensor product, a von Neumann closure or bicommutant, quasi-
equivalence, a factor type classification, hyperfiniteness, or the existence of
a trace or weight.  No gLU condition, refinement scheme, or layer-coherence
hypothesis appears.
-/

namespace AristotleCandidates

namespace InfiniteAlgebraicStateTransport

open StabilizerHyperfinite
open StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv

variable {R : RegionalLimitData}

/-- The **supplied** compatible family of target-stage algebraic functionals.

Both fields are inputs: the finite-stage functionals themselves and their
exact compatibility with every target connecting map.  Positivity and
normalization are *not* part of this bundle; they are hypotheses of the
statements that need them. -/
structure TargetStageStates (R : RegionalLimitData) where
  /-- The supplied target-stage complex-linear functionals. -/
  omega : ∀ i, R.Target i →ₗ[ℂ] ℂ
  /-- Exact compatibility with every target connecting map. -/
  compatible : ∀ (i j : R.Index) (le : i ≤ j) (y : R.Target i),
    omega j (R.targetConnecting i j le y) = omega i y

namespace TargetStageStates

variable (S : TargetStageStates R)

/-- The glued functional on the target algebraic limit determined by the
supplied compatible target-stage functionals. -/
noncomputable def targetLimitState : R.TargetLimit →ₗ[ℂ] ℂ :=
  algebraicLimitTrace (A := R.Target) (f := fun i j le => R.targetConnecting i j le)
    S.omega S.compatible

@[simp]
theorem targetLimitState_targetOf (i : R.Index) (y : R.Target i) :
    S.targetLimitState (R.targetOf i y) = S.omega i y :=
  rfl

/-- **The transported state.**  The functional on the source algebraic limit
obtained by pulling the supplied target-stage functionals back along the P23
algebraic equivalence `alpha`. -/
noncomputable def pulledBackState : R.SourceLimit →ₗ[ℂ] ℂ :=
  algebraicLimitStatePullback (A := R.Source) (f := fun i j le => R.sourceConnecting i j le)
    (D := R.Target) (h := fun i j le => R.targetConnecting i j le)
    R.stageEquiv R.stageEquiv_connecting S.omega S.compatible

/-- The transported state is the target limit functional composed with the P23
algebraic equivalence `alpha`. -/
theorem pulledBackState_eq_targetLimitState_alpha (z : R.SourceLimit) :
    S.pulledBackState z = S.targetLimitState (R.alpha z) :=
  rfl

/-- **The exact finite-stage formula.**  On the image of a finite source stage,
the transported state is the supplied target-stage expectation of the image
under the supplied finite-stage equivalence. -/
@[simp]
theorem pulledBackState_sourceOf (i : R.Index) (x : R.Source i) :
    S.pulledBackState (R.sourceOf i x) = S.omega i (R.stageEquiv i x) :=
  algebraicLimitStatePullback_of (A := R.Source)
    (f := fun i j le => R.sourceConnecting i j le)
    (D := R.Target) (h := fun i j le => R.targetConnecting i j le)
    R.stageEquiv R.stageEquiv_connecting S.omega S.compatible i x

/-- **Uniqueness.**  The finite-stage formula determines the transported state:
any complex-linear functional on the source limit with those finite-stage
values is `pulledBackState`. -/
theorem pulledBackState_unique (phi : R.SourceLimit →ₗ[ℂ] ℂ)
    (h_phi : ∀ (i : R.Index) (x : R.Source i),
      phi (R.sourceOf i x) = S.omega i (R.stageEquiv i x)) :
    phi = S.pulledBackState := by
  refine LinearMap.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ i x =>
    change phi (R.sourceOf i x) = S.pulledBackState (R.sourceOf i x)
    rw [pulledBackState_sourceOf, h_phi]

/-- **The transported functional is an algebraic state** whenever every
supplied target-stage functional is one. -/
theorem pulledBackState_isAlgebraicState
    (h_omega : ∀ i, IsAlgebraicState (S.omega i)) :
    IsAlgebraicState S.pulledBackState :=
  algebraicLimitStatePullback_isAlgebraicState (A := R.Source)
    (f := fun i j le => R.sourceConnecting i j le)
    (D := R.Target) (h := fun i j le => R.targetConnecting i j le)
    R.stageEquiv R.stageEquiv_connecting S.omega S.compatible h_omega

/-- The transported state is unchanged along the source connecting maps: it is
well defined on the direct limit. -/
theorem pulledBackState_sourceConnecting (i j : R.Index) (le : i ≤ j) (x : R.Source i) :
    S.pulledBackState (R.sourceOf j (R.sourceConnecting i j le x)) =
      S.pulledBackState (R.sourceOf i x) := by
  rw [pulledBackState_sourceOf, pulledBackState_sourceOf, R.stageEquiv_connecting,
    S.compatible]

end TargetStageStates

/-!
### Conditional corollary: the P17 stabilizer indicator through the transport

Everything used below is supplied: the finite word/stabilizer realizations at
every stage, the realizing elements of the words inside the finite source
algebras, their compatibility with the source connecting maps, and the
identification of the transported target-stage expectation with the finite
pure/mixed qubit product-state expectation of P17.  No regional or word
realization is constructed here.
-/

section StabilizerWords

open AristotleCandidates

variable {R : RegionalLimitData} (S : TargetStageStates R)
variable {V : R.Index → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module PauliBit (V i)]
variable {Word : R.Index → Type*} {qubits : R.Index → ℕ}
variable {data : ∀ i, AdaptedPauliCoordinateBasis (I := Fin (qubits i)) (V := V i)}
variable {pure : R.Index → ℕ → Bool}

/-- **Conditional stabilizer formula for the transported limit state.**

Hypotheses, all supplied:

* `realization i` is a P17 finite stabilizer word realization at stage `i`;
* `wordElt i w : R.Source i` realizes the word `w` in the finite source
  algebra; and
* `h_state` identifies the supplied target-stage expectation of the
  transported realizing element with the finite pure/mixed qubit product-state
  expectation of the corresponding finite qubit Pauli word.

Conclusion: the transported direct-limit state takes on every realized word
the P17 stabilizer indicator value. -/
theorem pulledBackState_wordElt_eq_stabilizerWordIndicator
    (realization : ∀ i, FiniteStabilizerWordRealization (qubits i) (data i) (pure i) (Word i))
    (wordElt : ∀ i, Word i → R.Source i)
    (h_state : ∀ (i : R.Index) (w : Word i),
      S.omega i (R.stageEquiv i (wordElt i w)) =
        qubitPureMixedState (pure i) (qubits i)
          (finiteQubitPauliWord (qubits i) ((realization i).label w)))
    (i : R.Index) (w : Word i) :
    S.pulledBackState (R.sourceOf i (wordElt i w)) =
      stabilizerWordIndicator (realization i).isStabilizer w := by
  rw [TargetStageStates.pulledBackState_sourceOf, h_state,
    FiniteStabilizerWordRealization.qubitPureMixedState_label_eq_stabilizerWordIndicator]

/-- The transported state is `1` on a supplied stabilizer word. -/
theorem pulledBackState_wordElt_eq_one
    (realization : ∀ i, FiniteStabilizerWordRealization (qubits i) (data i) (pure i) (Word i))
    (wordElt : ∀ i, Word i → R.Source i)
    (h_state : ∀ (i : R.Index) (w : Word i),
      S.omega i (R.stageEquiv i (wordElt i w)) =
        qubitPureMixedState (pure i) (qubits i)
          (finiteQubitPauliWord (qubits i) ((realization i).label w)))
    {i : R.Index} {w : Word i} (hw : (realization i).isStabilizer w) :
    S.pulledBackState (R.sourceOf i (wordElt i w)) = 1 := by
  classical
  rw [pulledBackState_wordElt_eq_stabilizerWordIndicator S realization wordElt h_state,
    stabilizerWordIndicator, if_pos hw]

/-- The transported state vanishes on a supplied non-stabilizer word. -/
theorem pulledBackState_wordElt_eq_zero
    (realization : ∀ i, FiniteStabilizerWordRealization (qubits i) (data i) (pure i) (Word i))
    (wordElt : ∀ i, Word i → R.Source i)
    (h_state : ∀ (i : R.Index) (w : Word i),
      S.omega i (R.stageEquiv i (wordElt i w)) =
        qubitPureMixedState (pure i) (qubits i)
          (finiteQubitPauliWord (qubits i) ((realization i).label w)))
    {i : R.Index} {w : Word i} (hw : ¬ (realization i).isStabilizer w) :
    S.pulledBackState (R.sourceOf i (wordElt i w)) = 0 := by
  classical
  rw [pulledBackState_wordElt_eq_stabilizerWordIndicator S realization wordElt h_state,
    stabilizerWordIndicator, if_neg hw]

/-- **Stage independence of the stabilizer indicator.**  If the supplied word
realizations are compatible with the source connecting maps (via a supplied
word transfer `wordMap`), then the stabilizer indicator of a transferred word
agrees with that of the original word. -/
theorem stabilizerWordIndicator_wordMap
    (realization : ∀ i, FiniteStabilizerWordRealization (qubits i) (data i) (pure i) (Word i))
    (wordElt : ∀ i, Word i → R.Source i)
    (h_state : ∀ (i : R.Index) (w : Word i),
      S.omega i (R.stageEquiv i (wordElt i w)) =
        qubitPureMixedState (pure i) (qubits i)
          (finiteQubitPauliWord (qubits i) ((realization i).label w)))
    (wordMap : ∀ i j : R.Index, i ≤ j → Word i → Word j)
    (h_wordMap : ∀ (i j : R.Index) (le : i ≤ j) (w : Word i),
      R.sourceConnecting i j le (wordElt i w) = wordElt j (wordMap i j le w))
    (i j : R.Index) (le : i ≤ j) (w : Word i) :
    stabilizerWordIndicator (realization j).isStabilizer (wordMap i j le w) =
      stabilizerWordIndicator (realization i).isStabilizer w := by
  have h_transfer :
      S.pulledBackState (R.sourceOf j (wordElt j (wordMap i j le w))) =
        S.pulledBackState (R.sourceOf i (wordElt i w)) := by
    rw [← h_wordMap, S.pulledBackState_sourceConnecting]
  rw [← pulledBackState_wordElt_eq_stabilizerWordIndicator S realization wordElt h_state,
    ← pulledBackState_wordElt_eq_stabilizerWordIndicator S realization wordElt h_state,
    h_transfer]

end StabilizerWords

end InfiniteAlgebraicStateTransport

end AristotleCandidates
