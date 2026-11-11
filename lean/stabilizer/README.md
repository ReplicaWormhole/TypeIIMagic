# Stabilizer Hyperfinite Formalization

This is a standalone Lean project.  It is deliberately outside the Overleaf
checkout and does not edit the manuscript.

## Scope

The source claim is the proposed normal `*-isomorphism`

\[
  \mathcal M_\Gamma \cong \mathcal B(\mathcal K)\,\bar\otimes\,\mathcal R,
\]

where `\mathcal R` is the hyperfinite type `II_1` factor.  This project
formalizes the algebraic transport lemma and a concrete dyadic finite-stage
trace system.  It does not identify a regional von Neumann algebra with a
completed hyperfinite factor: that operator-algebraic identification remains
an explicit interface until its missing compatibility assumptions are proved.

The project distinguishes two cases which the manuscript had conflated:

* if `\mathcal K` is finite dimensional, the tensor-product trace can be a
  normal tracial state;
* if `\mathcal K` is infinite dimensional, `\mathcal B(\mathcal K)` has no
  tracial state.  The corresponding tensor-product trace is semifinite, not a
  state.

`Formalization/ProperlyInfiniteTraceObstruction.lean` checks the algebraic
core of this second point: two isometries with range projections summing to
the identity contradict a unital cyclic trace, hence also an algebraic
tracial state.  Connecting that abstract criterion to a particular infinite
von Neumann representation remains analytic work.

The manuscript-only source contract is in `SOURCE-CONTRACT.md`. The source and
proof-audit record is in `blueprints/001-tensor-product-trace.tex`. Earlier
gLU/refinement artifacts are retained as legacy infrastructure only; see
`CONTEXT-LEDGER.md`.

## Module map

`Formalization.Manuscript` is the manuscript-facing Lean entry point. It orders
the project as `SourceDefinitions`, `FiniteModel`, `AlgebraicLimit`,
`ProductState`, `GNSBridge`, `TraceDichotomy`, and `TheoremContract`.
`Formalization.Infrastructure` exposes reusable checked material without a
manuscript claim. `Formalization.Legacy` is an opt-in aggregate for quarantined
exploratory modules and is not imported by `Formalization.lean`.

## Current checked result

`Formalization/TraceTransport.lean` proves that an algebraically positive,
unital tracial functional pulls back along a `StarAlgEquiv` to an algebraic
tracial state, and that traciality is reflected by such an equivalence.  Thus
a nontracial product state cannot become tracial merely by changing
coordinates.  No axiom, `sorry`, or unproved model-factor classification is
used by these theorems.

`Formalization/FiniteMatrixTrace.lean` proves that the normalized trace on a
nonempty finite full matrix algebra is an algebraic tracial state, including
positivity through an explicit sum-of-squares calculation.

`Formalization/FiniteCornerTrace.lean` transports that checked finite trace to
any finite corner supplied with an explicit `StarAlgEquiv` to a full matrix
algebra.

`Formalization/FiniteTensorTrace.lean` identifies the finite algebraic tensor
product of two matrix factors through the Kronecker `StarAlgEquiv` and proves
the product-trace formula on elementary tensors.

`Formalization/MatrixOverTrace.lean` proves the finite type-I amplification
lemma in the needed noncommutative form: for an algebraic tracial state
`tau : R -> ℂ`, the normalized diagonal functional on `Matrix n n R` is an
algebraic tracial state.  It then transports this trace along an explicitly
supplied `StarAlgEquiv` into the target regional algebra.

`Formalization/TensorMatrixEquiv.lean` proves the canonical algebraic
star-isomorphism
`Matrix n n ℂ ⊗[ℂ] R ≃⋆ₐ[ℂ] Matrix n n R`, rather than assuming a finite
product identification as data.  It proves the induced product-trace formula
on elementary tensors.

`Formalization/DyadicTensorTower.lean` builds the concrete finite qubit tower
in iterated matrix-amplification form, with the diagonal embeddings that
correspond to adjoining an identity qubit.  It proves finite-stage trace
compatibility for all inclusions and constructs an algebraic tracial state on
the resulting directed algebraic limit.  This is the algebraic infinite qubit product,
not its C-star or von Neumann completion.

`Formalization/SingleQubitPauli.lean` and
`Formalization/FiniteQubitPauli.lean` make the finite target stages concrete:
they prove the ordered one-qubit Pauli multiplication and star phases, its
four-element complex basis, and their recursive finite-stage analogues.  The
dyadic identity embeddings preserve these words and their phases.  This
eliminates the former finite-stage target-side Pauli-basis assumption.  A
single global target word system and the matching regional source data remain
separate obligations.

`Formalization/QubitMatrixState.lean` and
`Formalization/FinitePureMixedQubitState.lean` formalize the state actually
suggested by an adapted stabilizer coordinate decomposition.  A Boolean
coordinate pattern selects either the `|0⟩` vector state or the normalized
qubit trace at each finite stage.  These states are positive, compatible with
the dyadic embeddings, and therefore define an algebraic state on the UHF
direct limit.  The value on every finite Pauli word is explicit.  When every
coordinate is mixed, this is exactly `qubitUHFTrace`; when a pure coordinate is
present it is not promoted to a tracial state.  More precisely, a pure
coordinate permits only a zero X exponent, whereas a mixed coordinate permits
only the identity Pauli word.  Lean proves the expected obstruction already
for one pure qubit, and now for an arbitrary pure coordinate in the direct
limit: its vector-state factor is not cyclic, hence is not tracial.  Thus the
algebraic UHF product state is tracial if and only if every coordinate is
mixed, precisely when it equals the checked UHF trace.

`Formalization/AlgebraicLimitStateTransport.lean` transports this compatible
state family across any coherent finite-stage `StarAlgEquiv` family.  It is the
formal conditional bridge from a regional finite-coordinate construction to
the corresponding quasi-local algebraic state.

`Formalization/CoherentBasisEquiv.lean` and
`Formalization/CoherentPhaseQubitState.lean` make that coherence condition
finite and checkable.  If a finite-stage coordinate equivalence sends each
source basis word to a specified phase times a concrete finite Pauli word, and
the source-basis embedding, phase, and Pauli-label maps are coherent under
enlarging the stage, Lean derives compatibility on every algebra element.
This gives a star-algebra equivalence of algebraic direct limits to the
concrete qubit-UHF algebra, then transports the pure/mixed product state and
proves its exact value on each source basis word.  Its all-mixed
specialization pulls the UHF trace back to a source algebraic tracial state,
and the corresponding pure/mixed source state is tracial exactly when all
coordinates are mixed.  This does not manufacture the required regional
coordinate bases or their coherence; it isolates those as the remaining
finite geometric inputs rather than assuming a global infinite map.

`Formalization/FinitePureUHFProduct.lean` combines that concrete tracial
algebraic product with an arbitrary nonempty finite matrix factor.  It proves
the product algebraic tracial state and its elementary-tensor formula.  This
is the formal finite-pure-sector analogue of the asserted tensor-product
trace, still before the UHF completion and normality statement.
`Formalization/FinitePureUHFTraceTransport.lean` then proves the requested
induction step for any separately established regional `StarAlgEquiv`: it
pulls this product trace back to an algebraic tracial state on the region and
retains the elementary-tensor formula on inverse images.

`Formalization/SymplecticCoordinates.lean` proves the linear finite-word
consequence of an adapted Hamel basis: every label has a finitely supported
coordinate representative, and the chosen X/Z coordinate labels map to the
specified basis vectors.  `Formalization/AdaptedStabilizerSubspace.lean`
then proves the missing stabilizer-membership criterion: the selected
Z-coordinate span contains exactly the finite words with no X coordinate and
no Z coordinate outside the selected set.  `Formalization/PauliCocycleCompatibility.lean`
then proves the exact multiplier and involution phase equations required for
such a coordinate map to respect Pauli-word multiplication and star.  These
modules deliberately do not call symplecticity alone a Pauli star-algebra
isomorphism.  Formalization/StabilizerCharacterCalibration.lean proves
that the quotient of two multiplier phases is an ordinary additive character,
that an additive character on a vector subspace extends to the ambient vector
space by a complementary-subspace construction, and that calibration by the
extended Pauli-bit character preserves both the Pauli-word multiplication and
involution compatibility equations.  This checks the algebraic
stabilizer-sign calibration once the initial Pauli phase correction is
given.  Formalization/FiniteSupportQuadraticRefinement.lean defines the
blueprint's finite-support quadratic-refinement formula itself and proves its
global polarization and diagonal identities.  Its explicit finite double-sum
discrepancy pairing is additive in both arguments and symmetric for a
symmetric discrepancy.  Formalization/CoordinateQuadraticPhase.lean uses
these results to produce the required Pauli-word multiplication and star
compatibility certificates once the concrete source/target exponents are
identified with that pairing.  Together with
Formalization/PhaseCorrectedWordBasisEquiv.lean, it gives a `StarAlgEquiv`
between distinct source and target algebras whenever the phase-corrected word
map is supplied as a linear equivalence on a Pauli-word basis.  The remaining
obligations are this concrete regional identification and the extension of
words to the quasi-local C-star algebra.

`Formalization/FiniteQubitPauliSelection.lean` now identifies the recursive
finite-qubit label convention with this same selected-Z rule: a coordinate
marked pure has zero X exponent, while an unmarked (mixed) coordinate has the
identity label.  It proves that the finite pure/mixed Pauli expectation is the
indicator of that condition, and identifies it with literal membership in the
selected-Z submodule after an arbitrary supplied adapted coordinate basis.
`CoherentPhaseQubitState.lean` consequently offers a source-basis expectation
formula directly in terms of the selected-Z indicator, conditional on the
already explicit coherent finite-stage data.
It also has a theorem whose single additional premise is the actual regional
membership identification: selected target labels are exactly the source
stabilizer basis words.  The conclusion is the phase-weighted stabilizer expectation
formula on every basis word; completing this step requires an explicitly
supplied finite-coordinate construction, which the manuscript does not yet
specify.

`Formalization/CoordinateQuadraticPhaseTrace.lean` composes this concrete
phase result with the finite-pure times qubit-UHF trace construction: the same
regional word-system, exponent, and basis hypotheses now produce both a
`StarAlgEquiv` to `Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra` and the induced algebraic
tracial state with its elementary-tensor formula.  The interface uses only a
`Semiring` because that is the actual structure of the algebraic direct-limit
model; no unproved additive-inverse structure is imposed.

Formalization/WordBasisExtension.lean proves the algebraic extension step:
when Pauli words form a complex linear basis, a linear map that preserves the
products of all basis pairs is multiplicative on arbitrary finite sums and
therefore gives an algebra homomorphism if it is unital.  It also proves the
conjugate-linear star extension: a bijective such map is a star-algebra
equivalence when it commutes with star on basis words.

Formalization/AlgebraicLimitStarHom.lean moves that finite-word result to
the algebraic quasi-local level.  It proves that compatible finite-stage
star-algebra maps induce a star-algebra map from the directed algebraic
limit, and that compatible finite-stage star-algebra equivalences induce a
star-algebra equivalence of the two algebraic limits.  Norm continuity and
completion remain separate C-star obligations.

`Formalization/CStarEquivExtension.lean` discharges the automatic part of
that analytic step: once the source and target have actually been supplied as
complex C-star algebras, every complex `StarAlgEquiv` is isometric and hence
continuous in both directions.  It also transports continuity of a target
functional along the equivalence.  Constructing the required C-star norms and
completions of the regional and coordinate direct limits remains open.

`Formalization/AlgebraicInductiveTrace.lean` proves that any compatible system
of finite-stage unital cyclic traces glues to a unital cyclic functional on its
algebraic direct limit.

`Formalization/AlgebraicStarDirectLimit.lean` equips that algebraic direct
limit with the involution induced by compatible finite-stage star-algebra maps.
It proves that compatible algebraic tracial states glue to an ordinary
`IsAlgebraicTracialState` on the limit.  This is the checked algebraic
infinite-product layer; no C-star or von Neumann completion is silently
assumed.

`Formalization/AlgebraicLimitTraceTransport.lean` adds the missing transport
step for a quasi-local algebraic factorization: compatible finite-stage
`StarAlgEquiv`s and a compatible target tracial-state family induce a source
direct-limit tracial state, with its value on every finite-stage element fixed
by the target-stage formula.  This is the exact algebraic statement required
once a stabilizer-region construction supplies coherent finite word maps.

## Deliberate boundary

Mathlib 4.28 includes preliminary abstract and concrete von Neumann-algebra
definitions, but its own basic module records the missing equivalence project.
The pinned library does not provide the needed API for infinite von Neumann
tensor products, normal states/traces, hyperfiniteness, or factor-type
classification.  Those analytic results are stated in the blueprint with exact
source locators; they must not be silently replaced by Lean axioms.
