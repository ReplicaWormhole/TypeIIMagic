# Formalization semantic audit

Status: first inventory in progress.

This document is the approved semantic/tutorial audit described in
`FORMALIZATION-AUDIT-DECISION.md`. It is not itself a proof and does not
change the manuscript theorem status.

## Audit verdict convention

- **proved**: the stated Lean theorem follows from its explicit hypotheses and
  compiles without placeholders;
- **conditional**: the Lean implication is proved, but one or more hypotheses
  are supplied structures or external analytic assumptions;
- **infrastructure**: reusable Lean mathematics with no manuscript claim;
- **unformalized**: a manuscript step for which no corresponding theorem is
  currently present;
- **not aligned**: the Lean conclusion is stronger, weaker, or materially
  different from the natural-language sentence.

Compilation, axiom reports, and mathematical alignment will be recorded
separately.

## Source clauses

The manuscript-facing audit uses only the locators recorded in
`SOURCE-CONTRACT.md`:

- `main.tex:1671-1679`: local symplectic basis and finite-support condition;
- `main.tex:1740-1752`: regional factor theorem statement;
- `main.tex:1915-1920`: proposed adapted-basis star-isomorphism;
- `main.tex:1927-1931`: pure/mixed product density state;
- `main.tex:1945-1967`: GNS, tensor, and factor claims;
- `main.tex:1970-2004`: quasi-equivalence and normal-folium claims.

## Initial module inventory

The detailed theorem ledger and dependency graph are the next sections to be
filled after inspecting the principal declarations. The current theorem
contract itself still says:

```lean
def regionalAlgebraTheoremStatus : String :=
  "conditional contract pending analytic model"
```

That status is consistent with the source contract and is not to be upgraded
without discharging the missing finite-coordinate, representation, normality,
and product-classification premises.

## First-pass verdict

The current formalization is a sequence of conditional bridges, not yet a
formal proof of the manuscript's regional factor theorem. The strongest
currently checked route is:

```text
finite adapted-coordinate data
  -> finite StarAlgEquiv at each stage
  -> coherent algebraic direct-limit StarAlgEquiv alpha
  -> compatible algebraic state transport
  -> supplied compatible operator representation
  -> closed operator-range C*-algebra
  -> supplied state-preserving C*-extension
  -> GNS unitary and algebraic bicommutant transport
  -> conditional product-factor/type classification
```

The arrows are not all existence theorems. In particular, the source-specific
finite coordinate realization, a faithful representation of the algebraic
limit, the regional C*-extension, the analytic normality/WOT statements, and
the product-factor classification remain explicit premises or missing
mathematics.

## Status table for the reviewed overnight packages

| Package | Principal Lean object | Semantic verdict | Main external premise |
|---|---|---|---|
| P37 | `algebraicLimitOperatorRep` | conditional theorem proved | compatible finite-stage operator representations |
| P38 | `quasilocalCStarAlgebra` | conditional theorem proved | supplied compatible representation; stage injectivity for faithfulness |
| P39 | `StatePreservingData`, `gnsUnitary` | conditional theorem proved | C*-completion, alpha extension, state identity and continuity |
| P40 | `bicommutantStarEquiv`, folium transport | algebraic part proved; analytic part conditional | WOT/double-commutant and normal-functional characterizations |
| P41 | `ProductGNSFactorization` | partial boundary only | supplied factorization/classification; infinite weight interface is incomplete |
| P42--P46 | no reviewed candidate currently present | not yet audited | candidate/archive status must be established before use |

All five reviewed packages compile in the local project. Their closeout
reviews explicitly separate compilation from mathematical scope. P41 is
accepted only as partial: its infinite-pure `TracialWeightCore` does not yet
assert positivity, normality, faithfulness, or semifiniteness.

## Dependency spine and one-to-one theorem anchors

### 1. Finite coordinate map

Natural-language sentence:

> Given finite adapted source and target word bases, send each source word to a
> phase-corrected target word.

Lean anchor:

```lean
FiniteAdaptedCoordinateStarData.starEquiv
FiniteAdaptedCoordinateStarData.starEquiv_word
FiniteAdaptedCoordinateStarData.starEquiv_correctedWord
```

Semantic status: the construction is proved from the fields of
`FiniteAdaptedCoordinateStarData`, but the actual manuscript-specific finite
data are not constructed from `main.tex:1671-1679` or `main.tex:1915-1920`.

### 2. Coherence of finite maps

Natural-language sentence:

> The finite coordinate maps commute with the inclusions of stages.

Lean anchor:

```lean
starEquiv_connecting_of_pauliBasis
DirectedFiniteCoordinateFamily.stageEquiv_connecting
```

Semantic status: proved when word, label, phase, and connecting-map
compatibility are supplied.

### 3. Algebraic infinite map

Natural-language sentence:

> Compatible finite maps descend to a unique star-isomorphism of algebraic
> direct limits.

Lean anchor:

```lean
DirectedFiniteCoordinateFamily.alpha
DirectedFiniteCoordinateFamily.alpha_of
DirectedFiniteCoordinateFamily.existsUnique_alpha
```

Semantic status: this is a genuine algebraic direct-limit theorem, conditional
on the finite coherent family. It is not yet a C*-completion theorem.

### 4. State transport

Natural-language sentence:

> Pull the target product state back along the algebraic alpha.

Lean anchor:

```lean
TargetStageStates.targetLimitState
TargetStageStates.pulledBackState
TargetStageStates.pulledBackState_eq_targetLimitState_alpha
TargetStageStates.pulledBackState_isAlgebraicState
```

Semantic status: the state-level implication is proved from compatible target
stage states. The infinite product density operator itself is not constructed
as a von Neumann-algebraic state in this module.

### 5. Algebraic operator representation

Natural-language sentence:

> Compatible finite-stage operator representations define a representation of
> the quasi-local algebra.

Lean anchor:

```lean
algebraicLimitOperatorRep
algebraicLimitOperatorRep_of
algebraicLimitOperatorRep_stage_congr
algebraicLimitOperatorRep_injective
```

Semantic status: proved conditionally. Injectivity requires stagewise
injectivity; no infinite tensor-product Hilbert space is constructed.

### 6. Concrete C*-model

Natural-language sentence:

> Complete the quasi-local algebra in the operator norm.

Lean anchor:

```lean
OperatorRepresentation.rangeClosure
OperatorRepresentation.embedding
OperatorRepresentation.denseRange_embedding
```

and, for the direct-limit range,

```lean
quasilocalCStarAlgebra
quasilocalEmbedding
denseRange_quasilocalEmbedding
```

Semantic status: the closure is genuinely constructed inside bounded
operators, but only after an isometric operator representation is supplied.
This does not prove that the manuscript's algebra has such a representation.

### 7. State-preserving GNS transport

Natural-language sentence:

> A state-preserving C*-isomorphism induces a canonical GNS unitary.

Lean anchor:

```lean
StatePreservingData.sourceState_eq_pullback
StatePreservingData.gnsUnitary
StatePreservingData.gnsUnitary_intertwines
StatePreservingData.gnsConjStarAlgEquiv
```

Semantic status: proved from supplied C*-completions, state positivity/order
data, continuity, and an exact state identity. It is not a proof of the
manuscript's state identity.

### 8. Bicommutant transport

Natural-language sentence:

> The GNS unitary identifies the represented von Neumann algebras.

Lean anchors:

```lean
StarSubalgebra.vonNeumannGenerated
StarSubalgebra.le_vonNeumannGenerated
StarSubalgebra.vonNeumannGenerated_le
bicommutantStarEquiv_sourceRepVN
```

Semantic status: the algebraic bicommutant/conjugation statement is proved.
The identification with strong/weak operator closure and the normal-folium
step are conditional interfaces, not proved analytic theorems.

### 9. Product-factor and trace conclusion

Natural-language sentence:

> The product GNS algebra is a type-I pure factor tensor a finite type-I or
> hyperfinite type-II1 mixed factor, with the appropriate trace conclusion.

Lean anchors:

```lean cddddddddssssssssssssssssssssssssssw1
ProductGNSFactorization.pureFactor_typeI_of_finite
ProductGNSFactorization.pureFactor_typeIInfinity_of_infinite
ProductGNSFactorization.mixedFactor_typeI_of_finite
ProductGNSFactorization.mixedFactor_hyperfiniteII1_of_infinite
finitePureSector_product_classification
infinitePureSector_product_classification
```

Semantic status: the type labels and tensor identification are supplied data.
The finite algebraic trace transport is proved. The infinite-pure package does
not yet provide a faithful normal semifinite weight, so the corrected
infinite-sector trace conclusion is not formalized.
