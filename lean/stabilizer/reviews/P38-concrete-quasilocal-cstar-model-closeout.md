# P38 closeout review — concrete quasilocal C-star model

## Decision

**Status: proved at the packet's stated conditional scope.**

The reviewed and integrated module is
`AristotleCandidates/ConcreteQuasilocalCStarModel.lean`.  It was retrieved in
the quarantine archive
`aristotle_responses/P38-concrete-quasilocal-cstar-model.tar.gz`, extracted at
`aristotle_responses/P38-extracted/aristotle-stabilizer_hyperfinite-0_i1v83l_aristotle/`,
and never built, updated, or dependency-fetched there.  No remote file other
than the candidate module was integrated.  The raw archive and its extraction
remain as the response record.

The integrated module differs from the remote candidate only in its source
comment: its locator was corrected from `manuscript/main.tex:1915-1924` to the
authoritative `main.tex:1915-1924`.  This changes neither a declaration nor a
premise.

## Source and scope

This is a manuscript-facing conditional interface with source basis
`main.tex:1915-1924`.  Those lines propose an adapted-basis star-isomorphism
and a pulled-back state; they do **not** supply the faithful operator
representation, a C-star completion, or an infinite tensor-product Hilbert
space.  Accordingly, all such input remains explicit and no stronger
manuscript conclusion is claimed.

## Exact declarations and assumptions

For a nonempty directed preorder, complex stage star algebras `A`, compatible
connecting maps `f`, a supplied complex Hilbert space `H`, and supplied stage
representations

`rho i : A i →⋆ₐ[ℂ] (H →L[ℂ] H)`

with

`compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x`,

the module declares:

- `quasilocalCStarAlgebra rho compat`, the closure of the range of
  `algebraicLimitOperatorRep rho compat` inside bounded operators;
- `quasilocalEmbedding`, its canonical star-algebra map from `DirectLimit A f`;
- `coe_quasilocalEmbedding_of` and `quasilocalEmbedding_of_apply`, the exact
  finite-stage operator and vector formulas;
- `denseRange_quasilocalEmbedding` and `denseRange_stage_images`;
- `range_algebraicLimitOperatorRep` and
  `coe_quasilocalCStarAlgebra_eq_closure_iUnion`, identifying the concrete
  algebra with the closure of the union of stage operator ranges;
- `injective_quasilocalEmbedding`, conditional on the added explicit premise
  `h_inj : ∀ i, Function.Injective (rho i)`; and
- `quasilocalCStarAlgebra_le` and `quasilocalCStarAlgebra_isLeast`, its
  closed-star-subalgebra minimality.

`IsometricStageRepresentation` adds the explicit premise
`norm_rho : ∀ i a, ‖rho i a‖ = ‖a‖`.  Its `injective_embedding` derives
faithfulness, while `norm_embedding_of` is only a finite-stage norm formula.
The dyadic `QubitOperatorRepresentationData` specialization has no norm
instance for the project's qubit stages, so
`injective_qubitQuasilocalEmbedding` correctly retains the explicit
stage-injectivity assumption.  No isometry of an already normed algebraic
direct limit is asserted or needed.

## Scope classification

| Classification | Result |
| --- | --- |
| proved | The conditional concrete closed operator-range C-star model, dense algebraic embedding, finite-stage formulas, closure-of-union description, and minimality. |
| partial | None at P38's stated scope. |
| blocked | No Lean/API obstruction for this conditional construction.  Constructing the project-specific faithful compatible representation remains an external obligation. |
| failed | None. |

The packet's mathematical target is met at its stated scope.  It does not
prove the manuscript's regional C-star isomorphism, construct an infinite
tensor-product Hilbert space, establish GNS factorization or normality, take a
bicommutant, or establish a factor/trace classification.

## Adversarial review

No defect was found in the reviewed scope.  In particular, density is proved
in the subtype concrete algebra, the closure statement is only for the union
of the supplied finite-stage operator ranges, and faithfulness is conditional
on stage injectivity (or derived from the explicit stagewise norm equality).
The audit found no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
`implemented_by`, or `native_decide` declaration.

Residual risk: Lean checks validate the conditional formal interface and its
dependencies, not the missing project-specific representation or the analytic
and von Neumann-algebraic steps outside the packet.

## Verification

- `lake build AristotleCandidates.ConcreteQuasilocalCStarModel` — passed
  before and after the source-locator correction.
- `lake build AristotleCandidates.AlgebraicLimitOperatorRepresentation AristotleCandidates.ConcreteCStarCompletion AristotleCandidates.ConcreteQuasilocalCStarModel Formalization` — passed.
- `lake build` — passed in the already-built live project.
- `lake env lean /dev/stdin` with `#print axioms` for the concrete algebra,
  dense embedding, finite-stage formula, conditional faithfulness,
  closure/minimality, isometric embedding, and dyadic closure theorem — passed;
  each reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan and both tracked/untracked whitespace checks — passed.

## Cleanup and worktree state

Kept intentionally:

- `AristotleCandidates/ConcreteQuasilocalCStarModel.lean`, the sole reviewed
  candidate integration;
- the P38 quarantine archive and extracted snapshot under `aristotle_responses/`;
- this closeout review.

All pre-existing modified and untracked work was preserved.  No manuscript
file was modified, and no commit, push, dependency update, or archive build
was performed.
