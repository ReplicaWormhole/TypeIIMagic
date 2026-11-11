# P39 closeout review — state-preserving C-star alpha and GNS transport

## Decision

**Status: proved at the packet's stated conditional scope.**

The reviewed and integrated module is
`AristotleCandidates/StatePreservingGNSModel.lean`.  It was retrieved in the
quarantine archive `aristotle_responses/P39-state-preserving-gns-model.tar.gz`,
extracted at
`aristotle_responses/P39-extracted/aristotle-stabilizer_hyperfinite-oadr2kun_aristotle/`,
and was never built, updated, or dependency-fetched there.  The live module is
byte-identical to the reviewed candidate.  No remote file other than that
candidate module was integrated; the archive and extraction remain the raw
response record.

## Source and scope

This is a manuscript-facing conditional interface with source basis
`main.tex:1921-1958`.  Those lines state the pullback state
`tilde omega = omega_S circ alpha`, give the local pure/mixed density formula,
and propose the associated GNS representation.  They do not construct the
finite adapted-coordinate data, C-star completions, a bounded extension, or
the infinite tensor-product/GNS decomposition.  The module exposes the first
three of these as data and does not claim the last.

## Exact declarations and assumptions

`RegionalConcreteCompletionData` supplies:

- `limitData : RegionalLimitData`, hence the P23 finite-coordinate algebraic
  direct-limit data and coherent stage equivalences;
- a Hilbert space `H`, compatible stage representations
  `rho i : Source i ->*_a[complex] (H ->L[complex] H)`, and `rho_compat`;
- a target C-star algebra `TargetCStar`, dense target algebraic embedding
  `targetEmbed`, and `targetEmbed_dense`; and
- an extension
  `alphaCStar : quasilocalCStarAlgebra rho rho_compat ~=*_a[complex] TargetCStar`
  with its exact finite-stage formula `alphaCStar_stage`.

`StatePreservingData` additionally supplies partial orders and star-ordered
ring instances required by the GNS API, positive unital source and target
functionals, continuity of `targetState`, and the explicit premise
`state_compat : sourceState a = targetState (alphaCStarMap a)`.

With optional target-stage expectation data `S : TargetStageStates ...` and
the explicit restriction premise `h_restrict`, the principal declarations are:

- `RegionalConcreteCompletionData.eq_of_stage_formulas`: continuous complex
  linear functionals agreeing on every concrete finite-stage element agree;
- `StatePreservingData.continuous_sourceState` and
  `sourceState_eq_pullback`: the source state is the continuous pullback;
- `sourceState_stageElem`, `sourceState_sourceEmbed`, and
  `sourceState_unique_of_continuous`: the exact finite-stage expectation
  formula and its dense uniqueness consequence;
- `gnsUnitary`, `gnsUnitary_intertwines`, and
  `gnsUnitary_symm_intertwines`: the canonical GNS isometric equivalence and
  intertwining along the supplied extension; and
- `gnsConjStarAlgEquiv`, `gnsConj_range`,
  `gnsConj_image_centralizer`, and
  `gnsConj_image_centralizer_centralizer`: operator conjugation and only the
  algebraic centralizer/bicentralizer transport inherited from P26.

`state_preserving_gns_package` collects the isometry, state pullback,
finite-stage and algebraic-limit formulas, GNS intertwining, inner-product
preservation, and algebraic-centralizer transport.  `opStatePreserving` is a
one-stage non-vacuity witness only, not a regional model.

## Scope classification

| Classification | Result |
| --- | --- |
| proved | At the supplied-data scope: concrete source completion through P38, continuous state pullback, dense finite-stage uniqueness, and the GNS unitary/intertwining consequences. |
| partial | None at P39's stated scope. |
| blocked | The manuscript-specific finite coordinate construction, compatible faithful stage representation, regional completion/extension, and state restriction remain explicit external premises. |
| failed | None. |

The packet's mathematical target is met at its stated scope.  It does not
prove the asserted tensor-product decomposition, normality, a von Neumann
equivalence, factor type, hyperfiniteness, or a trace/weight statement.

## Adversarial review

No defect was found in the reviewed conditional interface.  In particular:

- the dense-equality theorem requires continuity of both functionals;
- state continuity is derived only from the supplied continuous target state
  and supplied C-star equivalence;
- the finite-stage formula requires the explicit `h_restrict` premise; and
- all completion, alpha, order, and state data remain fields rather than
  hidden axioms or manuscript-derived facts.

The source locator was checked directly against the authoritative manuscript.
No `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or
`native_decide` declaration occurs in the candidate.  Residual risk is exactly
the unformalized manuscript-specific and analytic input listed above; Lean
compilation verifies this conditional interface, not those premises.

## Verification

- `lake build AristotleCandidates.StatePreservingGNSModel` — passed.
- `lake build AristotleCandidates.ConcreteQuasilocalCStarModel AristotleCandidates.CStarAlphaGNSBridge AristotleCandidates.StatePreservingGNSModel Formalization` — passed.
- `lake build` — passed in the already-built live project.
- `lake env lean /dev/stdin` with `#print axioms` for dense equality, state
  continuity/uniqueness, GNS intertwining, the package theorem, and the
  non-vacuity witness — passed; each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Candidate equality and forbidden-placeholder scan — passed.

## Cleanup and worktree state

Kept intentionally:

- `AristotleCandidates/StatePreservingGNSModel.lean`, the sole reviewed P39
  integration;
- the P39 quarantine archive and extracted snapshot under
  `aristotle_responses/`; and
- this closeout review.

All pre-existing modified and untracked work was preserved.  No manuscript
file was modified, and no commit, push, dependency update, or archive build
was performed.
