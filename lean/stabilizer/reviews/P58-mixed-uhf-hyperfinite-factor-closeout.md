# P58 closeout review — mixed UHF factor classification

## Decision

**Status: proved at the stated mixed-sector, conditional Lane-H scope; queue may
advance.**

Aristotle task `ed55ef94-0313-4123-9cc0-b00ffdb465aa` was downloaded as
`aristotle_responses/P58-mixed-uhf-hyperfinite-factor.tar.gz` (SHA-256
`6a9c6e453986cbacfed106b03db592f946fd61c13acb976a9b9da8f4c3c7c7b5`) and
extracted without building, updating, or fetching dependencies at
`aristotle_responses/P58-quarantine/aristotle-stabilizer_two_lane_p58-3px4hkyb_aristotle/`.
Only the packet-authorized module
`AristotleCandidates/MixedUHFHyperfiniteFactor.lean` was integrated into the
live project. Its quarantine and live SHA-256 values agree:
`5dbf9ff8c35035c94b37804435793102cb0c59f88c7a39e2746c32274fc67d20`.
The archive and extraction remain raw response records. No manuscript file was
changed.

## Source and exact declarations

The source basis is the narrow claim in `main.tex:1945-1967`, specifically the
finite maximally-mixed matrix alternative and the infinite maximally-mixed
hyperfinite-II1 assertion at lines 1964-1966. This packet formalizes only the
project-local dyadic mixed sector; it neither establishes the preceding GNS
tensor splitting nor transports its result to the manuscript's regional algebra.

The new module's load-bearing declarations are:

- `qubitMatrixStarEquiv` (line 197) and
  `qubitTensorTrace_eq_normalizedTrace` (line 213), identifying the `n`-qubit
  algebra with `M_(2^n)(C)` and its trace with normalized matrix trace;
- `qubitTensorPower_isMixedMatrixFactor` (line 291), whose explicit fields are
  the star equivalence, positivity of `2^n`, normalized-trace identity,
  traciality, faithfulness, and algebraic scalar centre;
- `qubitUHF_hasScalarCenter` (line 314) and
  `qubitUHF_not_matrixAlgebra` (line 331), the algebraic infinite-limit
  statements;
- `uhfConcreteCStar_isMatricialChain` (line 410), an increasing dense chain of
  finite matrix subalgebras in the P54 concrete C-star model;
- `matrixRange_vonNeumannGenerated_trivialCenter` (line 683) and
  `mixedStage_vonNeumannGenerated_trivialCenter` (line 725), direct
  matrix-unit proofs of trivial centre for each finite-stage generated concrete
  von Neumann algebra;
- `mixedVonNeumann` (line 739), defined as the von Neumann algebra generated
  by `UHFConcreteCStar`; and
- the conditional `mixedVonNeumann_isHyperfiniteFiniteFactor` (line 840).

The last theorem uses exactly the three fields of
`MixedWeakClosurePremises` (lines 798-811): traciality of `uhfVectorState` on
the weak closure, faithfulness there, and `HasTrivialOperatorCenter` of that
weak closure. `IsHyperfiniteFiniteFactorModel` (line 814) is explicitly a
project-local feature predicate: factorhood, a vector-normal faithful tracial
state, a matricial chain, and unbounded matrix sizes. It is **not** a proof of
the Murray-von Neumann/Connes uniqueness/classification theorem for the
hyperfinite II1 factor.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The finite mixed stage is star-isomorphic to `M_(2^n)(C)` with normalized faithful tracial functional and scalar centre. The algebraic UHF limit has scalar centre and is not a finite matrix algebra. In the P54 representation, finite matrix stages form a monotone dense C-star-level chain; each individual stage's generated von Neumann algebra has trivial centre by the local matrix-unit proof. The conditional theorem assembles the stated project-local finite-factor model. |
| partial | Infinite weak-closure traciality, faithfulness, and factorhood are not proved; they are the three named fields above. The module's `IsVectorNormal` is a project-local single-vector-functional predicate, not a formalized Mathlib sigma-weak continuity theory. No canonical hyperfinite-II1 classification/isomorphism is formalized. |
| blocked | Nothing blocks P58's stated gate, because the packet expressly permits an analytic factoriality/classification bridge only as an explicit conditional interface. Those analytic premises remain open for any later use. |
| failed | None. |

The packet's mathematical target is met at its stated scope. The alternate
route is a direct finite-matrix/matrix-unit construction plus a C-star-level
matricial approximation, rather than an unproved weak-closure transfer. It
adds exactly the three `MixedWeakClosurePremises`; it does not silently weaken
the finite result or promote the conditional infinite result to a theorem of
the manuscript.

## Plan alignment

- **Package and lane:** P58, Lane H — correct.
- **Predecessors:** P54 is integrated, compiled, and audited in
  `reviews/P54-uhf-reference-representation-closeout.md`. The imports
  `Formalization.DyadicTensorTower`, P54's
  `UHFReferenceRepresentation`, and the pre-existing local bicommutant core
  are byte-identical between the quarantine snapshot and live checkout. The
  bicommutant core is supporting infrastructure, not an undeclared later Lane-H
  package dependency.
- **Permitted gate:** discharged: the finite mixed matrix alternative is
  proved, and the infinite alternative supplies a checked matrix approximation
  with all weak-closure/factor/classification gaps isolated as named premises.
- **Forbidden downstream claims:** respected. The candidate contains no
  regional alpha transport, pure-sector classification, spatial product
  factorhood, regional factor claim, or final trace/weight theorem. Its
  finite-stage factor statements and conditional mixed weak-closure model are
  confined to the P54 dyadic reference representation.

## Verification

- `lake build AristotleCandidates.MixedUHFHyperfiniteFactor` — passed (8038
  jobs) in the live project.
- `lake build AristotleCandidates.UHFReferenceRepresentation AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.MixedUHFHyperfiniteFactor Formalization` — passed (8089 jobs) in the live project.
- `lake build` — passed in the live project; no work was required after the
  focused build.
- `lake env lean -o .lake/build/lib/lean/AristotleCandidates/MixedUHFHyperfiniteFactor.olean AristotleCandidates/MixedUHFHyperfiniteFactor.lean` — passed in the live project, producing the importable cache used by the axiom check.
- `#print axioms` for `qubitTensorPower_isMixedMatrixFactor`,
  `qubitUHF_hasScalarCenter`, `qubitUHF_not_matrixAlgebra`,
  `uhfConcreteCStar_isMatricialChain`,
  `matrixRange_vonNeumannGenerated_trivialCenter`,
  `mixedStage_vonNeumannGenerated_trivialCenter`,
  `uhfVectorState_isVectorNormal`, and
  `mixedVonNeumann_isHyperfiniteFiniteFactor` — each reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan of the candidate and its three direct imports —
  no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` occurrence.
- Direct-import SHA-256 comparisons, candidate quarantine/live SHA-256
  comparison, and `git diff --check` — passed.

## Adversarial review

No acceptance-blocking finding. The review checked the finite normalization
against the actual recursive matrix equivalence; that the algebraic scalar-
centre proof first reduces an arbitrary limit element to a finite stage; that
the non-matrix result uses a finite-rank obstruction rather than a mere label;
and that the matrix-unit proof establishes only trivial centre for each finite
generated algebra. It also checked that `mixedVonNeumann` factorhood,
faithfulness, and traciality remain three separate explicit premises, and that
the project-local `IsHyperfiniteFiniteFactorModel` is not reported as a
hyperfinite-II1 uniqueness theorem. Lean builds and axiom reports validate the
formal statements, not the manuscript's unformalized GNS tensor splitting or
the open analytic closure bridge.

## Cleanup and worktree state

Kept intentionally: the P58 candidate, this closeout review, its raw archive,
quarantine extraction, and the generated `.olean` under the existing
`.lake/build/` cache. All previously untracked P49/P49A/P49B/P53 candidates
and reviews remain untouched. No commit, push, dependency update, archive
build, fetch, or manuscript modification was performed.
