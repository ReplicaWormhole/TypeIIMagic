# P47 closeout review — center and finite-projection core

## Decision

**Status: proved at the stated infrastructure scope; queue may advance.**

The completed Aristotle project was downloaded as
`aristotle_responses/P47-center-finite-projection-core.tar.gz` (SHA-256
`51640368062f659201ebae314966a1220fab89b20fa2dfa3c33e4ab364744ea6`) and
extracted, without building or fetching dependencies, at
`aristotle_responses/P47-extracted/aristotle-stabilizer_two_lane_p47-80u8nxnx_aristotle/`.
Only the packet-authorized module
`AristotleCandidates/CenterFiniteProjectionCore.lean` was integrated into the
live project.  Its SHA-256 is
`c55831ac16d3dec3d471c25c24159a5c22c79dff1460c586830eadda27da57d8` in both
the quarantine snapshot and live project.  The archive and extraction remain
as raw response records.

## Exact declarations and assumptions

For a concrete `M : VonNeumannAlgebra H`, with
`[NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]`, the module
defines:

- `center`, `IsProjection`, `IsCentralProjection`, and `ProjLe`;
- `MvNEquiv`, `MvNLe`, and `IsFiniteProjection`;
- the non-unital compressed algebra `corner`;
- `IsCentralSupport` as a predicate and `IsFull := IsCentralSupport _ _ 1`.

The key checked lemmas are `coe_center`, `mem_center_iff`,
`ProjLe.trans`, `MvNEquiv.trans`, `MvNEquiv.add`, `MvNLe.trans`,
`IsFiniteProjection.mul_central`, `corner_eq_image`,
`central_corner_eq_image`, `IsCentralSupport.unique`,
`IsFull.mul_ne_zero`, `isFull_iff_forall_central`, and
`IsFull.exists_nonzero_projection`.

No auxiliary mathematical premise was added.  The only imported project-local
theory is the already locally used P36 concrete bicommutant core
`AristotleCandidates.BicommutantVonNeumannCore`; P47 imports no P47--P61
successor.  The compression/comparison proofs use the ambient C*-identity for
bounded operators, not a topology, normality, or factor-classification
assumption.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The requested concrete algebraic vocabulary and basic center, order, compression, Murray--von Neumann comparison, finite-central-compression, central-support, and fullness lemmas.  In particular, `IsFull.mul_ne_zero` proves that a full projection meets every nonzero central projection nontrivially. |
| partial | None within P47's stated algebraic target. |
| blocked | Existence/construction of a central-support projection, projection-tower limits, normality, corner traces, and analytic comparison theory remain for later packets.  `IsCentralSupport` is intentionally only a predicate. |
| failed | None. |

P47's mathematical target is met at its stated scope.  It does **not** establish
a manuscript theorem, a finite corner for a particular projection, or a
no-type-III conclusion.

## Plan alignment

- **Package and lane:** P47, Lane G.
- **Predecessors:** none.  The packet-authorized P36 bicommutant import is
  already locally present and compiled; it is supporting infrastructure, not
  a P47--P61 dependency.
- **Permitted gate:** discharged: the algebraic center/corner/fullness
  vocabulary required by Lane G is available in the live project.
- **Forbidden downstream claims:** respected.  The module contains no
  projection tower, trace/state, global weight, fullness assertion for a
  manuscript projection, type-III exclusion, normality, spatial tensor
  factorization, or factor classification.

## Verification

- `lake build AristotleCandidates.CenterFiniteProjectionCore` — passed.
- `lake build AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.CenterFiniteProjectionCore Formalization` — passed.
- `lake build` — passed in the already-built live project.
- `lake env lean /dev/stdin` with `#print axioms` for
  `IsFull.mul_ne_zero`, `IsFiniteProjection.mul_central`, `MvNLe.trans`,
  `MvNEquiv.add`, `IsCentralSupport.unique`, `center`, and `corner` — each
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scan of P47 and its direct project import
  — no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`,
  or `native_decide` occurrence.
- Quarantine/live SHA-256 comparison and `git diff --check` — passed.

## Adversarial review

No acceptance-blocking finding.  The audit verified that the only generic
fullness conclusion is the conditional algebraic intersection lemma, and that
the finite-compression theorem is not combined with it to claim the Lane-G/P51
central finite-projection conclusion.  Residual mathematical risk is limited
to the explicitly deferred analytic and existence results above; compilation
does not validate those later claims.

## Cleanup and worktree state

Kept intentionally: the integrated P47 candidate, its quarantine archive and
extraction, and this review.  All pre-existing modified and untracked work was
preserved.  No manuscript file was changed; no commit, push, dependency
update, archive build, or dependency fetch was performed.
