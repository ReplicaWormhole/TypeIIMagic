# P50U closeout review — ultraweak topology and normality bridge

## Decision

**Status: accepted; shared infrastructure gate discharged and the queue may
advance.**

The exact task archive
`aristotle_responses/P50U-ultraweak-normality-bridge-665c01eb-43682f4c.tar.gz`
was extracted only into its task-specific quarantine directory.  No build,
update, or dependency fetch was run there.  The sole packet-authorized module,
`AristotleCandidates/UltraweakNormality.lean`, was reviewed and integrated
into the live project.  Its SHA-256 is
`ce7d0887c340c4f1209d8f88aa05a556b77f2763bb4d2ce0392ca768bb3b8997`
both in quarantine and live.

The packet's P50 predecessor is locally accepted: the recovery closeout records
the provenance repair for P49 and the accepted P50 recovery, whose live
`NormalFaithfulCornerTrace.lean` hash is
`2e9f93915721cf61978bd718ff972c3d0c26c8662efdc03fe7b91b65a627def2`.
Its exported `normal_faithful_corner_trace` invokes P49's
`D.finite_corner_trace` and P49C, rather than accepting cyclicity or density
as an interface field.

## Exact declarations and assumptions

The integrated module defines:

- `UltraweakCoeff`, with sequences `x : Nat -> H`,
  `y : Nat -> H ->L[C] C`, and
  `Summable (fun n => ||x n|| * ||y n||)`;
- `UltraweakCLM`, a type copy of bounded operators with the topology induced
  by all `UltraweakCoeff.eval` series;
- `UltraweakCLM.continuous_toWOT`, using
  `UltraweakCoeff.single x y` to make each WOT matrix coefficient an
  ultraweak generator;
- `IsUltraweaklyContinuous.of_wot`,
  `cornerTau_ultraweakContinuous`, and
  `IsFaithfulUltraweakNormalTracialCorner`; and
- `ultraweak_normal_faithful_corner_trace`, which exports P50's corner
  theorem with a literal ultraweak-continuity normality field.

No new premise of ultraweak continuity, normality, separability,
finite-dimensionality, supplied predual, supplied topology comparison, or
global trace/weight is added.  The final theorem is conditional exactly on
P50's explicit finite-codespace, decreasing-tower, represented-algebra,
commuting-complement, and dense-vector inputs.  These remain external to the
manuscript-specific stabilizer realization; P50U is infrastructure only.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The ultraweak topology is induced by arbitrary absolutely summable matrix-coefficient series, not aliased to WOT, SOT, or norm topology.  The checked identity `UltraweakCLM.continuous_toWOT` has the required direction, and composition proves the WOT-to-ultraweak continuity bridge. |
| partial | The exported corner theorem is conditional on the already explicit P50 hypotheses; it does not construct the represented stabilizer system, complement, or dense-vector premise from the manuscript. |
| blocked | None at the P50U infrastructure gate. |
| failed | None.  The candidate meets the packet's stated acceptance criteria. |

The packet's mathematical target is met at its stated infrastructure scope.

## Plan alignment

- **Package and lane:** P50U, lane `shared` — correct.
- **Predecessors:** P50 is integrated, compiled, and accepted in
  `reviews/P50-normal-faithful-corner-trace-recovery.md`; P49 and P49C are
  likewise accepted in the local recovery/closeout chain.
- **Gate discharged:** the standard ultraweak topology, the continuous identity
  from ultraweak to WOT, and the literal ultraweak-normal P50 export.
- **Forbidden downstream claims:** respected.  The module adds no traciality or
  faithfulness proof, finite-projection/fullness result, central type-III
  exclusion, global trace/weight, or Lane-H tensor-factor/factor theorem.

## Verification

All Lean commands were run in the already-built live project:

- `lake build AristotleCandidates.UltraweakNormality` — passed.
- `lake build AristotleCandidates.FiniteCornerTrace
  AristotleCandidates.NormalFaithfulCornerTrace
  AristotleCandidates.KaplanskyDensity AristotleCandidates.UltraweakNormality`
  — passed (one pre-existing non-blocking style suggestion in
  `KaplanskyDensity.lean:463`).
- `lake build` — passed.
- `#print axioms` for `continuous_toWOT`, `of_wot`,
  `cornerTau_ultraweakContinuous`, and
  `ultraweak_normal_faithful_corner_trace` — each lists only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-placeholder scan of P50U and its direct dependency chain — no
  executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` declaration; the sole scan hit is
  negative-scope documentation in P49C.
- `git diff --check` — passed.

## Adversarial review and cleanup

Artifact types: math and workflow.  The review checked the topology direction,
that arbitrary summable series occur in the definition, the one-term WOT
generator argument, the exact P50 export hypotheses, and the forbidden-claim
boundary.  No acceptance-blocking defect was found.  Compilation and axiom
reports do not establish the remaining manuscript-specific P50 premises.

Kept intentionally: the integrated P50U candidate, its exact raw archive and
quarantine extraction, and this review.  All pre-existing modified and
untracked files remain preserved; no manuscript file was changed, and no
commit, push, remote submission, archive build, update, or dependency fetch
occurred.
