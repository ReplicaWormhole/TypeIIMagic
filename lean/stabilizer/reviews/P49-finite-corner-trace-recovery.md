# P49 recovery review — finite-stage trace and compressed quasi-local corner

## Decision

**Status: accepted after a provenance-only repair; queue may advance.**

The original fail-closed review remains preserved in
`reviews/P49-finite-corner-trace-closeout.md`. It correctly halted P49 because
the packet and candidate declared `main.tex:1196-1335`, which omitted the
finite-stage vector-state and cyclicity clauses actually used by the module.

The source basis is corrected to `main.tex:1133-1261` in both
`aristotle_tasks/P49-finite-corner-trace.md` and the integrated
`AristotleCandidates/FiniteCornerTrace.lean`. This exact range contains:

- vector fixing and normalization at lines 1133-1148;
- the compressed vector functional and finite-stage cyclicity at lines
  1150-1191;
- the bounded strong-limit passage at lines 1193-1205; and
- the norm-closure C-star extension at lines 1207-1261.

Line 1262 begins the separate extension to the von Neumann corner, which is
deliberately excluded from P49 and remains the P50 gate. Thus the corrected
locator neither broadens the Lean theorem nor imports a downstream conclusion.

## Artifact identity and scope preservation

The quarantined candidate had SHA-256
`38d4cbb58104d88f9830aa6b73846d6309f497f48b4140f762a2f031343be487`.
The integrated candidate has SHA-256
`12cc9185a24773f85855bfc05ee779e997bf40f05abb2823e3352932ffff7111`.
After mechanically replacing only `main.tex:1196-1335` by
`main.tex:1133-1261`, the sole remaining byte difference is one terminal blank
line introduced by patch integration. No Lean declaration, theorem statement,
proof term, import, assumption, or namespace was changed.

The corrected packet has SHA-256
`251f2a0bec1737378f3c05b3d12fe61ad48a6588706f0b549bd973122ba62f95`.
The rejected closeout review is unchanged, with SHA-256
`b62be4793f9cc195c87db9278eebec7bbac7a25d2f2f4d8bb839f43e0e13831d`.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The conditional finite-stage cyclicity, compressed vector functional, strong-limit vector identity, and norm-closed C-star traciality compile in the live Lean project. |
| partial | This is not yet a normal or faithful trace on `q M_Gamma q`; those are P50 obligations. |
| blocked | Nothing blocks the P49 gate after correcting its exact source locator. |
| failed | None. The original failure was provenance-only and remains recorded in the rejected closeout. |

All auxiliary data remain explicit: finite-stage star representations,
hermitian idempotent code projections, scalar-multiple normalized densities,
the vector-state identity, compatible inclusions, a decreasing projection
tower, and a norm-density premise. No normality, faithfulness, finiteness,
fullness, global weight, or type-III conclusion is asserted.

## Verification

- `lake build AristotleCandidates.FiniteCornerTrace AristotleCandidates.CenterFiniteProjectionCore AristotleCandidates.GeneralLatticeProjectionTower` — passed.
- `lake env lean /tmp/P49AxiomAudit.lean` — passed; `finite_corner_trace`,
  `stage_cyclic`, `tendsto_tauVec_sandwich`, and `CornerTracialOn.closure`
  depend only on `propext`, `Classical.choice`, and `Quot.sound`; the temporary
  audit file was removed afterward.
- `lake build` — passed.
- Placeholder/forbidden-declaration scan of P49 and its two plan predecessors —
  no executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` declaration.
- `git diff --check` — passed.

## Adversarial review

No acceptance-blocking finding remains. The correction was checked against the
canonical manuscript line by line. The theorem scope is still strictly below
P50: it reaches only the norm-closed compressed quasi-local C-star algebra.
Compilation does not establish the later normality, faithfulness, finiteness,
fullness, or central type-III exclusion claims.

## Supervisor recovery

The supervisor state may record this review as a manual, audited recovery while
retaining the original closeout metadata as rejected history. P49 may be added
to the accepted package set, which permits P50 to start because P49C has also
been accepted. No remote result was cancelled or overwritten.

AUTOPILOT_ACCEPTED: yes

AUTOPILOT_DECISION: advance
