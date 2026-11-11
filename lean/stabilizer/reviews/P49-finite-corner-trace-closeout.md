# P49 closeout review — finite-stage trace and compressed quasi-local corner

## Decision

**Status: partial; queue must halt.**

The Aristotle result contains a technically sound-looking, conditional candidate
module, but it is not accepted or integrated.  The packet's required source
declaration is `main.tex:1196-1335`, while the candidate explicitly attributes
its finite-stage cyclicity and codespace-density identities to the manuscript.
Those identities occur at `main.tex:1133-1191`: in particular, the vector
fixing calculation is at lines 1133-1148, the functional is stated at
1150-1158, and finite-stage cyclicity and `eq:local_traciality` are at
1161-1191.  Lines 1196-1335 begin only with the bounded strong-limit passage
and then the C-star and von Neumann extensions.  Thus the packet does not give
the exact source locator required for all of its manuscript-derived claims.

Changing the packet or candidate locator would be a scope/policy edit outside
this bounded closeout.  The candidate remains only in the response quarantine;
the live working tree was not given `AristotleCandidates/FiniteCornerTrace.lean`.

The downloaded raw response record is
`aristotle_responses/P49-finite-corner-trace.tar.gz` (SHA-256
`17ceca9683eb286ebd136fb5fc2238f97fb077f2d1f73dacff93ff548ebe5473`), extracted
without a build, update, or dependency fetch at
`aristotle_responses/P49-quarantine/aristotle-stabilizer_two_lane_p49-gizp5x2z_aristotle/`.
Its candidate module has SHA-256
`38d4cbb58104d88f9830aa6b73846d6309f497f48b4140f762a2f031343be487`.

## Exact declarations and assumptions reviewed

The quarantined module declares, under complex Hilbert-space assumptions, the
following scoped results:

- `tauVec`, `compressL`, and `cornerTau`, with
  `cornerTau_star_mul_self`, `cornerTau_nonneg`, `cornerTau_one`, and
  `compressL_mem_corner`;
- `trace_density_sandwich_comm`, `stabilizerCodeDensity`,
  `trace_stabilizerCodeDensity`, `trace_groupAverage_eq`, and
  `posSemidef_smul_of_isIdempotent`;
- `FiniteCodespaceSystem`, `CompatibleFiniteCodespaceSystem`, and the derived
  `FiniteCodespaceSystem.stageProj_apply_self`,
  `FiniteCodespaceSystem.stage_cyclic`, and
  `CompatibleFiniteCodespaceSystem.trace_density_incl`;
- `tendsto_tauVec_sandwich`, `cornerTau_cyclic_of_stage`,
  `CornerTracialOn.closure`,
  `cornerTracialOn_quasilocalCStarAlgebra`, and the packaged conditional
  theorem `CompatibleFiniteCodespaceSystem.finite_corner_trace`.

The candidate's named auxiliary data are explicit: finite stage star
representations; hermitian idempotent code projections; densities of the form
`weight n • codeProj n` with trace one; the vector-state identity; compatible
stage inclusions; the P48 decreasing-projection-tower premise; and a
norm-density inclusion into the closure of finite-stage ranges.  No normality,
faithfulness on the von Neumann corner, fullness, finiteness of `q`, global
weight, or type-III conclusion is declared.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | In the live project's Lean environment, the quarantined module type-checks.  Its conditional finite-stage/corner-C-star statements compile, and the four sampled key declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. |
| partial | The Lean result is a conditional finite-stage and norm-closed quasi-local statement, not a proof of a trace on `q M_Gamma q`.  More importantly, its source-backed presentation needs the packet locator expanded to cover `main.tex:1133-1191`; that correction is not made in this closeout. |
| blocked | Acceptance is blocked by the source-locator mismatch.  P50's separate Kaplansky-density/normality passage remains unaddressed, as required. |
| failed | No Lean compilation or forbidden-declaration failure was found.  The task fails acceptance solely on the mandatory source-authority/context requirement. |

The packet's mathematical target is therefore **not accepted at its stated
manuscript-facing scope**, despite the successful conditional Lean check.

## Plan alignment

- **Package and lane:** P49, Lane G — correct.
- **Predecessors:** P47 and P48 are locally integrated and audited.  Their live
  SHA-256 values match the corresponding files in quarantine:
  `c55831ac16d3dec3d471c25c24159a5c22c79dff1460c586830eadda27da57d8`
  (P47) and
  `190af007e460f439360a0e195c6458e23f0aa5146009cb7f6b40ece2ea6b2386`
  (P48).
- **Permitted gate:** the candidate addresses only finite-stage cyclicity and
  its norm-closed compressed quasi-local extension, with explicit finite
  codespace density data.  This is the P49 gate.
- **Forbidden downstream claims:** respected in the candidate.  The scan found
  no theorem asserting normality, faithfulness, finiteness/fullness, a global
  trace/weight, Kaplansky density, a double-commutant theorem, or central
  type-III exclusion.

## Verification

- `lake env lean <quarantined FiniteCornerTrace.lean>` — passed, run from the
  already-built live project; no build, update, or fetch was run in quarantine.
- `lake build AristotleCandidates.CenterFiniteProjectionCore AristotleCandidates.GeneralLatticeProjectionTower Formalization` — passed.
- `lake build` — passed.
- `#print axioms` for `finite_corner_trace`, `stage_cyclic`,
  `tendsto_tauVec_sandwich`, and `CornerTracialOn.closure` — only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scans of the candidate and its direct
  project imports — no executable `sorry`, `admit`, user `axiom`, `opaque`,
  `unsafe`, `implemented_by`, or `native_decide` declaration.
- `git diff --check` — passed.

## Adversarial review

No Lean-term defect was found in the reviewed route: the strong-limit argument
uses `p_n Omega = Omega` to reduce the product limit to pointwise convergence,
and the C-star extension uses continuity on the product closure.  The
acceptance-blocking defect is provenance, not compilation: the declared source
range omits the exact finite-stage clauses the candidate claims to formalize.
Compilation and axiom inspection cannot repair that source mismatch or prove
the later von Neumann-algebraic conclusions.

## Cleanup and worktree state

Kept intentionally: the ignored raw archive and quarantine extraction, for the
supervisor's inspection.  Not integrated: `FiniteCornerTrace.lean`.  Preserved
unchanged: the pre-existing untracked P49A candidate and its closeout review.
No manuscript file was changed, and no commit, push, remote submission,
dependency update, archive build, or dependency fetch was performed.
