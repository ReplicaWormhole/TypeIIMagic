# P60 closeout review — full-corner semifinite weight

## Decision

**Status: partial and blocked; do not advance Lane G.**

The exact archive
`aristotle_responses/P60-full-corner-semifinite-weight-94c2fd67-fdc0344a.tar.gz`
was extracted only into its task-specific quarantine directory.  Its SHA-256 is
`d52b56d1d7dcf36a90e96e89db6037aee25fa50cd82b36d7e68bf6ebdcade81b`.
Only the packet-authorized candidate
`AristotleCandidates/FullCornerSemifiniteWeight.lean` was integrated into the
live tree; its quarantine and live SHA-256 is
`1a1d0a592a2d2445d3a3905104f90b1214bb9bb3d3d36e5acc4750811b4a598b`.
No build, update, or dependency fetch was run in quarantine.

The candidate compiles and contains a substantial conditional construction,
but the packet's stated mathematical target is not fully met. The only
acceptance blocker is the mismatch between its compression certificate and
standard positive-cone semifiniteness; the P51 predecessor correction is
recorded below.

## Exact declarations and assumptions

The candidate defines `srcProj`, `rngProj`, `partialProj`, and the explicit
comparison-family structure at lines 110–145.  Its assumptions are:

- `ComparisonFamily M q v`: `v n ∈ M`, idempotent source projections below
  `q`, pairwise orthogonal range projections, strong convergence of the finite
  range sums to `1`, and `srcProj v 0 = rngProj v 0 = q` (lines 128–145);
- P50U's `IsFaithfulUltraweakNormalTracialCorner M q Ω`; and
- `q Ω = Ω` for faithfulness (the exported theorem at lines 1123–1133).

The global definition is `globalWeight` (lines 280–290), the series of
`ENNReal.ofReal` transported corner vector traces.  The principal proved
declarations are `globalWeight_add`, `globalWeight_smul`, and
`globalWeight_mono` (lines 352–385); `globalWeight_tracial` (lines 494–524);
`globalWeight_faithful` (lines 540–601); the ultraweak and strong
monotone-supremum certificates
`globalWeight_iSup_of_ultraweakTendsto` and
`globalWeight_iSup_of_stronglyTendsto` (lines 648–705 and 672–705);
`globalWeight_partialProj` and `globalWeight_corner` (lines 731–833); and
`globalWeight_semifinite` (lines 903–926).  These are collected in
`IsGlobalFaithfulNormalSemifiniteTrace` and
`full_corner_global_semifinite_weight` (lines 1071–1133).

The missing comparison theorem is not silently assumed: the reduction
`exists_comparisonFamily_of_orthogonal_decomposition` (lines 942–1001) still
requires the orthogonal decomposition and Murray–von Neumann comparison data.
The P51 wrapper `full_finite_corner_globalized_weight` (lines 1158–1175) also
requires the full P51 input data and an explicit comparison family.

## Classification

| Classification | Result |
| --- | --- |
| proved | The extended-positive series definition; the displayed additivity, positive homogeneity, traciality, faithfulness, finite-partial-sum, corner-restriction, and monotone-supremum certificates compile from explicit premises. |
| partial | The exported normality statement is a project-local quadratic-form/sequence certificate: it does not explicitly require positive elements or state the full standard normal-weight interface. |
| partial | The declaration named `globalWeight_semifinite` proves finite compressions by an increasing strongly exhaustive family, but it does not state the standard semifiniteness condition on the positive cone (finite-weight positive subelements/order-density for every positive element). Its final claim “hence ... semifinite” is therefore stronger than the declaration actually establishes. |
| corrected | P51 is accepted in `reviews/P51-full-finite-corner-central-exclusion-recovery.md`; the original provenance objection consulted a superseded closeout. |
| failed | None as a Lean compilation artifact; the candidate itself is not a failed build. |

The packet's mathematical target is therefore **not actually met at its stated
scope**.  The candidate recovers a useful conditional weight-series and several
valid laws, but it does not discharge the standard semifiniteness gate.

## Provenance correction — 2026-08-08

The predecessor objection in this review is superseded.  It consulted the
historical rejected P51 closeout rather than the later accepted recovery
`reviews/P51-full-finite-corner-central-exclusion-recovery.md`, whose decision
is `advance`.  P51 is an accepted predecessor.  The P60 halt remains correct
solely because the candidate does not yet prove standard positive-cone
semifiniteness.  P60R is the approved focused recovery packet; it may revise
the candidate in place but must not weaken that missing theorem to a
compression-only certificate.

## Plan alignment

- **Package and lane:** P60, Lane `G` optional strengthening — declared lane is
  correct.
- **Predecessors:** declared `P51`, `P50U`, both locally accepted in their
  recovery/closeout reviews. The original P51 provenance objection is
  superseded by the correction above.
- **Permitted gate:** globalize a full finite corner to a faithful normal
  semifinite weight under explicit comparison/countability hypotheses.  The
  candidate reaches a conditional series construction and partial law
  certificates, but not the standard semifiniteness conclusion.
- **Forbidden claims:** respected.  It does not infer a global weight from
  fullness alone, does not prove a direct-integral theorem, and makes no
  Lane-H factorization or factor claim.

## Verification

All Lean checks were run only in the already-built live project:

- `lake build AristotleCandidates.FullCornerSemifiniteWeight` — passed;
- broader relevant build of P60 and P49–P51/P50U dependency modules — passed;
- `lake build` — passed with zero new jobs;
- `#print axioms` for `full_corner_global_semifinite_weight` and
  `full_finite_corner_globalized_weight` — only `propext`, `Classical.choice`,
  and `Quot.sound`;
- forbidden-placeholder scan over P60 and its direct dependency chain — no
  executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` declaration (the only hit was
  negative-scope prose in P49C);
- `git diff --check` — passed.

Compilation and axiom reports do not establish the missing standard
semifiniteness interface.

## Adversarial review

Artifact types: math, code, computation, and workflow.  The review checked the
comparison-family fields, the construction of `globalWeight`, the exported
theorem signatures, the normality hypotheses, the semifiniteness declaration,
the predecessor audit, and the forbidden-claim boundary. The remaining
acceptance-blocking finding is the mismatch between the claimed standard
semifiniteness and the compression certificate; the P51 provenance finding was
subsequently corrected.

## Cleanup and remaining state

Kept intentionally: the exact archive, its task-specific quarantine
extraction, the integrated P60 candidate, and this review.  All unrelated
modified and untracked files were preserved.  No manuscript file was changed;
there was no commit, push, new Aristotle submission, archive build, dependency
fetch, or destructive cleanup.

The queue has not advanced. P60R will preserve the accepted P51/P50U
predecessors and prove a genuine standard positive-cone semifiniteness theorem;
the current compression result remains a local supporting certificate.
