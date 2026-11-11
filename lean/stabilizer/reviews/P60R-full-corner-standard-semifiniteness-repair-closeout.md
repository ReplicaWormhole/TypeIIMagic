# P60R closeout review — standard positive-cone semifiniteness repair

## Decision

**Status: accepted at the packet's conditional optional-strengthening scope.**

The exact archive
`aristotle_responses/P60R-full-corner-standard-semifiniteness-repair-ae5ca7f3-9cf226e6.tar.gz`
was SHA-256 checked as
`b1aa1b1f547a45608fe338978bdd396a41326b7f755e2cb562b6fc7c06559306`
and extracted only to its named quarantine directory.  No build, update, or
dependency fetch was run in that dependency-free snapshot.  Only the
packet-authorized candidate `AristotleCandidates/FullCornerSemifiniteWeight.lean`
was integrated into the live project; its quarantine and live SHA-256 agree:
`15f0f528c5febebc96075f7174aafd34ec9ac98c541d8dd2f1373a135c230360`.
The archive's `ARISTOTLE_SUMMARY.md` remains a quarantined raw response record.

P60R closes the P60 acceptance gap without weakening the target.  Its central
theorem is `globalWeight_semifinite_positiveCone` (lines 1117--1124): for every
nonzero positive `x` in `M`, it produces a nonzero positive `y` in `M` with
`y <= x` and `globalWeight q Omega v y < top`.  This is the required standard
positive-cone semifiniteness assertion, not merely the old finite-compression
certificate.

## Exact declarations and assumptions

New local proved infrastructure is:

- `posSqrt`, `posSqrt_mul_self`, `posSqrt_mem`, and `posSqrt_ne_zero`
  (lines 981--1011), constructing the positive square root by Mathlib CFC and
  proving that it remains in the concrete von Neumann algebra;
- `compressedSub`, `compressedSub_isPositive`, `compressedSub_mem`,
  `compressedSub_le`, and `globalWeight_compressedSub_lt_top`
  (lines 1032--1093), for `x^(1/2) p_N x^(1/2)`;
- `exists_compressedSub_ne_zero` and
  `globalWeight_semifinite_positiveCone` (lines 1095--1124);
- `positiveCone` and the positive-cone structure
  `IsGlobalFaithfulNormalSemifiniteTrace` (lines 1297--1347); and
- the repaired exports `full_corner_global_semifinite_weight`
  (lines 1367--1383) and `full_finite_corner_globalized_weight`
  (lines 1409--1434).

The prior theorem is retained honestly as
`globalWeight_finite_compressions` (lines 924--953).  It is no longer claimed
to be standard semifiniteness by itself.

All global-weight results remain conditional on the explicit
`ComparisonFamily M q v` and P50U's
`IsFaithfulUltraweakNormalTracialCorner M q Omega`; faithfulness also uses the
explicit normalization `q Omega = Omega`.  The comparison family includes the
partial-isometry, source-below-corner, pairwise orthogonal-range, strong-sum,
and zeroth-term normalization premises.  No premise of positive square root,
factorization, order density, normality, traciality, faithfulness, or
semifiniteness was added.  The separate sigma-finite comparison theorem
producing this family from fullness is still not formalized (lines 1150--1160).

## Classification

| Classification | Result |
| --- | --- |
| proved | The square-root/factorization route, positivity, membership, order inequality, finite weight, and literal positive-cone semifiniteness theorem compile from the named assumptions. |
| proved | The exported weight-law structure is now restricted to `positiveCone M`; it includes the standard semifiniteness field and retains finite compressions separately. |
| partial | Normality is the existing locally developed monotone-supremum law for increasing ultraweakly convergent sequences in the positive cone, not a formalization of arbitrary nets or a predual-level normal-weight theory. |
| partial | The optional global theorem is conditional on `ComparisonFamily`; fullness alone is not proved to provide it. |
| blocked | None at the P60R packet gate.  The unformalized comparison theorem remains explicitly outside that gate. |
| failed | None. |

The packet's mathematical target is met at its stated conditional scope.

## Plan alignment

- **Package and lane:** `P60R`, Lane `G`, optional recovery — correct.
- **Predecessors:** `P51` and `P50U` are locally integrated and accepted in
  `reviews/P51-full-finite-corner-central-exclusion-recovery.md` and
  `reviews/P50U-ultraweak-normality-bridge-closeout.md`.  The P60 baseline was
  rechecked locally and is not used as a semantic predecessor.
- **Gate discharged:** standard positive-cone semifiniteness of the explicitly
  constructed extended-positive trace under the named countable comparison
  family.
- **Forbidden downstream claims:** respected.  The candidate neither derives
  the family/global weight from fullness alone nor claims a direct-integral
  theorem, a Lane-H factorization, or that finite compressions alone establish
  standard semifiniteness.  It makes no manuscript claim.

## Verification

All Lean checks were run only in the already-built live project:

- `lake build AristotleCandidates.FullCornerSemifiniteWeight` — passed
  (8,060 jobs; only the pre-existing non-blocking Kaplansky style suggestion at
  line 463).
- `lake build AristotleCandidates.FiniteCornerTrace AristotleCandidates.KaplanskyDensity AristotleCandidates.NormalFaithfulCornerTrace AristotleCandidates.UltraweakNormality AristotleCandidates.FullFiniteCornerCentralExclusion AristotleCandidates.FullCornerSemifiniteWeight` — passed.
- `lake env lean --stdin` with `#print axioms` for `posSqrt_mul_self`,
  `posSqrt_mem`, `globalWeight_semifinite_positiveCone`,
  `full_corner_global_semifinite_weight`, and
  `full_finite_corner_globalized_weight` — each lists only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The same live Lean check printed the literal type of
  `globalWeight_semifinite_positiveCone`, confirming the required nonzero
  positive order-below finite-weight conclusion.
- Forbidden-declaration scans of P60R and its direct Lean dependency chain —
  no executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide`; the sole dependency-chain lexical hit
  is negative-scope prose in `KaplanskyDensity.lean:41`.
- `git diff --check` — passed.

## Adversarial review

Artifact types reviewed: math, code, and workflow.  The review tested the
positive-cone domain, square-root membership in `M`, the nonzero compressed
subelement argument, the operator-order inequality, the use of traciality to
obtain finite weight, the distinction from the retained compression
certificate, the exported assumptions, predecessor provenance, and forbidden
claim boundary.  No acceptance-blocking defect was found.  Compilation and
axiom reports establish the Lean artifact from its hypotheses, not the missing
comparison theorem or an unconditional global weight for the manuscript.

## Cleanup and remaining state

Kept intentionally: the exact archive, its task-specific quarantine extraction,
the integrated P60R candidate, and this closeout review.  Pre-existing modified
and untracked project files remain preserved.  No manuscript file was changed;
there was no commit, push, new Aristotle submission, archive build, dependency
fetch, or destructive cleanup.
