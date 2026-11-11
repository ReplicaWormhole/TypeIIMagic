# P51 closeout review — full finite corner and central type-III exclusion

## Decision

**Status: blocked; do not advance Lane G.**

The completed Aristotle task was retrieved only from the exact archive
`aristotle_responses/P51-full-finite-corner-central-exclusion-10f2fe5c-f7631f0b.tar.gz`
(candidate SHA-256
`99294408c47f35f5716520b2a423fc399f6957bab6c632a184e5aa5daa75264c`) and
extracted only into its task-specific quarantine directory.  No archive build,
dependency fetch, update, or working-tree overwrite was performed.

The candidate is mathematically coherent at its conditional Lean scope and
typechecks through the live project environment, but it cannot be accepted at
the stated manuscript-facing packet scope.  The packet declares only
`main.tex:1456-1536` as its source basis.  Its required first gate, and the
candidate's theorem
`isFiniteProjection_of_faithfulNormalTracialCorner`, are explicitly the
finite-corner lemma at `main.tex:1426-1450` (the candidate cites
`main.tex:1425-1451`).  That source clause is outside the declared range.
Under `AGENTS.md`'s source-authority policy, a manuscript-derived claim needs
an exact source locator covering the claim; the declaration cannot silently be
expanded at closeout.  The candidate therefore remains quarantined and no
`AristotleCandidates/FullFiniteCornerCentralExclusion.lean` was integrated.

## Exact candidate declarations and assumptions

The quarantined candidate declares:

- `mem_corner_of_mvNEquiv_projLe`;
- `isFiniteProjection_of_faithfulNormalTracialCorner`, deriving
  `M.IsFiniteProjection q` from
  `IsFaithfulNormalTracialCorner M q Omega`;
- `isFull_of_dense_cyclic_vectors`, deriving fullness of `q` for
  `M = A''` from complement commutation, `q Omega = Omega`, and the dense
  span of vectors `b a Omega`;
- `central_summand_nonzero_finite_projection`, whose conclusion includes
  `z * q != 0`, `M.IsFiniteProjection (z * q)`, membership in
  `centralSummand M z`, and
  `IsFiniteProjectionIn (centralSummand M z) (z * q)`;
- `not_isTypeIIILike_centralSummand`; and
- `full_finite_corner_central_exclusion`, exporting the three claims from the
  P50 input data.

It adds no premise beyond the P50 input shape: compatible finite codespace
data, decreasing tower, represented norm-closed algebra and its finite-stage
density data, complement commutation `hB`, and dense-vector premise `hdense`.
It introduces no global trace or weight.  Its `IsTypeIIILike` is explicitly a
project-local set-relative obstruction predicate, not a new direct-integral or
factor-classification result.

## Classification

| Status | Finding |
| --- | --- |
| proved | Conditional Lean route: P50 corner faithfulness/traciality implies finiteness of `q`; fullness plus central compression yields the required nonzero finite `z*q` in each nonzero central summand. |
| partial | The proof is only conditional on the inherited P50 finite-system, closure, commutation, and density premises.  It does not itself realize these hypotheses for the manuscript stabilizer system. |
| blocked | The packet's source basis starts at line 1456, while its finite-corner gate requires the preceding manuscript lemma at lines 1426-1450.  This fails the required exact-locator contract. |
| failed | The packet cannot meet its stated manuscript-facing acceptance scope, so its candidate was not integrated and the queue has not advanced. |

## Plan alignment

- **Package and lane:** P51, Lane G — correct.
- **Predecessors:** P47 and the recovered accepted P50 are locally present and audited.  The live `NormalFaithfulCornerTrace.lean` SHA-256 is `2e9f93915721cf61978bd718ff972c3d0c26c8662efdc03fe7b91b65a627def2`, matching the P50 recovery record.
- **Permitted gate:** the candidate addresses only q-finiteness, q-fullness, and finite projections in nonzero central summands.  Its exact nonzero-finite-projection theorem is `central_summand_nonzero_finite_projection`.
- **Forbidden claims:** respected in the candidate: no direct integral, trivial center, global faithful normal semifinite weight/trace, or Lane-H tensor factorization.
- **Acceptance blocker:** the declared source basis does not cover the first permitted gate.  A corrected, separately prepared packet must explicitly cover `main.tex:1426-1450` (or label that finite-corner lemma as auxiliary infrastructure) before a new closeout may accept this route.

## Verification

- `lake build AristotleCandidates.CenterFiniteProjectionCore AristotleCandidates.NormalFaithfulCornerTrace` — passed in the live project (8057 jobs).
- `lake env lean aristotle_responses/P51-full-finite-corner-central-exclusion-10f2fe5c-f7631f0b-quarantine/aristotle-stabilizer_two_lane_p51-_l52ps0z_aristotle/AristotleCandidates/FullFiniteCornerCentralExclusion.lean` — passed, using the live project's already-built environment; no check was run inside the downloaded snapshot.
- Placeholder scan over the P47/P49--P50 live chain and the quarantined P51 candidate — no executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration found.
- `git diff --check` — passed.
- Adversarial review — source-scope mismatch confirmed against the authoritative manuscript: lines 1426-1450 establish the finite-corner result, while the packet begins at line 1456.  This is acceptance-blocking; no further semantic defect was found in the candidate's conditional route.

## Cleanup and worktree state

Kept: the supplied archive, its task-specific quarantine extraction, and this
halt review.  Not integrated: the P51 candidate module or any other archive
file.  The pre-existing modified P49/P50 packets and untracked candidate/review
files were preserved.  No manuscript file was changed; no commit or push was
made.

AUTOPILOT_ACCEPTED: no

AUTOPILOT_DECISION: halt
