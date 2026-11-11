# P60 — optional global semifinite weight from a full finite corner

## Context declaration

- **Infrastructure only:** optional strengthening beyond the Lane-G manuscript
  conclusion; this packet makes no claim that the manuscript requires it.

## Plan alignment

- **Package and lane:** `P60`; Lane `G` optional strengthening.
- **Predecessors:** `P51`, `P50U`, both integrated and locally audited before
  submission.
- **Gate discharged:** globalize a full finite corner to a faithful normal
  semifinite weight under exact comparison/countability hypotheses.
- **Forbidden downstream claims:** no claim that P51 already supplied a global
  weight, no direct-integral theorem, and no Lane-H factorization.

## Mathematical target

Create only `AristotleCandidates/FullCornerSemifiniteWeight.lean`. Use P51's
full finite corner and P50U's literally ultraweak-normal faithful tracial
corner state. Under an explicit normalized countable comparison family of
partial isometries whose source projections lie below `q`, whose pairwise
orthogonal range projections sum strongly to `1`, and whose distinguished
zeroth member has source and range projection `q`, define the ambient
extended-positive trace/weight on the positive cone with values in `ℝ≥0∞` by
the corresponding monotone series of transported corner traces. Develop the
smallest project-local extended-positive-weight API required when pinned
Mathlib does not provide one.

Prove, from the displayed construction, additivity, positive homogeneity,
traciality, faithfulness, normality in the standard weight sense (preservation
of suprema of increasing positive nets/sequences at the level supported by the
developed API), and semifiniteness. The global extended-valued weight is not a
bounded linear functional, so do not define its normality as ordinary
ultraweak continuity on all of `M`; instead use P50U's ultraweak-normal bounded
corner functional to prove the monotone-supremum law. Also prove the value on
finite partial sums and that the global weight restricts exactly to the P50U
trace on `q M q`. Keep the separate theorem that fullness plus the exact
sigma-finite comparison theorem produces the required countable family; if
that comparison theorem itself is unavailable, take only the countable family
as a named hypothesis and do not claim it follows from fullness.

## Auxiliary assumptions

List every comparison-family, orthogonality, normalization, and convergence
premise explicitly. Normality,
faithfulness, traciality, and semifiniteness of the resulting weight are proof
targets, not permitted premise fields. The P50U corner normality theorem must
be used rather than the older WOT field name. Do not encode the desired global
weight itself as an interface field or axiom.

## Files and imports

Create only `AristotleCandidates/FullCornerSemifiniteWeight.lean`; import P51
and P50U.

## Acceptance criteria

`lake build AristotleCandidates.FullCornerSemifiniteWeight` succeeds without
forbidden declarations and reports the exact optional assumptions, the weight
definition, and the declarations proving its required weight laws. A
genuine missing comparison theorem may remain conditional; the weight laws may
not be replaced by a bundled assumption.
