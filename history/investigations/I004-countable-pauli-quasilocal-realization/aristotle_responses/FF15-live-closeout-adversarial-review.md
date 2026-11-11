# FF15 live closeout adversarial review

## Decision

**Accepted at the packet's stated finite-region scope.**  The candidate
module is byte-identical to the live
`FiniteFiber/FiniteRegionFullPauliMultiplication.lean` and was reviewed only
from the designated quarantine extraction.  The raw response archive remains
at `FF15-finite-region-full-pauli-multiplication.tar.gz`; no archive build,
dependency update, or dependency fetch was run.

## Reviewed declarations and assumptions

**Proved.**

- `normalFormOneSiteMatrix_mul (p q : ProjectivePauliLabel)` proves the raw
  one-site `X`-then-`Z` multiplication law with phase
  `FullPauliWord.phaseEmbed ((p i).2 * (q i).1)`.
- `finiteRegionNormalFormMatrix_mul (F) (p q)` proves finite-region projective
  multiplication with the summed `finiteRegionNormalFormCocycle F p q`.
- `cocycle_eq_finiteRegionNormalFormCocycle (F) (u v) (hu : u.support ⊆ F)`
  identifies that exponent with `FullPauliWord.cocycle u v`.
- `fullPauliRegionMatrix_mul (F) (a b) (ha : a.label.support ⊆ F)` proves
  `fullPauliRegionMatrix F (a * b) = fullPauliRegionMatrix F a *
  fullPauliRegionMatrix F b`.  Only the left support premise is needed by the
  ordered cocycle, so this includes the requested local-local case.
- `fullPauliRegionMatrix_one` and
  `fullPauliRegionMatrix_negativeIdentity` give the identity and central
  negative-identity cases.

**Partial.**  The result is a finite-region operator identity only: no
support/local-algebra identification, multi-region representation, colimit,
norm closure, state, GNS, or finite-fiber conclusion is claimed.

**Blocked.**  No obstruction remains for FF15 itself.

**Failed.**  No failed declaration or verification check.  A stdin-only
pretty-printing diagnostic was unavailable; it did not affect builds or
axiom audits.

## Adversarial findings

No confirmed defect in the reviewed scope.

- The phase convention is preserved: the proof uses the existing
  `FullPauliWord.phaseEmbed` and cocycle, while its imports retain the checked
  one-site `X Z = -iY` convention.
- The theorem's one-sided support condition is explicit and is not misreported
  as a support/local-algebra equivalence.
- The candidate module and audit contain no `sorry`, `admit`, project `axiom`,
  `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration.
- Remote README, handoff, summary, manifest, and all other snapshot files were
  not adopted.

## Live checks

- `lake build FiniteFiber.FiniteRegionFullPauliMultiplication` — passed.
- `lake build` — passed (3,204 jobs), after importing the reviewed module from
  umbrella `FiniteFiber.lean`.
- `lake env lean tests/AxiomAudit.lean` — passed; the eight FF15 public
  declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean tests/FullPauliMultiplicationAxiomAudit.lean` — passed with
  the same axiom set.
- `git diff --check` — passed.

## Residual risk and cleanup

Lean compilation and axiom audits establish the named finite-dimensional
theorems, not later bridges.  Pre-existing dirty/untracked material was
preserved.  No commit, push, manuscript edit, or destructive cleanup occurred.
