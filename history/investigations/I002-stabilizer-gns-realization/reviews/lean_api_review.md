# Lean/mathlib API review: finite stabilizer, strong support, and trace layer

**Final verdict: APPROVED.**  The reviewed public API has a checked path from
finite self-adjoint group averages, through a nested/increasing finite-subgroup
sequence and a constructed strong limit, to the existing GNS/corner result.
The new finite-dimensional trace lemma is correctly separate: it proves a
local-support nonvanishing criterion under its stated tracelessness hypothesis
without silently constraining the general GNS/corner theorem to finite
dimension.  No
project-local axiom, placeholder, unsafe declaration, or API weakening was
found.

This review covers the snapshot of the following files whose SHA-256 digests
are recorded below:

| File | SHA-256 |
|---|---|
| `FiniteFiber/FiniteStabilizer.lean` | `34f4d68d9eef9d418998e15806a115391f6802b37e24d802da99cf69762d9ab4` |
| `FiniteFiber/FiniteStabilizerTrace.lean` | `4c6094ffd1ec99937b5ccb9250500c43a55816e524de71ed82249f945e102574` |
| `FiniteFiber/StabilizerSequence.lean` | `95ff99d7b82a70f3c2c588b8871b8b17af3497f17e1423c88da75a3742d4e789` |
| `FiniteFiber/StrongSupport.lean` | `7c691412167940bac1f50bda2b4e8ca8a31b1cd3b7170773316ca9b900e75d6e` |
| `FiniteFiber/StabilizerFiniteFiber.lean` | `13412ab9c70650f8850c75d700c76b5ed02f21b1b05420d67b5d78728ef78951` |
| `FiniteFiber.lean` | `6b74f343c24d41bc1dff94198812b642d1fd11b0d4f5cac22f7efbe84cf38a09` |
| `tests/AxiomAudit.lean` | `d7d1d381cda33c1e70937901f7aab979fe5cf70fbe2c338773e6954a3c5229c7` |

## Findings

No blocking or correctness finding.

## Public API and mathematical-coherence audit

| Layer | Checked result | Audit result |
|---|---|---|
| Finite group average | `SelfAdjointFiniteGroupAction.average` normalizes the finite sum by `|G|^{-1}`; `average_isIdempotent` and `average_isSelfAdjoint` give `average_isStarProjection` (`FiniteStabilizer.lean:39-98`). | Correct.  `Fintype.card G` is nonzero because `G` is a group, and the proof uses the left/right bijections of finite-group multiplication.  The self-adjoint action hypothesis is deliberately strong enough for the claimed projection statement; no unproved Pauli realization is smuggled in. |
| Nested stabilizers | `restrict_average_isSubprojection_of_le` proves that, for `S <= T`, the average for `T` is below the average for `S` (`FiniteStabilizer.lean:245-254`). | Correct orientation: adding constraints decreases the common-fixed-space projection.  The two equations of `IsSubprojection` are supplied, rather than a one-sided operator inequality. |
| Finite-dimensional trace | `average_trace` assumes `[FiniteDimensional C H]` and explicitly supplied `htraceless` away from the group identity; `average_ne_zero_of_traceless` additionally assumes `Module.finrank C H != 0` (`FiniteStabilizerTrace.lean:21-78`). | Correct scope and normalization: the identity contribution is `finrank`, all other summands vanish by the displayed hypothesis, and a nonzero trace rules out a zero average.  This conditional local criterion is not an input to the global GNS conclusion; it does not claim to prove Pauli tracelessness, exclude phase conventions such as `-I`, or derive the qubit dimension formula. |
| Nested/increasing finite-subgroup sequence | `stabilizerAverageSequence_decreasingProjectionSequence` turns finite subgroup inclusions and membership of represented stabilizers in `M` into a `DecreasingProjectionSequence`; fixed-vector and nonzero-support helpers retain their exact hypotheses (`StabilizerSequence.lean:27-74`). | Correct.  The local `[forall n, Fintype (S n)]` instance is an explicit parameter, not a global/orphan instance.  Nonzero local supports require either a common nonzero fixed vector or the separate trace criterion; neither is overclaimed. |
| Canonical strong support | `decreasingProjectionStrongLimit p` is `1 - P_closure(union_n (range (p n))^perp)`, with a direct pointwise strong-convergence proof (`StrongSupport.lean:41-86`). | Correct construction for decreasing orthogonal projections: the orthogonal complements increase, so its complement projects onto the intersection of the decreasing ranges.  The proof derives membership in `M`, idempotence, self-adjointness, and common-fixed-vector preservation rather than taking the strong limit as an input (`:88-210`). |
| Stabilizer-to-fiber composition | The explicit and canonical entry points return `SupportCornerConclusion`, `IsSemifinite M`, and the exact witness `z * q` (`StabilizerFiniteFiber.lean:29-130`). | Correctly preserves the visible `GNSOrbitConditions` input.  The canonical theorem removes only the separate strong-convergence hypothesis because the strong limit has now been constructed; it does not pretend to construct the GNS orbit, corner trace, or full stabilizer realization. |

The canonical public entry point has exactly the intended support:

```text
stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit
  A S hmem hmonotone hfix C
  : SupportCornerConclusion M
      (decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) xi
```

The associated central-witness theorem was independently type-checked at its
full conjunction: `z * q` is finite, nonzero, and a subprojection of every
specified nonzero central projection `z`.  A separate consumer check also
type-checked both finite-dimensional trace theorems at their advertised
`FiniteDimensional`, `finrank != 0`, and nonidentity-tracelessness hypotheses.

## Imports, typeclasses, and axiom audit

The actual new import direction is acyclic:

```text
FiniteStabilizerTrace -> FiniteStabilizer -> Basic
StrongSupport -> Basic
StabilizerSequence -> FiniteStabilizer + StrongSupport
StabilizerFiniteFiber -> GNSOrbit + StabilizerSequence
FiniteFiber -> public re-export of all layers
```

The trace layer has no downstream dependency in the support/fiber theorem; this
is desirable because its finite-dimensional hypotheses should not constrain the
general Hilbert-space/GNS theorem.  `FiniteFiber.lean` re-exports the new trace
API and the umbrella build succeeds.

The source scan found no declaration of `axiom`, `sorry`, `admit`, `opaque`,
`unsafe`, or `implemented_by`.  There are intentional `noncomputable`
definitions for finite averages, subgroup restriction/sequence construction,
the Hilbert-space strong-limit projection, and the finite-dimensional operator
trace.  Those definitions use ordinary classical choice where required; they
are not placeholders or hidden project axioms.

`tests/AxiomAudit.lean:11-38` audits the load-bearing I001/I002,
strong-limit, finite-group-average, trace, stabilizer-sequence, and canonical
end-to-end theorems.  Every printed dependency set contains only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.  The supplemental
consumer check printed the same set for the initially unaudited public helpers
`average_isIdempotent`, `average_isSelfAdjoint`,
`average_ne_zero_of_forall_fix`, `stabilizerAverageSequence_ne_zero`, and the
explicit (noncanonical) support/canonical-witness entry points.

## Verification

All commands ran from `formalization_finite_fibers/` and exited successfully:

```text
lake build FiniteFiber.Basic
lake build FiniteFiber.TracialCorner
lake build FiniteFiber.FiniteFibers
lake build FiniteFiber.FiniteStabilizer
lake build FiniteFiber.FiniteStabilizerTrace
lake build FiniteFiber.StrongSupport
lake build FiniteFiber.StabilizerSequence
lake build FiniteFiber.VectorCorner
lake build FiniteFiber.GNSOrbit
lake build FiniteFiber.StabilizerFiniteFiber
lake build
lake env lean tests/AxiomAudit.lean
```

The umbrella build completed with 2729 jobs.  The `AxiomAudit` output and both
no-file Lean consumer checks contain only `propext`, `Classical.choice`, and
`Quot.sound` for their audited declarations.

## Adversarial closeout and residual boundary

The review searched specifically for reversed subgroup order, hidden
finite-dimensional assumptions in the general theorem, an unconstructed or
arbitrary strong-limit operator, missing central-witness clauses, orphan
instances, cycles, and project-local axioms.  None was found.

This approval is limited to the stated formal interfaces and their Lean proofs.
It does not establish a tensor-product Pauli realization, nonidentity Pauli
tracelessness in a chosen phase convention, a qubit-dimension/rank formula, an
infinite-lattice stabilizer-state/GNS construction, or the analytical
corner-traciality and dense-orbit inputs.  Those remain explicitly displayed
hypotheses or separate realization tasks, as they should.
