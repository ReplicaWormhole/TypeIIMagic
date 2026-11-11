# Current formalization state

Imported on 2026-11-11. The saved supervisor decisions run through 2026-08-11.
Use `python3 scripts/typeiimagic.py status` for the current local runtime state.

## Finite-range support corner

[FiniteRangeTracialCorner.lean](lean/finite_fibers/FiniteFiber/FiniteRangeTracialCorner.lean)
contains the substantial completed corner argument:

- `FiniteRangeStabilizerSystem.tracial_cornerProjection_localVonNeumannAlgebra`;
- `FiniteRangeStabilizerSystem.faithful_cornerProjection_localVonNeumannAlgebra`;
- `FiniteRangeStabilizerSystem.cornerProjection_isFullProjection_localVonNeumannAlgebra`;
- `FiniteRangeStabilizerSystem.supportCornerConclusion_localVonNeumannAlgebra`.

The vector functional is tracial and faithful on the **support corner** `q M q`.
The projection `q` is nonzero and full. The result is stated for a supplied
finite-range stabilizer system, a quasilocal C-star completion `Q`, and an
extending global stabilizer state `W`. The bicommutant generation condition is
discharged for the canonical algebra. The existence of `Q` and `W` is not
constructed merely by writing this theorem.

[FiniteRangeNoTypeIII.lean](lean/finite_fibers/FiniteFiber/FiniteRangeNoTypeIII.lean)
then provides a nonzero finite projection in each nonzero central summand under
the same supplied-model inputs. This is not a formalized measurable direct
integral/fiberwise type-classification theorem. A trace on `q M q` is not a
tracial state on the entire fiber algebra.

The older README/HANDOFF files inside the imported packages are retained as
historical records; some describe earlier milestones. Read the actual FF22/FF23
source and their [integration reviews](history/investigations/I004-countable-pauli-quasilocal-realization/aristotle_responses/)
for the later accepted work.

## Later corner and two-lane development

[UltraweakNormality.lean](lean/stabilizer/AristotleCandidates/UltraweakNormality.lean)
exports `ultraweak_normal_faithful_corner_trace`, upgrading the P50 corner result
to an explicitly ultraweak-continuous normality statement. Its finite-codespace,
projection-tower, represented-algebra, commuting-complement and density premises
are stated in the theorem; they are not automatically supplied by the first
project. See [the accepted P50U review](lean/stabilizer/reviews/P50U-ultraweak-normality-bridge-closeout.md).

The further full-corner and positive-cone semifinite-weight infrastructure is
also preserved. The local-hyperbolic factorization route remains blocked:

| Packet | Recorded state | Exact record |
| --- | --- | --- |
| P57C | Partial result, halted; missing completed vacuum-ITP identification | [closeout](history/logs/20260811T085811Z-stabilizer_two_lane_p57c-07e097eb-codex-final.md) |
| P59B | Rejected candidate with eight `sorry`s and `sorryAx` | [closeout](history/logs/20260810T232204Z-stabilizer_two_lane_p59b-bb6c00a3-codex-final.md) |
| P59R | Waiting for P57C and P59B | [packet](lean/stabilizer/aristotle_tasks/P59R-regional-factor-transport.md) |
| P59T | Waiting for P59R | [packet](lean/stabilizer/aristotle_tasks/P59T-regional-trace-weight.md) |

Compiling a partial artifact such as `PureGNSFactor.lean` does not make it an
accepted implementation of its entire packet. Incomplete returned candidates
remain in historical archives rather than being silently integrated.

## Source versions

The manuscript in `sources/manuscript/` is the source snapshot at export time.
Historical task archives retain the manuscript/context available to those jobs;
line locators in an August packet may differ from the current snapshot. Review
source alignment before a resumed submission. No historical review has been
rewritten to claim verification against a newer manuscript.
