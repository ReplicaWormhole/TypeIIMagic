# P?? — concise task title

## Context declaration

Use exactly one of the following:

- **Source basis:** `main.tex:<start>-<end>`
- **Infrastructure only:** explain the reusable Lean component and state that
  no manuscript claim is being formalized.

## Plan alignment

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.
Fill every field below; this is part of the prompt sent to Aristotle.

- **Package and lane:** `P??`; one of `G`, `H`, `shared`, or `reconnection`.
- **Predecessors:** list only packages already integrated and locally compiled,
  or `none` for a foundation package.
- **Gate discharged:** name the single gate from `PLAN.md` this package may
  discharge.
- **Forbidden downstream claims:** list the later conclusions this package may
  not state, assume, or package as an implicit consequence.

Do not treat a remote-completed package as a predecessor until its candidate
has been integrated and passed the local semantic audit. Do not infer a result
from a later package in the plan.

## Mathematical target

State the exact theorem or definition in ordinary mathematics, then give the
exact Lean declaration to produce. Do not state a stronger result than the
cited source clause.

## Auxiliary assumptions

List every assumption not explicitly supplied by the source basis. Mark the
result conditional when this list is nonempty. In particular, list any
completion, star-isomorphism, product-GNS, normality, spatial tensor-product,
factor-type, or trace hypothesis.

## Files and imports

Specify files Aristotle may edit or create and the pinned imports it should
use. Do not alter existing unrelated artifacts.

## Acceptance criteria

- The declared Lean target compiles with the project toolchain.
- No `sorry`, `admit`, or new axiom is introduced.
- The response reports the exact command run and remaining mathematical
  assumptions.
- The response confirms that the package obeyed its declared lane,
  predecessors, gate, and forbidden-downstream-claims boundary.
