# P50 — faithful normal tracial state on the von Neumann corner

## Context declaration

- **Source basis:** `main.tex:1265-1417`.

## Plan alignment

- **Package and lane:** `P50`; Lane `G`.
- **Predecessors:** `P49` and `P49C`, integrated and locally audited before submission.
- **Gate discharged:** extend `tau_q` to `q M_Gamma q` and prove it is a
  faithful normal finite tracial state under the exact required hypotheses.
- **Forbidden downstream claims:** no fullness, no statement about every central
  summand, no global trace/weight, and no final type-III exclusion.

## Mathematical target

Create only `AristotleCandidates/NormalFaithfulCornerTrace.lean`. Define the
corner functional induced by P49 in the represented von Neumann corner. Use the
proved P49C bounded compressed approximants and bounded product convergence to
prove cyclicity on all of `q M_Gamma q`. Prove positivity and unitality directly;
prove normality from the vector-functional realization; and prove faithfulness
from the manuscript's dense-vector/commuting-complement argument. The conclusion
must be a faithful normal finite **tracial state**, not merely a weight.

The exported P50 theorem must instantiate
`CompatibleFiniteCodespaceSystem.finite_corner_trace` from P49. Concretely, it
must take the compatible finite-codespace system, its decreasing projection
tower, and the norm-density inclusion of the represented C-star algebra into
the closure of the finite-stage ranges, identify `q` with that tower's
`limitProj`, and derive C-star-level `CornerTracialOn` by applying P49. An
internal abstract helper may accept a `CornerTracialOn` argument, but the main
P50 conclusion may not expose `cstar_tracial` (or an equivalent cyclicity
field) as an auxiliary assumption.

## Auxiliary assumptions

List all representation, support, commutation, cyclicity-of-the-global-vector,
and dense-vector premises explicitly; do not use a global trace. Bicommutant or
Kaplansky density may not remain as auxiliary assumptions because P49C proves them.
The norm-density premise required by P49 may remain explicit. Traciality or
cyclicity of the compressed C-star functional may not remain explicit: it must
be derived from P49 in the exported theorem.

## Files and imports

Create only `AristotleCandidates/NormalFaithfulCornerTrace.lean`; import P49,
P49C, and the checked C-star/GNS infrastructure as needed.

## Acceptance criteria

`lake build AristotleCandidates.NormalFaithfulCornerTrace` succeeds without
forbidden declarations. Positivity, normalization, traciality, normality, and
faithfulness must be proved under the explicit manuscript specialization data;
the response must name every remaining non-analytic premise. Acceptance also
requires a checked declaration whose assumptions include P49's finite-stage
system and density input and do **not** include a supplied `CornerTracialOn`,
trace-cyclicity field, bicommutant theorem, or Kaplansky-density interface.
