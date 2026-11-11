# P21 — one-qubit positive state and GNS datum

## Context declaration

- **Source basis:** `main.tex:1927-1931`

## Mathematical target

Create only `AristotleCandidates/OneQubitPositiveGNSData.lean`.

For the concrete one-qubit matrix algebra, package the pure ket-zero state and
the normalized trace as Mathlib positive unital linear functionals suitable for
`PositiveLinearMap.GNS`. Prove the corresponding basic GNS data/representation
can be formed, reusing Mathlib's existing GNS construction rather than
reconstructing it. If a full packaged `PositiveLinearMap` is impractical in the
pinned API, return the strongest compiling finite statement and document the
precise API obstruction.

## Auxiliary assumptions

None beyond the concrete finite one-qubit matrix algebra and Mathlib's existing
order/C-star instances. This is a finite infrastructure result, not an infinite
product-state theorem.

## Files and imports

Use `Formalization.QubitMatrixState`, `Formalization.SingleQubitPauli`, and
`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` as needed. Do not modify
existing files.

## Acceptance criteria

- `lake build AristotleCandidates.OneQubitPositiveGNSData` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- No spatial tensor-product, normality, factor-type, trace-weight, or infinite
  GNS claim is made.
