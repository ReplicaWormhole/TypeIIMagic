# P42 — faithful regional theorem contract and source-gap audit

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1740-1752, 1915-2004`

## Mathematical target

Create only `AristotleCandidates/RegionalTheoremContract.lean`. Assemble the
proved conditional components from P38--P41 into one theorem contract for the
regional algebra. The theorem must list, in Lean fields, the exact finite
coordinate realization, C-star completion/alpha, state identity, normal
bicommutant transport, and product-factor assumptions it uses. Its conclusion
is the corrected factor/trace dichotomy only under those fields.

Also create a concise source-gap comment identifying which of these fields are
not provided by the cited manuscript. Do not convert a manuscript proof sketch
into an existence theorem by hiding its gaps in typeclass inference or axioms.

## Acceptance criteria

`lake build AristotleCandidates.RegionalTheoremContract` succeeds without
placeholders. The response must state whether the submitted snapshot proves a
manuscript-derived theorem or only a conditional theorem contract.
