# P28 — conditional product-factor and trace dichotomy

## Context declaration

- **Source basis:** `main.tex:1740-1752, 1945-1967`

## Mathematical target

Create only `AristotleCandidates/ProductFactorTraceDichotomy.lean`.

Define an explicitly supplied product von Neumann model interface for the
regional algebra after P27: a supplied normal regional/product equivalence, a
supplied spatial identification with a pure type-I sector times a mixed core,
and supplied core type/trace data. Prove formal transport of the stated
conclusion and encode the corrected dichotomy: finite pure sector permits the
supplied normalized tracial state; infinite pure sector must use a supplied
faithful normal semifinite trace/weight interface, not a tracial state.

## Boundary

Do not construct spatial tensor products, prove hyperfiniteness/type II1, or
prove nonexistence of normal tracial states on B(H). Those are supplied or
remain external. No gLU/refinement assumptions.

## Acceptance criteria

- `lake build AristotleCandidates.ProductFactorTraceDichotomy` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- All spatial/type/trace assumptions are named and the finite versus infinite
pure-sector distinction is explicit.
