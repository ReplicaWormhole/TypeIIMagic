# P32 — finite pure/mixed product-state coherence

## Context declaration

- **Source basis:** `main.tex:1927-1944`

## Mathematical target

Create only `AristotleCandidates/FiniteProductStateCoherence.lean`.

Prove compatibility of the concrete finite pure/mixed qubit product states with
the dyadic finite-stage embeddings, including their Pauli-word expectation
formula after inclusion. Package the result as the compatible state family
needed for algebraic direct-limit state transport.

## Boundary

Use the existing explicit pure/mixed pattern and finite-stage embeddings. Do
not claim a C-star-continuous state, GNS factorization, normality, or an actual
regional-state identification. No gLU/refinement assumptions.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteProductStateCoherence` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The finite-stage compatibility and Pauli-word formula are explicit.
