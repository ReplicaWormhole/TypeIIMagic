# P25 — C-star completion interface for alpha

## Context declaration

- **Source basis:** `main.tex:1915-1924`

## Mathematical target

Create only `AristotleCandidates/CStarCompletionAlphaInterface.lean`.

Package the first analytic boundary after P23/P24. Given supplied unital complex
C-star source and target completions, supplied dense algebraic embeddings of
the two direct limits, and a supplied C-star star-algebra equivalence extending
P23's algebraic `alpha` on every finite-stage representative, prove the
extension is isometric and continuous (and so is its inverse), and that a
supplied continuous target functional/state pulls back continuously with the
expected finite-stage formula.

Reuse `CStarEquivExtension`, P23, P24, and `CStarTransport` where appropriate.

## Auxiliary assumptions

- the two C-star completions and their algebraic embeddings;
- density of each embedding;
- a supplied C-star star-algebra equivalence; and
- its exact extension formula for P23 finite-stage representatives.

All are explicit assumptions. Do not construct a C-star norm/completion from
the algebraic limit.

## Boundary

Do not claim normality, GNS equivalence, spatial tensor products, von Neumann
closures/bicommutants, quasi-equivalence, hyperfiniteness, factor type, or a
trace/weight. Do not use gLU, refinement, or layer-coherence.

## Acceptance criteria

- `lake build AristotleCandidates.CStarCompletionAlphaInterface` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The module clearly separates the supplied completion/extension from the
checked consequences.
