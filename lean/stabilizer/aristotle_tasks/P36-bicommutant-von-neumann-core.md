# P36 — concrete bicommutant von Neumann core

## Context declaration

Infrastructure only: reusable Lean infrastructure; no manuscript claim.

## Mathematical target

Create only `AristotleCandidates/BicommutantVonNeumannCore.lean`.

Using `Mathlib.Analysis.VonNeumannAlgebra.Basic`, define the bicommutant
closure of a star subalgebra `S : StarSubalgebra ℂ (H →L[ℂ] H)` on a Hilbert
space as the concrete `VonNeumannAlgebra H` whose carrier is the double
commutant. Prove the basic order-theoretic facts that are available directly
from the centralizer API:

1. `S` is contained in its bicommutant;
2. the bicommutant operator is monotone;
3. the bicommutant of an already concrete von Neumann algebra is itself;
4. the construction is idempotent at the `VonNeumannAlgebra` level; and
5. membership in the generated algebra is characterized by commuting with the
   commutant.

Keep the distinction explicit between this algebraic double-commutant
construction and the analytic double-commutant theorem/strong or weak operator
closure. If an order statement is not supported by the pinned API, provide the
strongest compiling lemma and document the exact missing theorem instead of
axiomatizing it.

## Auxiliary assumptions

- `H` has the Hilbert-space structures required by Mathlib.
- The input is a star subalgebra of bounded operators.

## Boundary

No C*-completion, GNS construction, spatial tensor product, factor type,
hyperfinite classification, trace/weight, gLU, or refinement claim.

## Acceptance criteria

- `lake build AristotleCandidates.BicommutantVonNeumannCore` succeeds.
- no `sorry`/`admit`/user-declared axiom.
- no assertion that double commutant equals strong/weak closure unless proved
  from an existing theorem.
