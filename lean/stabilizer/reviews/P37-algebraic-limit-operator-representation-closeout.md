# P37 closeout review — algebraic-limit operator representation

## Decision

**Status: proved at the packet's stated conditional infrastructure scope.**

The reviewed module is `AristotleCandidates/AlgebraicLimitOperatorRepresentation.lean`.
It is byte-identical to the candidate in the quarantined Aristotle archive at
`aristotle_responses/P37-extracted/aristotle-stabilizer_hyperfinite-y537ze25_aristotle/AristotleCandidates/AlgebraicLimitOperatorRepresentation.lean`.
The archive was downloaded to `aristotle_responses/` and was never built,
updated, or used for dependency fetching.

P37 is explicitly **Infrastructure only**, so it makes no manuscript claim.

## Exact declarations and premises

For a preorder `ι` with `IsDirectedOrder ι` and `Nonempty ι`, a family of
complex semirings/star-rings/algebras `A`, a directed system of connecting
`StarAlgHom`s `f`, and a supplied complete complex inner-product space `H`,
the module declares:

- `StabilizerHyperfinite.algebraicLimitOperatorRep`:
  `DirectLimit A f →⋆ₐ[ℂ] (H →L[ℂ] H)`, from supplied
  `rho : ∀ i, A i →⋆ₐ[ℂ] (H →L[ℂ] H)` and the explicit compatibility premise
  `compat : ∀ i j (h : i ≤ j) x, rho j (f i j h x) = rho i x`.
- `algebraicLimitOperatorRep_of` and `algebraicLimitOperatorRep_of_apply`:
  the exact finite-stage operator and vector formulas.
- `algebraicLimitOperatorRep_stage_congr` and
  `algebraicLimitOperatorRep_congr_of_eq`: representative independence.
- `algebraicLimitOperatorRep_unique`: uniqueness among star-algebra maps with
  the same finite-stage values.
- `connecting_injective_of_stage_rep_injective`: stagewise injectivity of
  `rho` implies injectivity of every connecting map, using `compat`.
- `algebraicLimitOperatorRep_injective`: the induced limit representation is
  injective under the additional explicit premise
  `h_inj : ∀ i, Function.Injective (rho i)`.
- `QubitOperatorRepresentationData`, whose fields are the supplied dyadic
  stage representations and their compatibility with `qubitTensorPowerMap`,
  together with `limitRep`, `limitRep_of`, `limitRep_of_apply`,
  `rho_congr_of_eq`, `limitRep_unique`, and the conditional
  `limitRep_injective`.

The route uses the existing `algebraicLimitStarAlgHom` construction. No new
mathematical premise was silently added: faithfulness is expressly conditional
on stagewise injectivity; separate injectivity of the connecting maps is
derived rather than assumed.

## Scope classification

| Classification | Result |
| --- | --- |
| proved | The compatible algebraic direct-limit representation, finite-stage formulas, representative independence, uniqueness, and conditional faithfulness described above. |
| partial | None at P37's stated scope. |
| blocked | No blocking Lean/API issue for this algebraic construction. |
| failed | None. |

The packet's mathematical target is met only in this conditional algebraic
form. It does **not** construct an infinite tensor-product Hilbert space,
C-star norm/completion, operator-norm closure, GNS representation, bicommutant,
von Neumann closure, trace/weight, gLU, or refinement data.

## Adversarial review

No defect was found in the reviewed scope. In particular, the potentially
strong faithfulness claim is justified by Mathlib's `DirectLimit.induction₂`,
which puts two limit representatives into a common stage before applying the
explicit `h_inj` hypothesis. Representative-independence uses `compat` in the
correct orientation. The module does not introduce `sorry`, `admit`, a user
axiom, `opaque`, `unsafe`, `implemented_by`, or `native_decide`.

Residual risk: Lean compilation and the axiom audit validate this algebraic
interface, not the unformalized analytic/operator-algebraic continuation.

## Verification

- `lake build AristotleCandidates.AlgebraicLimitOperatorRepresentation` — passed.
- `lake build AristotleCandidates.AlgebraicLimitOperatorRepresentation Formalization` — passed.
- `lake build` — passed.
- `lake env lean /tmp/stabilizer_hyperfinite_p37_axioms.lean` — passed;
  all eight audited public declarations depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- `rg -n '\b(sorry|admit|axiom|opaque|unsafe|implemented_by|native_decide)\b' AristotleCandidates/AlgebraicLimitOperatorRepresentation.lean` — no matches.
- `git diff --check` — passed.

## Cleanup and worktree state

Kept intentionally:

- `AristotleCandidates/AlgebraicLimitOperatorRepresentation.lean`, the sole
  reviewed integration;
- `aristotle_responses/P37-algebraic-limit-operator-representation.tar.gz` and
  its extracted quarantine snapshot, preserving the raw remote response;
- this closeout review.

All pre-existing modified and untracked files were preserved. No manuscript
file was modified, and no commit or push was made.
