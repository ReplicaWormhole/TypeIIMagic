# P49A closeout review — strong-operator closed concrete von Neumann algebras

## Decision

**Status: proved at the stated shared-infrastructure scope; queue may advance.**

The completed Aristotle project was downloaded as
`aristotle_responses/P49A-strong-operator-closed-von-neumann.tar.gz`
(SHA-256 `eb1bd6ddf17213aaf2ba0062f0fe7ba5b0851f4a46eff6ea655801bb3f70d56e`)
and extracted, without building or fetching dependencies, at
`aristotle_responses/P49A-extracted/aristotle-stabilizer_two_lane_p49a-p0kpdbli_aristotle/`.

Only the packet-authorized module
`AristotleCandidates/StrongOperatorClosedVonNeumann.lean` was integrated
into the live project. Its SHA-256 is
`dfb39289d895c16400e05145112320a42e6d1b61736859edbba153d02df0571a`
in both the quarantine snapshot and live project. The archive and extraction
remain raw response records. No manuscript file was modified.

## Exact declarations and assumptions

For `H` with `[NormedAddCommGroup H] [InnerProductSpace ℂ H]`, the module
defines the SOT synonym `StrongOperator.SOT H`, the pointwise predicate
`StrongOperator.StronglyTendsto`, and `StrongOperator.IsStronglyClosed`.
The exact core theorems are:

- `StrongOperator.stronglyTendsto_iff_tendsto_sot` and
  `StrongOperator.tendsto_sot_iff_forall_tendsto`;
- `StrongOperator.mem_centralizer_of_stronglyTendsto` and
  `StrongOperator.isStronglyClosed_centralizer`;
- under `[CompleteSpace H]`,
  `StrongOperator.coe_vonNeumannAlgebra_eq_centralizer`,
  `StrongOperator.mem_vonNeumannAlgebra_of_stronglyTendsto`, and
  `StrongOperator.isStronglyClosed_vonNeumannAlgebra`;
- `StrongOperator.StronglyTendsto.const_mul`,
  `StrongOperator.StronglyTendsto.mul_const`,
  `StrongOperator.StronglyTendsto.mul_of_bounded`,
  `StrongOperator.StronglyTendsto.mul_of_norm_le`, and
  `StrongOperator.StronglyTendsto.compress`.

The only analytic assumptions are the standard complex inner-product-space
structure, and completeness precisely where Mathlib's concrete
`VonNeumannAlgebra H` requires it. The joint-product theorem explicitly
requires a uniform norm bound on its left family. No analytic conclusion is a
structure field or axiom.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | All four packet conclusions are proved: SOT/net equivalence; strong closedness of arbitrary commutants; strong closedness of concrete von Neumann algebras using `M = M''`; and fixed-side plus uniformly bounded joint product stability. |
| partial | None within the stated P49A infrastructure target. |
| blocked | Nothing blocks the stated gate. The analytic double-commutant theorem and Kaplansky density remain separate P49B/P49C work. |
| failed | None. |

The mathematical target is met at its stated scope. In particular,
`isStronglyClosed_vonNeumannAlgebra` is a closure theorem for an already
given Mathlib concrete von Neumann algebra; it does not identify the strong
closure of an arbitrary star subalgebra with its bicommutant.

## Plan alignment

- **Package and lane:** P49A, Lane shared.
- **Predecessors:** P48 was previously integrated and locally audited. The
  candidate imports only the locally present supporting module
  `AristotleCandidates.BicommutantVonNeumannCore`; it imports no P49B, P49C,
  P50, or later package.
- **Permitted gate:** discharged: commutants and therefore Mathlib concrete
  von Neumann algebras are closed under strong-operator limits.
- **Forbidden downstream claims:** respected. No double-commutant equality
  with a strong closure, Kaplansky density, corner trace, faithfulness,
  finiteness, fullness, or type classification is asserted.

## Verification

- `lake build AristotleCandidates.StrongOperatorClosedVonNeumann` — passed.
- `lake build AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.GeneralLatticeProjectionTower AristotleCandidates.StrongOperatorClosedVonNeumann Formalization` — passed.
- `lake build` — passed in the already-built live project.
- `lake env lean /dev/stdin` with `#print axioms` for all four core
  conclusions and the compression corollary — each reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scan of the candidate — no executable
  `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` declaration. Search hits occur only
  in the file's explicit negative-scope documentation.
- Quarantine/live byte comparison, SHA-256 comparison, and `git diff --check`
  — passed.

## Adversarial review

No acceptance-blocking finding. The review checked that the centralizer proof
passes the commutation equation pointwise through the two strong limits; that
the concrete von Neumann result uses only its defining bicommutant equality;
and that the product proof has the required uniform norm bound on the left
factor. The remaining risk is exactly the deliberately deferred P49B/P49C
analytic identification and density work; compilation and axiom inspection do
not establish those results.

## Cleanup and worktree state

Kept intentionally: the integrated P49A candidate, its ignored quarantine
archive and extraction, and this closeout review. No commit, push, manuscript
change, dependency update, archive build, or dependency fetch was performed
locally. The new candidate and review are the only working-tree changes from
this closeout.
