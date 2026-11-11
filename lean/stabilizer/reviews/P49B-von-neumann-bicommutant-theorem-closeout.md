# P49B closeout review - analytic von Neumann bicommutant theorem

## Decision

**Status: proved at the stated shared-infrastructure scope; queue may advance.**

The completed Aristotle project was downloaded as
`aristotle_responses/P49B-von-neumann-bicommutant-theorem.tar.gz`
(SHA-256 `6973bbc16ab59440f27f6b45b722ca8c482dbc7d35e724386cdd1d15cd550b96`)
and extracted without a build, update, or dependency fetch at
`aristotle_responses/P49B-quarantine/aristotle-stabilizer_two_lane_p49b-sn5_fvfw_aristotle/`.

Only the packet-authorized module
`AristotleCandidates/VonNeumannBicommutantTheorem.lean` was integrated.  Its
SHA-256 is `7f6101e5c55273dfc4a48661b0d4852183ac3e015a844764a7075e542f0fc3ce`
in both quarantine and the live project.  The archive and extraction remain
ignored raw response records.  No manuscript file was changed.

## Exact declarations and assumptions

For `H` with `[NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]`
and `A : StarSubalgebra ℂ (H ->L[ℂ] H)`, the module defines
`VonNeumannBicommutant.strongClosure` using Mathlib's
`PointwiseConvergenceCLM`/`StrongOperator.SOT` topology.  Its central theorem
declarations are:

- `VonNeumannBicommutant.mem_strongClosure_iff`, the exact arbitrary-finite-set
  strong-neighbourhood criterion;
- `VonNeumannBicommutant.exists_mem_approx_on_fin`, simultaneous approximation
  of every element of the bicommutant on a finite family of vectors;
- `VonNeumannBicommutant.bicommutant_subset_strongClosure` and
  `VonNeumannBicommutant.strongClosure_subset_bicommutant`;
- `VonNeumannBicommutant.strongClosure_eq_bicommutant`, namely
  `strongClosure (A : Set (H ->L[ℂ] H)) = Set.centralizer (Set.centralizer A)`;
- `VonNeumannBicommutant.strongClosure_eq_vonNeumannGenerated` and
  `VonNeumannBicommutant.strongClosure_eq_self_iff`.

Completeness is the only additional analytic premise beyond a complex inner
product space: it supplies the orthogonal projection onto the closed cyclic
subspace.  `StarSubalgebra` supplies the required unit, used to put the
amplified cyclic vector in that subspace.  No nondegeneracy hypothesis,
structure-field replacement, external theorem token, or user axiom is used.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The live Lean project proves both inclusions and the equality by finite amplification.  `ampOp`, `ampIn`, the matrix-entry commutant calculation, invariant-subspace projection commutation, and finite-family cyclic approximation are all local declarations in the integrated module. |
| partial | None within the stated P49B gate.  The theorem is abstract infrastructure, not a proof that any project-specific compressed quasi-local algebra satisfies a density hypothesis. |
| blocked | Nothing blocks the stated gate.  P49C remains required for bounded/unit-ball Kaplansky density, and P50 remains required for the corner trace/normality passage. |
| failed | None.  No compilation, axiom, placeholder, provenance, or scope failure was found. |

The packet's mathematical target is met: the result is about arbitrary finite
strong neighbourhoods and nets, not a sequential-closure substitute.  The
hard inclusion uses the usual diagonal finite amplification/cyclic-subspace
argument; the reverse inclusion uses P49A strong closedness of the commutant.

## Manuscript boundary

The packet declares source basis `main.tex:1269-1287`.  Those lines identify
the intended later use: extending from the compressed C-star algebra to the
von Neumann corner and requiring strong density before the Kaplansky step.
P49B is explicitly labelled **Lean infrastructure only** and makes no claim
that this manuscript density statement, the existence of its uniformly bounded
net, or its compressed-corner consequence has been formalized.  It provides
only the independently proved double-commutant tool.  In particular it does
not represent the Kaplansky assertion at `main.tex:1275-1281`; that remains
P49C work.

## Plan alignment

- **Package and lane:** P49B, lane `shared` - correct.
- **Predecessors:** P49A is integrated and locally audited; its live source is
  byte-identical to the corresponding quarantine predecessor.  The imported
  algebraic bicommutant core is local support, not a later package.  No P49C,
  P50, or later package is imported.
- **Permitted gate:** discharged exactly: for a unital complex star subalgebra
  of bounded operators, the bicommutant equals its strong-operator closure.
- **Forbidden downstream claims:** respected.  The module contains no
  Kaplansky unit-ball density, corner trace, normality/faithfulness,
  finiteness/fullness, global trace/weight, central type-III exclusion, or
  factor-classification theorem.

## Verification

- `lake env lean aristotle_responses/P49B-quarantine/.../VonNeumannBicommutantTheorem.lean` - passed from the live built project; no build/update/fetch was run in quarantine.
- `lake build AristotleCandidates.VonNeumannBicommutantTheorem` - passed.
- `lake build AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.StrongOperatorClosedVonNeumann AristotleCandidates.VonNeumannBicommutantTheorem Formalization` - passed.
- `lake build` - passed in the live project.
- `#print axioms` for `strongClosure_eq_bicommutant`,
  `strongClosure_eq_vonNeumannGenerated`, `mem_strongClosure_iff`,
  `exists_mem_approx_on_fin`, and `strongClosure_eq_self_iff` - each reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scan - no executable `sorry`, `admit`,
  user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide`;
  matches are only negative-scope documentation.
- Quarantine/live byte comparison, SHA-256 comparison, and `git diff --check` - passed.

## Adversarial review

No acceptance-blocking finding.  The review checked that `strongClosure` is
topological SOT closure rather than norm closure; the finite-neighbourhood
criterion works in both directions; the `n = 0` amplification case is covered
without an empty-family exception; and the cyclic-subspace step uses unitality,
star invariance, and completeness precisely where needed.  The remaining risk
is deliberately outside P49B: this theorem does not supply Kaplansky bounded
density, nor does compilation establish any project-specific normal trace or
von Neumann-algebra conclusion.

## Cleanup and worktree state

Kept intentionally: the integrated P49B candidate, its closeout review, and
the ignored raw archive/quarantine snapshot.  Preserved unchanged: the
pre-existing untracked P49A candidate and P49/P49A reviews.  No commit, push,
manuscript modification, dependency update, archive build, or dependency fetch
was performed.
