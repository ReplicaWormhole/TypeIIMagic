# P49C closeout review - Kaplansky density and compressed-corner approximation

## Decision

**Status: proved at the stated shared-infrastructure scope; queue may advance.**

The completed Aristotle project was downloaded as
`aristotle_responses/P49C-kaplansky-density.tar.gz` (SHA-256
`6ba52fd4f44f836e02dcf62d4d0cb2c66434d36ee860be54161d2f108a158074`) and
extracted without a build, update, or dependency fetch at
`aristotle_responses/P49C-quarantine/aristotle-stabilizer_two_lane_p49c-ocehfr10_aristotle/`.

Only the packet-authorized module `AristotleCandidates/KaplanskyDensity.lean`
was integrated. Its SHA-256 is
`e57deb88999d442a8882f37fd4b956e7d36df5849b460dea9f5aa1c5bd1ddde4` in both
quarantine and the live project. The ignored archive and quarantine snapshot
remain raw response records. No manuscript file was changed.

## Exact declarations and assumptions

For `H` with `[NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]`
and `A : StarSubalgebra ℂ (H ->L[ℂ] H)`, the integrated module proves:

- `KaplanskyDensity.ball_mem_strongClosure`: if `A` is norm closed, every
  `x` in `A''` with `‖x‖ <= 1` belongs to the SOT closure of the unit ball of
  `A`;
- `KaplanskyDensity.scaled_ball_mem_strongClosure`: the corresponding
  norm-bounded scaled statement;
- `KaplanskyDensity.selfAdjoint_mem_strongClosure` and
  `KaplanskyDensity.selfAdjoint_ball_mem_strongClosure`: the self-adjoint
  intermediate forms;
- `KaplanskyDensity.exists_bounded_net` and
  `KaplanskyDensity.exists_net_compression`: bounded SOT approximation of
  `qxq` by `qaq` with `a` in `A`;
- `KaplanskyDensity.exists_net_compression_product`: product-filter SOT
  convergence in both multiplication orders.

The only extra analytic premise is `IsClosed (A : Set (H ->L[ℂ] H))`.
Unitality is inherited from `StarSubalgebra`; completeness supports the
finite-amplification Hilbert-space argument. Projections are explicitly given
by `star q = q` and `q * q = q`. No density, trace, normality, faithfulness,
finiteness, or factor statement is supplied as a field or axiom.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The bounded Kaplansky theorem is derived from the P49B SOT bicommutant theorem, a local convex weak-to-strong closure argument, functional calculus for the self-adjoint unit ball, and a local 2 by 2 amplification. The compressed and product-filter corollaries are proved from the resulting bounded nets and P49A bounded SOT multiplication. |
| partial | None within the P49C gate. The result is abstract concrete-operator infrastructure; it does not yet identify a project-specific represented C-star algebra or its corner trace. |
| blocked | Nothing blocks the stated P49C gate. P50 still must supply traciality, normality, and faithfulness with its own exact hypotheses. |
| failed | None. No compilation, placeholder, provenance, scope, or forbidden-downstream-claim failure was found. |

The packet's mathematical target is met. In particular, the result is genuine
topological strong-operator closure and a nontrivial bounded net extracted from
that closure, rather than a sequential or unbounded-density substitute. The
joint result uses `l1 ×ˢ l2` and proves both displayed product orders.

## Manuscript boundary

The packet declares source basis `main.tex:1269-1315`. Those lines are used
only as the locator for the intended compressed-algebra-to-von-Neumann-corner
passage. This module is shared Lean infrastructure; it does not assert that
the manuscript's `tau_q` is tracial, normal, or faithful, that `q` is finite
or full, that any central summand is non-type-III, that a global trace/weight
exists, or that a Lane-H algebra is a factor.

## Plan alignment

- **Package and lane:** P49C, lane `shared` -- correct.
- **Predecessors:** P49B is integrated and locally audited; its imported P49A
  and bicommutant support are compiled predecessors. No later package is
  imported.
- **Permitted gate:** discharged exactly: unit-ball/scaled Kaplansky density,
  compressed-corner approximation, and jointly indexed bounded product SOT
  convergence.
- **Forbidden downstream claims:** respected. The source imports only Mathlib
  and `AristotleCandidates.VonNeumannBicommutantTheorem`; it contains no P50+
  import, trace/normality/faithfulness theorem, finiteness/fullness/type-III
  theorem, global trace/weight theorem, or Lane-H factor theorem.

## Verification

- `lake build AristotleCandidates.KaplanskyDensity` -- passed (one
  non-blocking style suggestion at line 463).
- `lake build AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.StrongOperatorClosedVonNeumann AristotleCandidates.VonNeumannBicommutantTheorem AristotleCandidates.KaplanskyDensity Formalization` -- passed.
- `lake build` -- passed in the already-built live project.
- `#print axioms` for `ball_mem_strongClosure`,
  `scaled_ball_mem_strongClosure`, `exists_net_compression`, and
  `exists_net_compression_product` -- each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scan -- no executable `sorry`, `admit`,
  user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide`;
  the sole matches are negative-scope documentation.
- Quarantine/live byte comparison, SHA-256 comparison, and `git diff --check`
  -- passed.

## Adversarial review

No acceptance-blocking finding. The review checked the load-bearing boundary:
the closure is Mathlib's SOT closure, the unit-ball restriction is obtained
before nets are extracted, norm-closedness is explicitly used for the
resolvent's membership in `A`, the zero scaling case is handled, and the two
compressed factors are bounded before invoking joint product convergence.
The residual risk is deliberately outside P49C: this generic theorem alone
does not establish the manuscript's concrete representation, corner trace,
normality, faithfulness, finiteness, fullness, or type classification.

## Cleanup and worktree state

Kept intentionally: the integrated P49C candidate, this review, and the
ignored raw archive/quarantine snapshot. Preserved unchanged: all pre-existing
untracked candidates and reviews. No commit, push, manuscript modification,
dependency update, archive build, or dependency fetch was performed.
