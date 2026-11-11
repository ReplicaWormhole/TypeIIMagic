# P41 closeout review — product-factor classification boundary

## Decision

**Status: partial; do not advance the queue.**

The reviewed candidate module is
`AristotleCandidates/ProductFactorClassificationBoundary.lean`.  It was
downloaded as
`aristotle_responses/P41-product-factor-classification-boundary.tar.gz` and
extracted, without building or fetching dependencies, at
`aristotle_responses/P41-extracted/aristotle-stabilizer_hyperfinite-7viao_05_aristotle/`.
Only this packet-authorized candidate module was copied into the live project;
the archive and extraction are retained as raw quarantine records.  The live
file is byte-identical to the quarantined candidate (SHA-256
`860d520816f1fdbd1f42a9c24d432ef6b6b5466d2c28d8b9404f85b14993591c`).

## Source and scope

The packet's source basis is `main.tex:1945-1967`.  Those lines propose the
product GNS Hilbert-space decomposition, the spatial product algebra, and the
type-I/hyperfinite-II1 alternatives.  The candidate correctly treats the GNS
algebra, spatial identification, and factor classifications as supplied
interfaces; it does not claim that Mathlib constructs an infinite tensor
product, spatial von Neumann tensor product, or a classified factor.

## Exact checked declarations and assumptions

`ProductGNSFactorization` (lines 223-282) supplies `VN`, `gnsRep`, `vnState`,
the equation `vnState_gnsRep`, `PureFactor`, `MixedFactor`, `Tensor`, the two
embeddings and `embeddings_commute`, `spatialIdentification`, type predicates,
and the two classification fields.  The finite case additionally takes
`FinitePureTraceData` (lines 359-379): `pureSector_finite`, three explicitly
algebraic tracial states, and `traceTensor_factorizes`.

With those inputs, `finitePureSector_product_classification` (lines 427-441)
proves the finite type-I pure label, the supplied mixed-sector label dichotomy,
and transport of a normalized **algebraic** tracial state with its displayed
product formula.  Its transport lemmas are `FinitePureTraceData.gnsTrace`,
`gnsTrace_tracialState`, and `gnsTrace_factorizes` (lines 383-408).

The infinite case takes `InfinitePureWeightData` (lines 455-471):
`pureSector_infinite`, two isometries, their equations, `ranges_sum`, and a
`TracialWeightCore`.  `InfinitePureWeightData.no_tracialState_vn` (lines
517-523) correctly transports the existing algebraic two-isometry obstruction,
and `infinitePureSector_product_classification` (lines 564-582) proves the
infinite type-I label, mixed-sector label dichotomy, absence of an **algebraic**
tracial state, and transport of that core.  The mutually exclusive sector
cases are proved by `finite_and_infinite_pure_data_incompatible` (lines
586-589).

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | Sector finite/infinite bookkeeping; transport of the supplied finite-case algebraic tracial state; type-label consequences of supplied predicates; the two-isometry algebraic no-trace obstruction; and transport of the algebraic finite trace ideal. |
| partial | The finite/infinite distinction is explicit in both theorem conclusions, and all type/classification content is conditional on named supplied fields. |
| blocked | `InfinitePureWeightData.weightCore` is only `TracialWeightCore`. Its defining source explicitly states that it asserts no positivity, normality, faithfulness, or semifiniteness. Thus no supplied faithful normal semifinite trace/weight interface exists, and neither P41 theorem conditionally states or transports such a weight. This fails the packet's explicit infinite-pure requirement; calling the core “prospective” in documentation does not recover the missing premise or conclusion. |
| failed | No Lean proof failure; the unmet item is the mathematical target's required interface, not compilation. |

Accordingly, P41's mathematical target is **not met at its stated scope**.
The candidate is useful, correctly bounded algebraic infrastructure, but it
does not supply the required named faithful-normal-semifinite weight
assumption/interface.  The supervisor must halt this lane rather than treating
the queue as advanced.

## Adversarial review

No placeholder or unacknowledged analytic classification claim was found in
the candidate.  In particular, the factor predicates are labels rather than
constructed types, the spatial identification is supplied, and the infinite
case never calls its core a state.  The acceptance-blocking finding above is
the precise remaining scope gap.  No `sorry`, `admit`, user `axiom`, `opaque`,
`unsafe`, `implemented_by`, or `native_decide` declaration occurs in the
candidate or its three direct imported modules.  The audited declarations
report only `propext`, `Classical.choice`, and `Quot.sound` under `#print
axioms`.

## Verification

- `lake build AristotleCandidates.ProductFactorClassificationBoundary` — passed in the already-built live project.
- `lake build AristotleCandidates.CStarTracialWeightCore Formalization.FinitePureMixedQubitState Formalization.ProperlyInfiniteTraceObstruction AristotleCandidates.ProductFactorClassificationBoundary Formalization` — passed.
- `lake build` — passed.
- `lake env lean /dev/stdin` with `#print axioms` for the finite/infinite classification theorems, their central transport/obstruction lemmas, and `trivialFinitePureTraceData` — passed; each listed only `propext`, `Classical.choice`, and `Quot.sound`.
- Candidate byte comparison, forbidden-declaration scans, and `git diff --check` — passed.

## Cleanup and worktree state

Kept intentionally: the P41 candidate module, its archive and extracted
quarantine snapshot, and this review, so the exact partial result is
auditable.  All pre-existing modified and untracked work was preserved.  No
manuscript file was modified; no commit, push, dependency update, archive
build, or dependency fetch was performed.
