# P56R closeout review — recovered regional C-star product state

## Decision

**Status: proved at the stated conditional Lane-H scope; queue may advance.**

Aristotle project `026bfc92-1158-49a3-9049-ca7588e54dbb`, task
`91db2acf-a167-41cd-bebd-ef882f843c64`, is terminal `COMPLETE` in
`history/logs/20260810T080459Z-026bfc92-tasks.log`.
The supervisor-supplied archive
`aristotle_responses/P56R-regional-cstar-product-state-026bfc92-91db2acf.tar.gz`
has SHA-256
`09c401cad7ea05da5257575b5a4a019bed4fdb802833e3a95e2e70f14f75ba1a`.
It was extracted only into
`aristotle_responses/P56R-regional-cstar-product-state-026bfc92-91db2acf-quarantine/`;
no Lean build, dependency update, or dependency fetch ran there.  The only
packet-owned source integrated into the live project was
`AristotleCandidates/RegionalProductStateIdentity.lean`.  Its live SHA-256
matches the quarantined candidate exactly:

```text
a2a4cbcc0aabdf90da9de9b75d15a60bc6c8dff7c5f12a5d7f5a56f2a76b5f00
```

No manuscript, P55D predecessor, unrelated candidate, or unrelated dirty file
was modified.  The older P56 material remains in the same candidate as a
preserved partial artifact; it is not evidence for the P56R acceptance.

## Exact P56R declarations and assumptions

The recovery section adds the following proved declarations:

- `AlphaData.norm_stageProductState_le`: the finite-stage product functional
  is norm-decreasing for the finite matrix C-star norm.
- `AlphaData.stageProductState_positive`: every finite-stage value on
  `star x * x` is a nonnegative real.
- `AlphaData.sourceProductState_positive` and
  `AlphaData.sourceProductState_isAlgebraicState`: positivity and unitality
  on the algebraic direct limit.
- `AlphaData.norm_sourceEmbedding_sourceOf` and
  `SourceConcreteRep.norm_sourceProductState_le`: the stage and direct-limit
  estimates transported through the faithful isometric P55C embedding.
- `SourceConcreteRep.cstarProductStateRecovered`, together with
  `cstarProductStateRecovered_sourceEmbedding`,
  `cstarProductStateRecovered_one`,
  `cstarProductStateRecovered_positive`,
  `cstarProductStateRecovered_isAlgebraicState`, and
  `norm_cstarProductStateRecovered_le_one`: the continuous source C-star
  functional, its dense formula, unitality, positivity on every square, local
  state predicate, and norm bound.
- `SourceConcreteRep.cstarRegionalStateRecovered`, together with
  `cstarRegionalStateRecovered_targetEmbedding`,
  `cstarRegionalStateRecovered_one`,
  `cstarRegionalStateRecovered_positive`, and
  `cstarRegionalStateRecovered_isAlgebraicState`: the transported regional
  functional and its corresponding properties.
- `SourceConcreteRep.cstarRegionalStateRecovered_cstarAlpha` and
  `cstarRegionalStateRecovered_comp_cstarAlpha`: the required exact
  alpha-transport identity.

P56R adds no auxiliary premise.  It takes an `A : AlphaData L I` and an
`R : A.SourceConcreteRep`, hence inherits only the already explicit P53/P55D
conditional infrastructure: the P52 local-hyperbolic family and lattice
exhaustion, `[LinearOrder I]`, and the named `AlphaData.symplectic` and
`AlphaData.stage_surjective` assumptions, together with the constructed
P55C finite/infinite concrete representation branch and the checked finite
pure/mixed one-qubit data.  No `ProductStateBound`, supplied positivity,
supplied state, supplied completion, or new axiom is used by any recovery
declaration.

The local predicate is the existing project predicate
`StabilizerHyperfinite.IsAlgebraicState`: unitality plus positivity on
`star x * x`.  All fields are proved; no standard von Neumann normality claim
is being smuggled into this predicate.

## Changed proof route

P56R replaces the old conditional `ProductStateBound` route with a proved
finite-dimensional density-matrix route.  It constructs the allowed-stage
density matrix
`D = ∑ v ∈ allowedStage, pauliMat v`, proves `D† = D`, `D² = |G| D`, and
computes its trace.  A column decomposition of `tr (D x D)` proves both the
finite-stage norm estimate and positivity.  The estimate transports through
the injective star homomorphism into the P55C concrete C-star model, after
which a proved dense continuous extension supplies the source functional and
transport through `cstarAlpha.symm` supplies the regional functional.

This is an alternative proof route, not a weakened target: it adds no premise
and does not reuse the preserved §8 `ProductStateBound` declarations in the
P56R recovery results.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | The complete P56R gate is proved: finite-stage norm/positivity, algebraic state, continuous source C-star state, transported regional state, and exact alpha identity. |
| partial | Relative to the manuscript theorem, the result remains conditional on P55D’s explicit coordinate and concrete-model data. The manuscript source does not itself construct those hypotheses. |
| blocked | None at the P56R gate. GNS tensor splitting, spatial von Neumann tensor products, factorhood, and trace/weight classification remain later packages and were not attempted. |
| failed | None. No compilation, placeholder, archive-integrity, or scope failure was found. |

The packet’s mathematical target is therefore met at its stated scope.  It is
not a claim that the full manuscript theorem is established.

## Plan alignment

- **Package and lane:** `P56R`, Lane `H`; correct.
- **Predecessors:** `P55D` is integrated, live-compiled, and semantically
  audited in `reviews/P55D-regional-concrete-cstar-alpha-closeout.md`.  The
  original `P56` is explicitly retained as a partial artifact and was not
  treated as a predecessor.
- **Permitted gate:** discharged exactly: construct the pure/mixed product
  C-star state and prove its equality with the regional state transported by
  the exact P55D C-star `alpha`.
- **Forbidden claims:** respected.  No GNS tensor splitting, von Neumann
  spatial tensor product, factorhood, center/trivial-center theorem, or
  trace/weight classification occurs in the recovery section.

The source basis in the packet is `main.tex:1921-1946`, matching the
manuscript’s proposed state construction and finite-word identity.  The
manuscript-facing geometric coordinate/model hypotheses remain external
conditional infrastructure, as required by `AGENTS.md` and
`SOURCE-CONTRACT.md`.

## Verification

- `lake build AristotleCandidates.RegionalProductStateIdentity` — passed
  (`8096/8096` jobs).
- `lake build AristotleCandidates.RegionalProductStateIdentity Formalization`
  — passed (`8096/8096` jobs).
- `lake build` — passed; the full live project was up to date.
- `#print axioms` for all load-bearing recovery declarations listed above —
  each reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan of the candidate and direct P55D/finite-pure-mixed imports
  — no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` occurrence.
- Recovery-section scan — no forbidden downstream terms or declarations.
- Live/quarantine candidate hash comparison and `git diff --check` — passed.
- The exact archive was inspected and extracted without building inside the
  dependency-free quarantine snapshot.

## Adversarial review

No acceptance-blocking finding.  The review checked that the finite estimate
does not divide by zero (`allowedStage` contains zero and the source label
type is nonempty), that positivity is proved first on finite matrix squares
and then extended by closedness from the dense algebraic image, and that the
regional positivity proof uses only the already constructed C-star
equivalence.  It also checked that the old `ProductStateBound` occurs only in
the preserved partial §8 material and explanatory text, not as an argument of
the recovery declarations.  Compilation and axiom reports validate the Lean
proof artifacts; they do not prove the inherited P53/P55D geometric premises
or any later operator-algebraic classification.

## Cleanup and worktree state

Kept intentionally: the exact archive, its quarantine extraction, the
integrated P56R candidate, and this closeout review.  Existing modified
`PLAN.md`, packet/decision files, earlier candidates, and earlier reviews were
preserved.  No commit, push, manuscript edit, archive build, dependency update,
or dependency fetch was performed.
