# P56 closeout review — regional/product-state identity

## Decision

**Status: partial; queue must halt.**

Aristotle task `4b9085b9-015c-4c03-915b-46aa98784ff6` is terminal `COMPLETE`
in `history/logs/20260808T204342Z-137c05f7-tasks.log`.
Its exact archive alone was extracted into
`aristotle_responses/P56-regional-product-state-identity-137c05f7-4b9085b9-quarantine/`.
No build, update, or dependency fetch ran in the dependency-free quarantine
snapshot. The sole packet-owned candidate module,
`AristotleCandidates/RegionalProductStateIdentity.lean`, was copied into the
live project after review. The live and quarantined copies agree at SHA-256
`39e430129834f067b1ee6942d2bf6acd74927c64b62ddc028949b6236cf7b176`.
The quarantined P55D and finite pure/mixed predecessor files are byte-identical
to their live, accepted copies.

The candidate proves the requested finite-word and algebraic identities, but
does **not** prove the required concrete C-star *state* identity. Its only
concrete construction requires the new premise
`SourceConcreteRep.ProductStateBound`; moreover its constructed objects have
type `... →L[ℂ] ℂ`, with no positivity or C-star-state theorem. Therefore the
reported C-star result is only a conditional equality of continuous linear
functionals, not the state extension requested by P56. This is a meaningful
partial artifact but does not discharge the P56 gate.

## Exact declarations and assumptions

For `A : AlphaData L I`, the candidate adds the following unconditional
algebraic results:

- `allowedLabels`, `stabilizerLabels`, and
  `coordinateMap_mem_stabilizerLabels_iff`;
- `productExpectation`, `productExpectation_of_mem`, and
  `productExpectation_of_not_mem`;
- coherent unital linear functionals `sourceProductState` and
  `regionalStabilizerState` on the algebraic direct limits;
- `regionalStabilizerState_alpha_word` (finite Pauli words) and
  `regionalStabilizerState_alpha` (the whole algebraic source limit);
- stabilizer-word and unitality lemmas, including
  `regionalStabilizerState_stabilizerElement`.

The density statement
`SourceConcreteRep.cstarState_identity` is correct at its stated type: for
*given* continuous linear maps `f` and `g` that agree with the two algebraic
functionals on dense ranges, it proves `g (R.cstarAlpha T) = f T`. It also
proves uniqueness of such maps.

The candidate then adds the new auxiliary structure
`SourceConcreteRep.ProductStateBound`:

```lean
structure ProductStateBound where
  const : ℝ
  norm_le : ∀ z : A.SourceLimit,
    ‖A.sourceProductState z‖ ≤ const * ‖R.sourceEmbedding z‖
```

Only under `hb : R.ProductStateBound` does it construct
`cstarProductState hb`, `cstarRegionalState hb`, and prove
`cstarRegionalState_cstarAlpha hb`. These are continuous linear functionals,
not formal C-star states: the module proves neither positivity nor the
norm-one/state property, and it does not derive `ProductStateBound` from the
finite density-matrix expectations and P55C representation.

The candidate inherits the already accepted P53/P55C/P55D conditional
coordinate and representation infrastructure. No axiom, sorry, admit, opaque,
unsafe declaration, or forbidden downstream declaration was added.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The finite-word equality is proved in `regionalStabilizerState_alpha_word`; linear-basis extension proves the algebraic direct-limit identity `regionalStabilizerState_alpha`. The generic dense-range theorem `cstarState_identity` is also proved for already-continuous functionals. |
| partial | The advertised concrete equality is conditional on the newly introduced `ProductStateBound`, which is not a locally integrated predecessor result. The constructed functionals have no proof of positivity, so Lean has not established either as a C-star state. |
| blocked | P56's gate is not discharged: the missing boundedness/positive-state extension must be proved from the finite pure/mixed density-matrix states and the actual P55C C-star norm (or be made an explicitly approved new conditional downstream interface). P57 may not treat this module as an accepted state-identity predecessor. |
| failed | No Lean build or placeholder failure occurred. The failure is semantic scope, not compilation. |

The packet's mathematical target is met on finite Pauli words and on the
algebraic quasi-local limit. It is **not** met at the required concrete
C-star-state scope.

## Plan alignment

- **Package and lane:** P56, Lane H. This is correct.
- **Predecessors:** the prepared packet incorrectly names retired `P55`.
  The active `PLAN.md` and decision record require P55D. The candidate itself
  imports `RegionalConcreteCStarAlpha`, and P55D is locally integrated,
  compiled, and semantically audited in
  `reviews/P55D-regional-concrete-cstar-alpha-closeout.md`; its archive copy
  matches the accepted live file. The stale packet declaration is recorded and
  has not been used as evidence.
- **Permitted gate:** only the product-state equality after the exact P55D
  alpha is in scope. The algebraic part is discharged; the concrete C-star
  state-extension part remains conditional and therefore the gate is not
  discharged.
- **Forbidden downstream claims:** respected. The module makes no GNS tensor
  splitting, represented von Neumann/spatial tensor-product, factorhood,
  trivial-center, trace, or weight conclusion.

## Source alignment

The packet's source basis `main.tex:1915-1969` is accurate. In particular,
the finite-word selection/expectation argument is represented by
`regionalStabilizerState_alpha_word`, matching `main.tex:1927-1943`. The
manuscript's passage from equality on Pauli-word bases to equality of the
states is represented only algebraically. Its C-star continuity/state
content remains an auxiliary analytic obligation, not a manuscript-derived
fact.

## Verification

- `lake build AristotleCandidates.RegionalProductStateIdentity` — passed
  (`8062/8062` jobs).
- `lake build AristotleCandidates.RegionalProductStateIdentity Formalization`
  — passed (`8096` jobs).
- `lake build` — passed (up to date, `0` jobs).
- `lake env lean /dev/stdin` importing the candidate and printing axioms for
  `regionalStabilizerState_alpha_word`, `regionalStabilizerState_alpha`,
  `cstarState_identity`, `cstarRegionalState_cstarAlpha`, and
  `regionalCStarAlpha_state_identity` — each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Placeholder scan of the candidate plus direct P55D and pure/mixed imports —
  no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or
  `native_decide` occurrence.
- Quarantine/live hashes for the candidate and direct predecessors, and
  `git diff --check` — passed.

## Adversarial review

One acceptance-blocking finding: lines 694--700 introduce rather than prove
the norm bound required to pass from the algebraic functional to a continuous
C-star functional; lines 714--765 use that premise. Lines 647--657 prove a
valid uniqueness implication, but it assumes the continuous functionals
already exist. The module contains no positivity theorem (the objects are
declared as continuous linear maps), so calling the final conditional result a
state identity would overstate the evidence.

No other scope, source-locator, forbidden-claim, axiom, or compilation defect
was found. The P53/P55D assumptions remain external conditional
infrastructure, as already recorded by their accepted closeouts.

## Cleanup and worktree state

Kept intentionally: the exact archive, its 223-file quarantine extraction,
the reviewed partial candidate, and this closeout. All modified plan/task/
decision files and pre-existing candidates/reviews remain untouched. No
manuscript file was modified; no commit, push, archive build, dependency
update, or dependency fetch occurred.
