# Lean/mathlib API re-audit: I003 finite Pauli-density realization

**Verdict: APPROVED WITH RESIDUAL RISKS.**  This re-audit supersedes the
earlier Lean/API `CHANGES REQUESTED` verdict.  The generic local API has been
renamed and consistently scoped as an algebraic theorem about normalized
signed-Pauli expressions.  It no longer presents arbitrary signed finite term
families as density matrices or states.  The actual finite-stabilizer branch
continues to prove its density and state properties under the required
finite-group hypotheses, and its bridge to `SelfAdjointFiniteGroupAction`
remains type-faithful and axiom-clean.

This review records the expression-level I003 snapshot listed below.  A
subsequent conditional nested-group layer, `FiniteNestedPauli.lean`, now proves
compatible actual finite stabilizer densities from an explicit tensor-coordinate
decomposition, injective inclusion, and survivor iff-condition.  It still does
not derive that contract from a countable-lattice stabilizer system or construct
the global GNS data.

## Reviewed snapshot

| File | SHA-256 |
|---|---|
| `FiniteFiber/FinitePauli.lean` | `b6b52186c52eeb94efa8037b6bcb8971a78f0503df5b8d715b98949066a5e6e0` |
| `FiniteFiber/FiniteDensity.lean` | `b7d95d9d9c1ae20cd9d79f7a17659faa1dcf8d7ef9ab741e65faa61de309ce7c` |
| `FiniteFiber/FinitePauliStabilizer.lean` | `9b148f81babcc7cb2af97303024580a6f2d7a0d4c2b8536ff7c2e4166c36275e` |
| `FiniteFiber/FiniteLocalPauli.lean` | `9bb0823883c2f4e600a2ac652d7b4a0d71380f0a85530552addafb906263c690` |
| `FiniteFiber.lean` | `83c384594dccf966534bb555f4d21600a5053ff36aa37c5f1cefc0d13eb83946` |
| `tests/AxiomAudit.lean` | `36081932701427169d9ea4a0382a818c05c75349fc7003123fc965db911c9742` |

## Resolved scope blocker

`CompatibleSignedPauliExpressionData` is now named at the correct level
(`FiniteLocalPauli.lean:23-40`).  Its only fields are finite large/small term
families, a sign, left/right Pauli labels, and an explicit survivor equality.
The public operations are `largeExpression` and `smallExpression`, and the
sole compatibility theorem is

```text
partialTraceRight D.largeExpression = D.smallExpression.
```

(`FiniteLocalPauli.lean:46-66`).  It has no `PosSemidef`, trace-one, positive
functional, group-law, or no-`-1` conclusion or hidden premise.  Its module
and theorem documentation explicitly say that it is not a theorem about
positive trace-one density matrices (`:4-17`, `:57-61`).

The lower-level generic survivor theorem has the same boundary.  Its
documentation calls the result a normalized signed-Pauli expression and states
that the survivor equality neither constructs a stabilizer group nor makes an
arbitrary term family a density matrix (`FiniteDensity.lean:260-280`).
The concrete group-density identification is likewise limited to one actual
`FinitePauliStabilizerData` instance and explicitly does not identify nested
local groups or establish their survivor condition
(`FinitePauliStabilizer.lean:232-249`).

An adversarial consumer check still constructs the negative identity expression
with `K = PUnit` and `n = m = 0`.  It proves the renamed partial-trace equality
and computes `smallExpression.trace = -1`.  This is now the intended behavior:
the API permits the expression but makes no density/state claim about it.  It
therefore confirms the scope boundary rather than refuting a public theorem.

The live I003 question and technical record preserve the same separation
between arbitrary expressions and actual densities, while now recording the
conditional nested-group bridge:

- `QUESTION.tex:39-54` asks for a partial-trace theorem for expressions and
  states the extra contract under which actual density compatibility is proved.
- `technical.tex` distinguishes actual finite-group densities from the generic
  expression calculation, records the conditional nested-group theorem, and
  leaves its derivation from the global local-group definition unformalized.
- `README.md:23-32`, `HANDOFF.md:77-95`, and `AGENTS.md:44-61` reflect the
  same package-level boundary.

I found no live source or I003-record claim that promotes the arbitrary
expression data to density matrices.  The retained mathematical-fidelity
review records the pre-correction counterexample and is historical review
evidence, not a declaration or current API contract.

## Confirmed finite branch and abstract-action bridge

The density/state results remain restricted to
`FinitePauliStabilizerData`, which supplies a group homomorphism, signed-Pauli
realization, injectivity, and exclusion of represented `-1`
(`FinitePauliStabilizer.lean:33-47`).  Under explicit `[Fintype G]`, Lean
proves the nonidentity trace calculation, projection identities, trace-one
normalization, positive semidefiniteness, positivity of the finite functional,
and code-corner traciality.  These are therefore genuine finite-dimensional
stabilizer-density conclusions, not consequences of an arbitrary `Finset`.

`actionInRepresentation` has the exact target
`SelfAdjointFiniteGroupAction (H := H) (G := G)`, while `operatorAction`
realizes the finite matrix action on the finite Euclidean Hilbert space.  Their
average equations preserve the concrete stabilizer projector.  The public
types require the unital star-algebra representation and make no implicit GNS,
normality, injectivity-of-the-target-representation, or infinite-volume claim.

## Imports and axiom audit

The direct I003 import direction is acyclic:

```text
FinitePauli -> mathlib
FiniteDensity -> FinitePauli
FinitePauliStabilizer -> FiniteStabilizerTrace + FiniteDensity + FinitePauli
FiniteLocalPauli -> FiniteDensity
FiniteFiber -> re-exports all four
```

`tests/AxiomAudit.lean:39-44` now audits the I003 projector, density,
finite-functional, corner-trace, abstract-action, and renamed expression-level
entry points.  In particular, it contains

```text
#print axioms FiniteFiber.CompatibleSignedPauliExpressionData.partialTrace_largeExpression
```

The current audit reports only `propext`, `Classical.choice`, and `Quot.sound`
for that theorem and the other I003 targets.  A source scan found no `axiom`,
`sorry`, `admit`, `opaque`, `unsafe`, or `implemented_by` declaration.  A scan
also found no remaining source occurrence of the superseded
`CompatibleSignedPauliLocalData`, `largeDensity`, `smallDensity`, or
`partialTrace_largeDensity` names.

## Verification

The following commands were rerun after the final documentation corrections,
from `formalization_finite_fibers/`, and all exited zero:

```text
lake build FiniteFiber.FiniteDensity
lake build FiniteFiber.FinitePauliStabilizer
lake build FiniteFiber.FiniteLocalPauli
lake build
lake env lean tests/AxiomAudit.lean
```

The full build completed with 3170 jobs.  The no-file consumer check described
above compiled against the renamed public API.

## Adversarial closeout and residual boundary

The previous negative-sign counterexample was rechecked under the corrected
names.  It verifies that the new API does not accidentally acquire an
unjustified positivity/normalization theorem.  No remaining Lean/API defect was
found in the requested scope.

The approval does not derive the `FiniteNestedPauli.lean` contract from the
global countable-lattice local-group definition.  Nor does it establish the
quasi-local state/GNS construction, strong extension of corner traciality, or
I002's remaining analytic hypotheses.  Those are stated boundaries, not hidden
assumptions in the approved finite APIs.
