# P56R — recovered regional C-star product state

## Context declaration

- **Source basis:** `main.tex:1921-1946`.

## Plan alignment

- **Package and lane:** `P56R`; Lane `H`.
- **Predecessors:** `P55D`, integrated and locally audited. `P56` is a
  preserved partial artifact, not a predecessor or accepted result.
- **Gate discharged:** construct the pure/mixed product **C-star state** and
  prove that the regional state transported through the exact P55D C-star
  alpha agrees with it.
- **Forbidden downstream claims:** no GNS tensor splitting, von Neumann
  spatial tensor product, factorhood, center statement, or trace/weight
  classification.

## Mathematical target

Edit only `AristotleCandidates/RegionalProductStateIdentity.lean`. Keep its
existing finite-word and algebraic state-identity lemmas, but add a recovery
section whose final declarations have **no** `ProductStateBound` argument or
other supplied boundedness/positivity premise.

Starting from the checked one-qubit pure/mixed density matrices and the P55D
concrete source C-star model, prove the finite-stage product functional is
unital and positive and has C-star norm at most one. Use the coherent direct
limit and the isometric dense source embedding to construct a continuous
functional `cstarProductStateRecovered` on the concrete source C-star algebra.
Prove it is unital and positive (positivity on every `a† * a`, or the pinned
Mathlib positive cone if available), and transport it through
`cstarAlpha.symm` to a unital positive
`cstarRegionalStateRecovered`. Finally prove

`cstarRegionalStateRecovered (cstarAlpha T) = cstarProductStateRecovered T`.

If the local project lacks a suitable state predicate, define a small local
predicate whose content is precisely unitality plus positivity on squares;
prove all of its fields. Do not package any of those fields as assumptions.
Do not reuse `ProductStateBound` in a final recovery theorem, and do not merely
rename its existence as an auxiliary structure.

## Auxiliary assumptions

None beyond P55D and the already checked finite pure/mixed one-qubit data.
If a required finite-dimensional C-star estimate cannot be derived from local
Mathlib and the existing finite-stage model, report the exact lemma/API gap and
leave this recovery gate unaccepted; do not add an axiom, `sorry`, `admit`,
opaque interface, or extra premise.

## Files and imports

Edit only `AristotleCandidates/RegionalProductStateIdentity.lean`. Retain its
existing imports and add only pinned local/Mathlib imports needed for a proved
finite-dimensional positivity or norm argument. Do not edit P55D, the
manuscript, another candidate, or an external project.

## Acceptance criteria

- `lake build AristotleCandidates.RegionalProductStateIdentity` succeeds.
- New recovery declarations do not depend on `ProductStateBound`.
- The exact finite-stage norm/positivity lemma, source C-star extension,
  unitality/positivity proofs, and alpha-transport identity are reported
  separately.
- No `sorry`, `admit`, new axiom, supplied state, or supplied completion is
  introduced.
- The response confirms the lane, predecessor, gate, and forbidden-claim
  boundary.
