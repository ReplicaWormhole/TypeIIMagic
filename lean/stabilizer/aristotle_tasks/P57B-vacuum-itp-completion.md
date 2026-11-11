# P57B — vacuum-restricted ITP completion

## Context declaration

- **Infrastructure only:** complete the proved finite-support vacuum-restricted
  pre-inner-product core from P57A. This packet makes no manuscript factor or
  trace claim.

## Plan alignment

- **Package and lane:** `P57B`; Lane `shared`.
- **Predecessors:** `P57A`, integrated and locally audited.
- **Gate discharged:** construct an actual quotient/completion Hilbert space
  with dense algebraic vacuum-tensor image, so later pure-sector work does not
  rely on an assumed infinite tensor-product Hilbert space.
- **Forbidden downstream claims:** no identification with a pure GNS
  representation, no `B(K)` closure/factor theorem, no mixed factor, no
  spatial von Neumann product, and no trace/weight statement.

## Mathematical target

Create only `AristotleCandidates/VacuumRestrictedITPCompletion.lean`. Starting
with `AristotleCandidates.VacuumRestrictedITP.itpCore`, use the pinned Mathlib
pre-inner-product construction to define the seminormed quotient implicit in
the core and its uniform-space completion. Prove that the resulting type has
the required complete normed complex inner-product/Hilbert structure, that the
algebraic vacuum-tensor span maps linearly and isometrically modulo zero into
it with dense range, and that the vacuum image has norm one.

The quotient must be genuine: equal zero-norm vectors must be identified by
the construction, not retained in a merely seminormed space while calling it a
Hilbert space. Establish every transferred scalar, norm, inner-product, and
completion instance by proof from P57A and Mathlib. If a required Mathlib API
is absent, expose the exact missing theorem and leave this gate unaccepted;
do not introduce a completion structure, quotient, Hilbert instance, or dense
embedding as a field, axiom, or interface.

## Auxiliary assumptions

Exactly P57A's generic assumptions: `[DecidableEq ι]`, complex inner-product
spaces `E i`, and unit reference vectors `Ω i`. No definiteness, quotient,
completion, density, GNS, or operator-algebra premise may be added.

## Files and imports

Create only `AristotleCandidates/VacuumRestrictedITPCompletion.lean`; import
P57A and the necessary pinned Mathlib completion modules. Do not import
`bound_beating`, edit P57A, or use its excluded completion wrappers.

## Acceptance criteria

- `lake build AristotleCandidates.VacuumRestrictedITPCompletion` succeeds.
- The final completion is an actual complete complex inner-product/Hilbert
  space, with a proved dense algebraic map and proved vacuum norm one.
- The module has no `sorry`, `admit`, axiom, opaque completion interface, or
  claim about GNS/factor/spatial tensor products.
- The response states how null vectors are quotiented and names every
  nontrivial Mathlib completion theorem used.
