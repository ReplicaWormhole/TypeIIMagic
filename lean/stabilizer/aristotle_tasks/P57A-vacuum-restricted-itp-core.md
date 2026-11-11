# P57A — vacuum-restricted infinite-tensor pre-Hilbert core

## Context declaration

- **Infrastructure only:** establish a reusable, local finite-support
  vacuum-restricted infinite-tensor pre-Hilbert core for the later product-GNS
  proof. This packet does not itself formalize a manuscript conclusion.

## Plan alignment

- **Package and lane:** `P57A`; Lane `shared`.
- **Predecessors:** none. This generic foundation may run in parallel with
  P56R.
- **Gate discharged:** a proved finite-support algebraic ITP kernel and
  pre-inner-product core, avoiding a second implementation in P57.
- **Forbidden downstream claims:** no completed infinite tensor-product Hilbert
  space, no tensor-factor GNS theorem, no spatial von Neumann tensor product,
  no factor classification, and no manuscript-facing state identity.

## Mathematical target

Create only `AristotleCandidates/VacuumRestrictedInfiniteTensorProduct.lean`.
Port and adapt the verified finite-support portion of
`<original-home>/Projects/current/bound_beating/formalize_itp/Formalization/InfiniteTensorProductHilbert.lean`
to this repository's namespace and imports. The source and target both use
Lean 4.28, but this must be a local audited port, not an import of the other
project.

For an index type `ι`, Hilbert spaces `E i`, and unit reference vectors `Ω i`,
define vacuum-restricted elementary tensors (equal to `Ω` away from a finite
active set), their finite-product kernel, the algebraic finite span, and its
sesquilinear extension. Prove finite-mode realization by finite tensor
products; use it to prove positivity on arbitrary finite linear combinations,
conjugate symmetry, additivity, and scalar compatibility. Export the resulting
`PreInnerProductSpace.Core` and the algebraic vacuum vector with norm-square
one.

Do **not** port, import, or rely on
`VacuumRestrictedITPInnerProductAxioms`, `ITPCompletionAxioms`,
`canonicalVacuumRestrictedITPInnerProductAxioms`, or any analogous wrapper.
This packet deliberately stops before quotient/completion. If a statement from
the source file turns out not to compile locally, repair it with a proof or
report the exact API mismatch; do not postulate it.

## Auxiliary assumptions

Only the explicit generic typeclass assumptions needed by the construction:
`[DecidableEq ι]`, a normed additive commutative group and complex inner-product
space for each `E i`, and `inner (Ω i) (Ω i) = 1`. No completion, positivity,
or density premise may be added.

## Files and imports

Create only `AristotleCandidates/VacuumRestrictedInfiniteTensorProduct.lean`.
Use local Mathlib imports for finsets, finsupps, finite tensor products, and
pre-inner-product cores. Do not import the `bound_beating` project, edit it, or
copy any file that contains a `sorry`/axiom wrapper into this repository.

## Acceptance criteria

- `lake build AristotleCandidates.VacuumRestrictedInfiniteTensorProduct`
  succeeds.
- The file has no `sorry`, `admit`, `axiom`, or completion/interface wrapper.
- The finite-mode realization and positivity on a general finite linear
  combination are both explicit proved theorems.
- The response names the local source file and confirms it did not import the
  external project or claim a completed Hilbert space.
