# Mathlib Operator-Algebra Coverage Audit

Date: 2026-06-21

Purpose: identify which parts of the complete canonical stabilizer
projection-state type-classification blueprint can rely on existing mathlib
theory, especially von Neumann algebra theory, and which parts need
project-local blueprint and Lean development.

## Checked Environment

Project toolchain:

- Lean/mathlib via this workspace's Lake project.
- `lakefile.lean` pins mathlib `v4.29.1`.

Main checks used:

```lean
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.PiTensorProduct
```

## Available In Mathlib

### Hilbert Spaces And Bounded Operators

Mathlib has standard Hilbert-space infrastructure:

- `HilbertSpace`, implemented as complete inner product spaces;
- `InnerProductSpace`;
- bounded/continuous linear maps `H ->L[ℂ] H`;
- adjoints for bounded operators.

These are usable foundations for represented algebras on Hilbert spaces.

### C*-Algebras And Positive Linear Maps

Mathlib has substantial C*-algebra infrastructure:

- `CStarAlgebra`;
- `NonUnitalCStarAlgebra`;
- `StarOrderedRing` and spectral order infrastructure;
- `PositiveLinearMap`, notation `A ->ₚ[ℂ] ℂ`;
- positivity facts such as `star_mul_self_nonneg`;
- continuous functional calculus and projection facts.

This can support the blueprint/Lean interface for states as positive linear
maps once the project has a suitable Pauli/quasi-local C*-algebra.

### GNS Construction

Mathlib has a GNS construction in
`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`.

Representative checked declarations:

```lean
PositiveLinearMap.GNS :
  (f : A ->ₚ[ℂ] ℂ) -> Type

PositiveLinearMap.gnsStarAlgHom :
  (f : A ->ₚ[ℂ] ℂ) -> A →⋆ₐ[ℂ] (f.GNS ->L[ℂ] f.GNS)
```

Important caveat from the mathlib file TODO: it does not yet explicitly
construct the cyclic unit vector and reconstruction formula as a polished
state package.  The blueprints should include this theory, and Lean may need
project-local wrappers around mathlib's GNS API.

### Concrete Von Neumann Algebras

Mathlib has a concrete bundled von Neumann algebra:

```lean
VonNeumannAlgebra H
```

from `Mathlib.Analysis.VonNeumannAlgebra.Basic`, where `H` is a Hilbert space.
It is a `StarSubalgebra ℂ (H ->L[ℂ] H)` equal to its double commutant.

Representative checked declarations:

```lean
WStarAlgebra
VonNeumannAlgebra
VonNeumannAlgebra.commutant
VonNeumannAlgebra.commutant_commutant
VonNeumannAlgebra.IsStarProjection.mem_iff
```

The file explicitly notes that the abstract/concrete equivalence and double
commutant theorem as a weak-closure theorem remain future work.

### Projections

Mathlib has star projections:

```lean
IsStarProjection p
```

and a von Neumann membership criterion:

```lean
VonNeumannAlgebra.IsStarProjection.mem_iff
```

This is useful for projection-level arguments, but not enough by itself for
Murray-von Neumann comparison or type classification.

### Finite Matrix Algebras And Traces

Mathlib has:

- matrix trace `Matrix.trace`;
- cyclic trace facts such as `Matrix.trace_mul_comm`;
- linear-map trace `LinearMap.trace`;
- tensor-product trace fact `LinearMap.trace_tensorProduct'`;
- Kronecker products and `Matrix.trace_kronecker`;
- C*-matrix algebras through `CStarMatrix`;
- `CStarMatrix.instCStarAlgebra`.

This is good support for finite local matrix-algebra pieces and finite tensor
products.

### Algebraic And Finite Hilbert Tensor Products

Mathlib has:

- algebraic tensor products;
- `PiTensorProduct` as an algebraic indexed tensor product;
- finite inner-product tensor product structure;
- `TensorProduct.instInnerProductSpace`;
- `TensorProduct.norm_tmul`;
- `OrthonormalBasis.tensorProduct`.

The finite tensor-product theory is useful for local finite systems.

## Missing Or Insufficient For The Full Classification

The following representative checks failed as unknown identifiers:

```lean
#check Factor
#check IsFactor
#check VonNeumannAlgebra.IsFactor
#check MurrayVonNeumann
#check IsFiniteProjection
#check IsInfiniteProjection
#check IsSemifinite
#check Semifinite
#check TypeI
#check TypeII
#check TypeIII
#check VonNeumannAlgebra.TypeI
#check VonNeumannAlgebra.TypeII
#check VonNeumannAlgebra.TypeIII
```

Conclusion: mathlib currently does not appear to provide the high-level von
Neumann algebra type-classification API needed for the final theorem.

In particular, the project should expect to blueprint and probably formalize
project-local versions of:

- factor/center definitions for concrete `VonNeumannAlgebra H`;
- finite, infinite, properly infinite, and semifinite projection notions;
- Murray-von Neumann equivalence/comparison, at least in the special cases
  needed by the proof;
- tracial von Neumann algebra and faithful normal semifinite trace interfaces,
  or narrowly scoped substitutes;
- type `I_n`, `I_infty`, `II_1`, `II_infty`, and type III exclusion criteria;
- proofs that the represented region algebra has the required type in each
  stabilizer-rank case.

## Infinite Tensor Product Caveat

Mathlib's `Analysis.InnerProductSpace.TensorProduct` file contains finite
Hilbert tensor-product infrastructure and explicitly lists completion of tensor
products as TODO.  `PiTensorProduct` is algebraic.  Therefore the project
should not assume mathlib already has the infinite Hilbert tensor product or
infinite von Neumann tensor-product theory needed for a direct infinite-product
construction.

Recommended blueprint strategy:

- use finite tensor products and finite matrix algebra facts where possible;
- use mathlib's GNS construction to obtain the infinite Hilbert space from a
  positive linear functional;
- formulate any infinite tensor-product/product-factor identifications as
  source-backed project-local theorems, initially blueprint-level and later
  possibly as scoped Lean abstractions rather than full general theory.

## Practical Blueprint Consequence

The complete blueprint theory should be split into two lanes:

1. **Mathlib-backed infrastructure lane.**
   Use existing declarations for Hilbert spaces, bounded operators, positive
   linear maps, GNS, concrete von Neumann algebras, star projections, finite
   matrices, traces, and finite tensor products.

2. **Project-local operator-algebra classification lane.**
   Develop the missing factor/type/projection/tracial theory in the precise
   scope needed for canonical stabilizer projection states.  The blueprints
   should cite standard von Neumann algebra sources for these facts and mark
   which statements are intended as new Lean targets.

This means the final classification blueprint must include the standard
von Neumann algebra type theory itself, not just reference a currently
available mathlib type-classification declaration.
