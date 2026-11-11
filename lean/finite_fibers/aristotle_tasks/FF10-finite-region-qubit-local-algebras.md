# FF10 — finite-region qubit local algebras

## Status

Accepted and integrated on August 5, 2026 from Aristotle project
`88d5f994-e829-4ded-b04a-b38c650e4f8b`.  This is the first operator-algebra
bridge between the existing abstract `Finset Site` lattice layer and the
existing finite tensor-matrix layer.  It replaces the off-track FF09
configuration-only follow-up and does not depend on or retrieve FF09.

The remote archive is
`aristotle_responses/FF10-finite-region-qubit-local-algebras.tar.gz` with
SHA-256 `7ca2f97893a1fc872626a0a7095b14887504c36939aa3b1e584cf086b0fa5778`.
Its snapshot is quarantined at `aristotle_responses/FF10-extracted/`.  Only
the candidate Lean file was integrated.  The candidate's file-local C-star
instance was promoted to the named scoped
`FiniteFiber.FiniteRegionQubitMatrix` instance so that downstream code can use
the public norm theorem; this small integration repair was independently
checked.  No other remote file or attribution text was accepted.

## Source locators

- `formalization_finite_fibers/FiniteFiber/ProjectivePauliLattice.lean`
  provides arbitrary finite regions `F : Finset Site`.
- `formalization_finite_fibers/FiniteFiber/FiniteTensorMatrixChain.lean`
  provides `coordinateEmbedRight`, its explicit reindexed Kronecker formula,
  and its injectivity theorem.

## Mathematical statement

For a site type `Site` with decidable equality and a finite region
`F : Finset Site`, let the computational basis be the functions
`F -> Fin 2`, and let the local algebra be its complex matrix algebra.  For a
finite inclusion `F \subseteq F'`, restriction to `F` and to `F' \ F`
gives a canonical coordinate equivalence

```text
(F' -> Fin 2)  ~=  (F -> Fin 2) x ((F' \ F) -> Fin 2).
```

Using the existing generic coordinate embedding, construct the physical local
inclusion `A |-> A tensor 1` from the smaller to the larger local matrix
algebra.  Prove only its explicit coordinate formula, injectivity, and
operator-norm preservation.

This is the literal finite-region version of the manuscript's local inclusion
`A_F -> A_F'` for `F \subseteq F'`.  It does not yet identify Pauli words or
stabilizer groups with matrix elements, and it does not construct a colimit,
norm closure, state, GNS representation, or finite-fiber theorem.

## Allowed ownership

Create and modify **only**:

```text
AristotleCandidates/FiniteRegionQubitAlgebra.lean
```

Do not modify `FiniteFiber/`, `tests/`, the package manifest, any README,
hand-off file, manuscript, or work record.  Do not add attribution text or
unrelated files.

## Required declarations

In `namespace FiniteFiber`, with

```lean
variable {Site : Type*} [DecidableEq Site]
```

define exactly these public declarations (private helper lemmas are allowed):

```lean
abbrev finiteRegionBasis (F : Finset Site) := ↥F → Fin 2

abbrev finiteRegionQubitAlgebra (F : Finset Site) :=
  Matrix (finiteRegionBasis F) (finiteRegionBasis F) ℂ

noncomputable def finiteRegionSplitEquiv
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionBasis F' ≃
      finiteRegionBasis F × finiteRegionBasis (F' \ F)

noncomputable def finiteRegionEmbed
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionQubitAlgebra F →⋆ₐ[ℂ] finiteRegionQubitAlgebra F'

theorem finiteRegionEmbed_apply
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    finiteRegionEmbed F F' hFF' A =
      Matrix.reindex (finiteRegionSplitEquiv F F' hFF').symm
        (finiteRegionSplitEquiv F F' hFF').symm
        (A ⊗ₖ (1 : finiteRegionQubitAlgebra (F' \ F)))

theorem finiteRegionEmbed_injective
    (F F' : Finset Site) (hFF' : F ⊆ F') :
    Function.Injective (finiteRegionEmbed F F' hFF')

theorem finiteRegionEmbed_norm
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    ‖finiteRegionEmbed F F' hFF' A‖ = ‖A‖
```

The candidate must import `FiniteFiber.FiniteTensorMatrixChain`, open the
`ComplexOrder` and `Kronecker` scopes, and use a **candidate-local**
noncomputable `CStarMatrix.instCStarAlgebra` instance for the finite-region
matrix type.  Do not introduce a global matrix-norm/C-star instance.
The intended local declaration is:

```lean
noncomputable local instance finiteRegionCStarAlgebra (G : Finset Site) :
    CStarAlgebra (finiteRegionQubitAlgebra G) :=
  CStarMatrix.instCStarAlgebra
```

## Proof constraints

- Construct `finiteRegionSplitEquiv` by restriction to `F` and `F' \ F`.
  Its inverse must case-split on membership in `F`.  Use `classical` and
  explicit subtype-membership proofs, in particular `hFF' x.property` and
  `Finset.mem_sdiff.mpr ⟨x.property, hx⟩`.
- Define `finiteRegionEmbed` by the existing
  `coordinateEmbedRight (finiteRegionBasis F)
  (finiteRegionBasis (F' \ F)) (finiteRegionBasis F')`
  applied to `finiteRegionSplitEquiv F F' hFF'`.
- Obtain the displayed formula from `coordinateEmbedRight_apply`.
- For injectivity, use `coordinateEmbedRight_injective`; the discarded basis
  is nonempty even when the complement is empty, witnessed by the constant
  zero bit function.
- For norm preservation, use the candidate-local C-star instance,
  injectivity, and `NonUnitalStarAlgHom.norm_map`.
- Do not assert nested-inclusion composition or a directed system yet.  That
  belongs to a subsequent task after this one-stage local-algebra bridge is
  checked.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `implemented_by`.

## Verification and response

Run:

```bash
lake env lean AristotleCandidates/FiniteRegionQubitAlgebra.lean
```

Return a compiling candidate containing exactly the public declarations above,
plus indispensable private helpers.  If blocked, return a precise minimal
Lean API/proof-obligation report without a placeholder.
