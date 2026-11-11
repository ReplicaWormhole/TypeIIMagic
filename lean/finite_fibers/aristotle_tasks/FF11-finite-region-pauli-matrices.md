# FF11 — phase-free finite-region Pauli matrices

## Status

Accepted and integrated on August 5, 2026 from Aristotle project
`76d70d89-bf7a-490b-a1ee-6c3512437110`.

- Archive: `../aristotle_responses/FF11-finite-region-pauli-matrices.tar.gz`
- SHA-256: `acaaeac3024447b211faf050224b9146e978d90c105da094a22b9226d84b529a`
- Quarantine: `../aristotle_responses/FF11-extracted/`

Only `AristotleCandidates/FiniteRegionPauliMatrices.lean` was integrated as
`formalization_finite_fibers/FiniteFiber/FiniteRegionPauliMatrices.lean`; the
two files are byte-identical.  The remote README attribution, stale handoff
deletion, `ARISTOTLE_SUMMARY.md`, and unsupported commit/push claim were
rejected.  The mathematical-fidelity and Lean/API reviews are recorded in
`../aristotle_responses/FF11-prompt-adversarial-review.md` and
`../aristotle_responses/FF11-integration-adversarial-review.md`.

## Source locators

- `writing/overleaf_prl_stabilizer_region_algebras/main.tex:812-885` defines
  the finite-region Hilbert spaces and local algebras, their inclusion by
  tensoring with the identity, and the local Pauli operators
  `O = tensor_{i in F} p_i`.
- `formalization_finite_fibers/FiniteFiber/FiniteRegionQubitAlgebra.lean`
  supplies `finiteRegionBasis`, `finiteRegionQubitAlgebra`, the canonical
  finite-region split, and `finiteRegionEmbed`.
- `formalization_finite_fibers/FiniteFiber/FinitePauli.lean` supplies
  `PauliLabel.matrix` and its one-site Hermiticity/identity facts.
- `formalization_finite_fibers/FiniteFiber/FiniteTensorMatrixChain.lean`
  supplies the ordered finite-string factorization and the generic reindexed
  Kronecker APIs.
- `formalization_finite_fibers/FiniteFiber/FullPauliLattice.lean:6-16,
  373-401` deliberately keeps the normal-form full Pauli group separate from
  an operator realization; FF11 must preserve that boundary.

## Mathematical statement

For a finite region `F : Finset Site` and a Hermitian Pauli label at every
site,

```lean
a : ↥F → PauliLabel,
```

construct the literal tensor-product matrix on the computational basis
`finiteRegionBasis F = (↥F → Fin 2)` by the coordinate-free formula

```text
P_F(a)(x,y) = product over i : ↥F of
  PauliLabel.matrix (a i) (x i) (y i).
```

This is the finite-region realization of the manuscript's phase-free local
Pauli strings.  Prove that the all-identity string is the matrix identity, the
string is self-adjoint, and that its image under the checked local inclusion
`finiteRegionEmbed F F' hFF'` is exactly the matrix with labels padded by the
identity on `F' \ F`.

The padding theorem must be stated through `finiteRegionEmbed`, whose
definition uses the canonical `finiteRegionSplitEquiv`; do **not** state an
unreindexed tensor equality on the raw `F'` basis.

## Essential phase boundary

This package is **not** a representation of `FullPauliWord`, and it must not
prove any multiplication/closure theorem for the new matrices.  The existing
normal form is `i^phase X^x Z^z`, whereas
`PauliLabel.ofProjectiveCoordinates (1, 1) = Y`; with the current one-qubit
matrices, `X * Z = -i * Y`.  Thus even the phase-zero normal-form label
`(1, 1)` is not represented by the Hermitian `Y` factor without a later
`ZMod 4` phase correction.  A Boolean sign is not enough for that correction.

Accordingly, do not import `FullPauliLattice`, define a map from
`FullPauliWord`, identify syntactic support with matrix-algebra membership,
or state a group homomorphism.  Also do not claim inclusion coherence for
three regions, a colimit, quasi-local closure, state, GNS representation, or
the finite-projection theorem.

## Allowed ownership

Create and modify **only**:

```text
AristotleCandidates/FiniteRegionPauliMatrices.lean
```

Do not modify `FiniteFiber/`, `tests/`, the package manifest, any README,
hand-off file, manuscript, or work record.  Do not add attribution text or
unrelated files.

## Required declarations

In `namespace FiniteFiber`, with

```lean
variable {Site : Type*} [DecidableEq Site]
```

define exactly these public declarations (private helper definitions and
lemmas are allowed when indispensable):

```lean
noncomputable def finiteRegionPauliMatrix
    (F : Finset Site) (a : ↥F → PauliLabel) :
    finiteRegionQubitAlgebra F :=
  fun x y => ∏ i : ↥F, PauliLabel.matrix (a i) (x i) (y i)

noncomputable def finiteRegionPadLabels
    (F F' : Finset Site) (a : ↥F → PauliLabel) :
    ↥F' → PauliLabel :=
  fun x => if hx : x.val ∈ F then a ⟨x.val, hx⟩ else PauliLabel.I

theorem finiteRegionPauliMatrix_all_I (F : Finset Site) :
    finiteRegionPauliMatrix F (fun _ => PauliLabel.I) = 1

theorem finiteRegionPauliMatrix_isSelfAdjoint
    (F : Finset Site) (a : ↥F → PauliLabel) :
    IsSelfAdjoint (finiteRegionPauliMatrix F a)

theorem finiteRegionEmbed_pauliMatrix
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (a : ↥F → PauliLabel) :
    finiteRegionEmbed F F' hFF' (finiteRegionPauliMatrix F a) =
      finiteRegionPauliMatrix F' (finiteRegionPadLabels F F' a)
```

## Proof constraints and useful APIs

- Import `FiniteFiber.FiniteRegionQubitAlgebra` and open
  `BigOperators` and `Kronecker` scopes.  Work classically where required.
- The product is over the subtype `↥F`, not an arbitrary `Fin F.card`
  enumeration.  This avoids adding a noncanonical order to the physical
  finite-region statement.
- Private helpers may define labels on `F'` obtained by joining labels on `F`
and `F' \ F`, and may prove the load-bearing reindexed split formula

  ```text
  Matrix.reindex e e P_{F'}(joined labels)
    = P_F(left labels) tensor P_(F' \ F)(right labels),
  ```

  for `e = finiteRegionSplitEquiv F F' hFF'`.  Derive the public padding
  theorem from `finiteRegionEmbed_apply`, that split formula, and the
  all-identity tail theorem.
- Relevant available APIs include `Finset.prod_sdiff`, `Finset.prod_subtype`,
  `Fintype.prod_equiv`, `Matrix.reindex_apply`, `Matrix.kronecker_apply`,
  `Matrix.one_apply`, and `PauliLabel.matrix_I_eq_one` /
  `PauliLabel.matrix_isSelfAdjoint`.
- The all-identity proof must handle the off-diagonal case explicitly: a
  differing bit assignment supplies an identity-factor entry equal to zero.
- Keep every helper private unless it is one of the five listed public
  declarations.  No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `implemented_by` declaration is permitted.

## Verification and response

Run:

```bash
lake env lean AristotleCandidates/FiniteRegionPauliMatrices.lean
```

Return a compiling candidate containing exactly the public declarations above,
plus indispensable private helpers.  If blocked, return a precise minimal
Lean API/proof-obligation report without a placeholder.
