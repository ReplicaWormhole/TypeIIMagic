# FF15: finite-region full-Pauli matrix multiplication

Work in the existing Lean project `formalization_finite_fibers`, using the
integrated modules `FiniteFiber.FiniteRegionPhasedPauliMatrices`,
`FiniteFiber.FiniteRegionEmbeddingCoherence`, and
`FiniteFiber.FullPauliLattice`.

Create a new file
`FiniteFiber/FiniteRegionFullPauliMultiplication.lean`.  Do not modify the
existing files and do not attempt a quasilocal completion, a state, a GNS
construction, or the infinite finite-projection theorem.

The target is the finite-region operator-level bridge for the existing
algebraic normal form `FullPauliWord Site`, whose multiplication is

`(a*b).phase = a.phase + b.phase + FullPauliWord.cocycle a.label b.label`.

For a finite region `F : Finset Site`, first define a matrix for a projective
label function `p : ↥F → ProjectivePauliLabel` using the already integrated
`finiteRegionNormalFormMatrix`, and define the scalar phase factor for a full
word as `zmod4PhaseFactor a.phase`.  If necessary, formulate the main result
for two finite-region projective label functions `p q` first, then lift it to
`FullPauliWord` values whose supports are contained in `F` via restriction to
`↥F`.

Prove the exact finite-dimensional multiplication identity:

`matrix(a * b) = matrix(a) * matrix(b)`

where the phase correction is precisely the existing cocycle
`FullPauliWord.cocycle`, not an unexplained new sign.  The proof should expose
the one-site relation for `X^x Z^z` multiplication and then use the finite
tensor/product factorization.  Also prove the identity-word case and, if it is
available without changing the scope, that the central word
`FullPauliWord.negativeIdentity` maps to `(-1) • 1`.

Use the established convention `X` then `Z`, so the `(1,1)` one-site raw
matrix is `-i * Y` and its correction is `3 : ZMod 4`.  Use the existing
`FullPauliWord.phaseEmbed`, `xCoordinate`, `zCoordinate`, `binaryDot`, and
`cocycle`; do not redefine the cocycle.

No `sorry`, `admit`, new axioms, `unsafe`, `opaque`, or `native_decide`.
If the full `FullPauliWord` lift is blocked by a missing finite-support lemma,
return the strongest compiling core (the one-site multiplication lemma and
finite-region projective multiplication theorem) and state the exact missing
lemma rather than silently weakening or postulating it.  Return the complete
candidate file and the exact Lean build result.
