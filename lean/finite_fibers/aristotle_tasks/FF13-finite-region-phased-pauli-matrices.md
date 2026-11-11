# FF13: finite-region phased Pauli matrices

Work in the existing Lean project `formalization_finite_fibers`.

Create a new file `FiniteFiber/FiniteRegionPhasedPauliMatrices.lean` importing
`FiniteFiber.FiniteRegionPauliMatrices` and
`FiniteFiber.OneSitePauliNormalForm`.  Do not modify existing files and do not
touch the global infinite-system theorem.

Define, for a finite region `F : Finset Site` and a label function
`p : ↥F → ProjectivePauliLabel`, the raw finite-region normal-form matrix as
the entrywise product of `normalFormOneSiteMatrix (p i)` over the region.
Define the summed `ZMod 4` correction as the finite sum of
`normalFormHermitianCorrection (p i)`.

Prove, with no `sorry`, `admit`, new axioms, `unsafe`, or opaque escape hatches,
the exact matrix identity relating the raw matrix to the scalar phase
`zmod4PhaseFactor` of the summed correction times the phase-free Hermitian
matrix built from `PauliLabel.ofProjectiveCoordinates (p i)`.  Also prove the
all-zero label gives the identity matrix.  If a padding statement is feasible,
prove identity padding under `finiteRegionEmbed`; otherwise leave it out and
return the strongest compiling core theorem.

Keep the convention explicit: the one-site factor order is `X^x * Z^z`, so the
`(1,1)` correction is `3` and `X*Z = -i*Y`.  Do not claim multiplicativity of
`FullPauliWord`, cocycle compatibility, support/locality, a colimit, a state,
or a GNS construction.  Return the complete candidate file and the exact
Lean build command/result.
