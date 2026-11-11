# Lean/mathlib API review: finite-fiber formalization

Verdict: APPROVED

## Scope and snapshot

This review covers the standalone conditional algebraic package
`formalization_finite_fibers/` and its correspondence with the I001 blueprint,
not the later stabilizer/GNS realization.  It was audited at the following
source hashes:

```text
Basic.lean          0ec21977eba9ef0a2cb2f30838efcebce65e5cbcbcc22d4327c430d68f78ccef
TracialCorner.lean  2f9f7e3d78636351e9e8a8d2e45406e1778d7ea1a9d535d36461f8f6ae0060bd
FiniteFibers.lean   5aee17afa13a64d1339bfb19bc7f6ef2e2743daa26cab37307e624a85cfab86b
```

## Findings

1. Severity: none -- the imported mathlib API is compatible with the pinned
   toolchain.

   Locations: `lakefile.lean:7-11`, `FiniteFiber/Basic.lean:1-4`, and the
   declarations in `Basic.lean:23-181`.

   The package pins mathlib `v4.28.0`, whose resolved revision agrees with the
   archived package (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`).  The concrete
   `VonNeumannAlgebra H`, `IsStarProjection`, C*-zero test, and star-subalgebra
   membership APIs elaborate under that revision.  The local `FiniteFiber`
   namespace avoids an upstream name collision.  The derived
   `isPartialIsometry_of_star_mul_eq_projection` preserves the blueprint's
   ordinary Murray--von Neumann witness definition rather than strengthening
   its public hypothesis.

   Required correction: none.

2. Severity: none -- the trace interface is now corner-scoped and does not
   assume the desired semifiniteness conclusion or an unjustified global trace.

   Locations: `FiniteFiber/TracialCorner.lean:15-29`,
   `FiniteFiber/TracialCorner.lean:36-112`, and
   `technical.tex:212-257,291-360`.

   `FaithfulTracialCorner.tracial` applies only to `IsCornerElement` arguments.
   The checked witness lemma proves that the partial isometry and its adjoint
   lie in that corner before cyclicity is used.  Thus the proof uses exactly
   the traciality supplied by a tracial corner state; it no longer requires
   `tau (a * b) = tau (b * a)` for arbitrary elements of `M`.  No hypothesis
   states `IsSemifinite`, finite projection existence, or a type-III
   exclusion.

   Required correction: none.

3. Severity: none -- the central/fiber API proves the intended ambient
   theorem and exposes the canonical witness.

   Locations: `FiniteFiber/FiniteFibers.lean:27-78` and
   `technical.tex:425-449`.

   From a full tracial support, `full_tracial_corner_semifinite` returns a
   nonzero finite projection below every nonzero central projection.  For an
   explicitly supplied finite central family,
   `finite_central_fiber_canonical_witness` identifies it as `z_i * q`; the
   existential corollary is a direct specialization.  This matches the stated
   projection-form result.  It deliberately does not claim a bundled corner
   algebra, a direct-integral decomposition, or a Lean `not_typeIII` theorem.

   Required correction: none.

## Verification

- `lake build` in `formalization_finite_fibers/` completed successfully:
  `Build completed successfully (2410 jobs)`.
- A separate temporary-output audit compiled `Basic.lean`,
  `TracialCorner.lean`, and `FiniteFibers.lean` in dependency order, then
  imported `FiniteFiber.FiniteFibers`.
- `lake env lean tests/AxiomAudit.lean` completed successfully.  Its public
  theorem audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
  no user axiom, `sorry`, or other placeholder was found.

## Residual scope risks

- `FaithfulTracialCorner.tau` is an ambient linear extension.  The later
  GNS/stabilizer layer must still supply such an extension (or refactor the
  interface to a bundled corner functional), as well as traciality,
  faithfulness, and fullness.  This is explicitly retained as future work in
  `technical.tex:453-479` and `HANDOFF.md:42-50`; it is not silently proved by
  this package.
- The finite-family fields `orthogonal` and `sum_eq_one` are useful for the
  advertised finite-fiber presentation, but the witness theorem itself needs
  only the selected member's centrality and nonzeroness.  This is an API
  economy observation, not a correctness defect.
- Upstream mathlib naming and placement remain deliberately provisional, as
  documented in `HANDOFF.md:52-59`.
