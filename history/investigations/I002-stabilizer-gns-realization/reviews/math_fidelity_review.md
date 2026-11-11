# Mathematical-Fidelity Review: I002 Post-Stabilizer Layer

Verdict: APPROVED

Status: APPROVED

## Findings

### Blocking

None in the final revised artifact.

## Fidelity Results

1. **The public scope now matches its signature.**  The canonical declaration
   is
   `stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit`
   (`FiniteFiber/StabilizerFiniteFiber.lean:49-63`).  It assumes exactly a
   `SelfAdjointFiniteGroupAction`, finite subgroups `S n`, their membership in
   `M`, monotonicity `S n <= S m`, common fixed-vector data, and the explicit
   `GNSOrbitConditions`.  It does not assert that the subgroups cover `K`.
   The theorem title, module comments, and technical statement now consistently
   say a nested/increasing finite-subgroup sequence
   (`technical.tex:95-105, 293-304, 349-355`), rather than falsely calling this
   weaker interface an exhaustion or a Pauli realization.

2. **Finite averages correctly model the required algebraic stabilizer step.**
   `SelfAdjointFiniteGroupAction` supplies a group representation and
   self-adjointness for every represented group element
   (`FiniteStabilizer.lean:26-41`).  That condition is sufficient for the
   commuting operator image used in the average: the image of `gh` is
   self-adjoint, while its adjoint reverses the images of `g` and `h`.  The
   direct proofs establish left/right invariance, idempotence, and
   self-adjointness of the normalized average
   (`:44-98`).  No tensor-product Pauli realization, no `-\id` consistency
   proof, and no claim that every abstract instance is Pauli is smuggled in.

3. **Nested local groups give the correct decreasing order.**
   For `S <= T`, the checked theorem
   `restrict_average_isSubprojection_of_le`
   (`FiniteStabilizer.lean:240-255`) gives the average over `T` below the
   average over `S`.  It is used with the correct orientation in
   `stabilizerAverageSequence_decreasingProjectionSequence`
   (`StabilizerSequence.lean:37-50`), giving
   `p_m p_n = p_n p_m = p_m` for `n <= m`.  This matches the decreasing
   local-support relation in the live proof
   (`writing/overleaf_prl_stabilizer_region_algebras/main.tex:1030-1110`).
   The unformalized bridge from the manuscript's lattice regions
   `\Gamma_n` and local groups `\cG_{\cS,\Gamma_n}` to this supplied sequence
   remains explicitly outside the theorem.

4. **The strong limit is genuinely constructed.**
   `decreasingProjectionStrongLimit` is the complement of the orthogonal
   projection onto the closure of the union of the decreasing ranges'
   orthogonal complements (`StrongSupport.lean:37-49`).  The implementation
   uses mathlib's monotone orthogonal-projection convergence theorem, then
   proves membership in the concrete bicommutant, projectionhood, and the
   fixed-vector property (`:89-108, 176-210`).  This is the standard
   decreasing-projection limit of Blackadar I.5.1.3, PDF p. 29, not an assumed
   strong-convergence axiom.

5. **The trace/nonzero-support module has the correct finite-volume boundary.**
   `average_trace` proves
   `Tr(P)=|G|^{-1} dim H` only from a supplied nonidentity-tracelessness
   condition; `average_ne_zero_of_traceless` additionally requires
   `finrank H != 0` (`FiniteStabilizerTrace.lean:25-78`).  The technical note
   now states both hypotheses, records the resulting finite-dimensional trace
   and nonzero-support conclusion, lists the module and its build command, and
   says that it is not used to prove nonzero global GNS support
   (`technical.tex:293-304, 349-370`).  It correctly leaves Pauli
   tracelessness, the qubit-dimension identity, and their finite-volume/GNS
   connection unformalized.

6. **The GNS, trace, and type boundaries remain fail-closed.**
   `GNSOrbitConditions` receives the regional/complementary commutations,
   dense product orbit, and corner traciality as explicit fields
   (`GNSOrbit.lean:20-38`).  It neither constructs the GNS representation nor
   derives density or the Kaplansky/strong-topology trace extension.  The
   technical boundary section states those omissions, as well as the lack of a
   direct-integral/type-III API (`technical.tex:305-336`).

7. **The central finite witness is the manuscript's literal one.**
   The final bundle exposes `central_witness` with the exact conjunction
   `IsFiniteProjection M (z * q) /\ z * q != 0 /\ IsSubprojection (z * q) z`
   (`GNSOrbit.lean:46-54, 76-95`).  The stabilizer-sequence specialization
   forwards that field unchanged (`StabilizerFiniteFiber.lean:114-130`) from
   `canonical_central_witness_of_full_tracial_corner`
   (`FiniteFibers.lean:42-50`).  It therefore matches the live central-summand
   proof and its `zq` witness (`main.tex:1474-1539`), rather than hiding the
   witness inside existential semifiniteness.

## Verification

- `lake build FiniteFiber.FiniteStabilizer` — passed.
- `lake build FiniteFiber.FiniteStabilizerTrace` — passed.
- `lake build FiniteFiber.StabilizerSequence` — passed.
- `lake build FiniteFiber.StrongSupport` — passed.
- `lake build FiniteFiber.StabilizerFiniteFiber` — passed.
- `lake build` — passed (2729 jobs).
- `lake env lean tests/AxiomAudit.lean` — passed.  Every audited declaration,
  including `average_trace`, `average_ne_zero_of_traceless`, and the canonical
  stabilizer theorem, depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Two isolated `pdflatex` passes on `technical.tex` — passed.  The final PDF is
  five pages and the second pass has no undefined-reference, overfull, or
  underfull warnings.

## Adversarial Closeout and Residual Boundary

The previous two scope blockers were repaired: a monotone sequence is no
longer presented as an exhaustion, and the new finite-dimensional trace result
is explicitly conditional and is not promoted to a global GNS fact.  No false
strengthening or missing hypothesis remains in the stated conditional theorem.

This approval does not certify an end-to-end Pauli/stabilizer construction,
the lattice-to-local-group bridge, compatible reduced density matrices, the
GNS construction or product-orbit density, the local-to-von-Neumann trace
extension, or direct-integral/type classification.  Those are correctly
recorded as future work.  Only this review artifact was changed; the broad
pre-existing dirty and untracked repository state was preserved.
