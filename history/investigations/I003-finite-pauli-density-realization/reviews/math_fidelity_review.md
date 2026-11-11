# I003 mathematical-fidelity re-review

**Verdict: APPROVED**

This re-review supersedes the earlier `REVISE` verdict.  The earlier blocker
was real: arbitrary signed term families satisfying the survivor equality need
not be positive or trace one.  The corrected snapshot no longer calls that
generic construction a density matrix or a local stabilizer group, and it
keeps the missing realization step explicit.

**Post-review scope update.** `FiniteNestedPauli.lean` now supplies the
conditional realization step for two actual finite stabilizer groups: its
explicit tensor-coordinate, injective-inclusion, and survivor-iff contract
identifies the generic expressions with positive trace-one stabilizer densities
and proves their partial-trace equality.  This historical review's references
to an unimplemented bridge mean only its derivation from the global
countable-lattice definition, which remains open.

## Scope checked against the manuscript

The source target is the live finite-volume construction in
`writing/overleaf_prl_stabilizer_region_algebras/main.tex:864-949`: consistent
finite Pauli stabilizers, the group-average projector and density
(`:881-914`), and the partial-trace survivor calculation (`:916-949`).

## Resolution of the previous blocker

- The generic API is now accurately named
  `CompatibleSignedPauliExpressionData`, with `largeExpression`,
  `smallExpression`, and `partialTrace_largeExpression`
  (`FiniteLocalPauli.lean:4-17,27-66`).  Its module documentation explicitly
  denies hidden group, positivity, and trace-one assumptions.
- The generic survivor theorem is also explicitly expression-level:
  `FiniteDensity.lean:260-279` says that the equality neither turns arbitrary
  term families into stabilizer groups nor into density matrices.
- The I003 question and technical note make the same distinction
  (`QUESTION.tex:23-29,47-51`; `technical.tex:44-61,191-212`).  In particular,
  the checked conclusion is now
  $\operatorname{Tr}_{F'\setminus F}(E_{F'})=E_F$, not an unqualified equality
  of density matrices (`technical.tex:193-203`).
- The package-level navigation is consistent: `README.md:24-33`,
  `HANDOFF.md:77-98`, and `AGENTS.md:49-56` all separate actual finite-group
  densities from generic expression-level partial trace.

The former negative-all-identity singleton counterexample remains permitted by
the expression API, but that is now correctly documented rather than being an
unstated counterexample to a theorem about states.

## Finite-group density claims remain justified

For `FinitePauliStabilizerData`, the Lean assumptions are exactly the needed
finite ones: a faithful group representation by signed Pauli strings and no
represented $-I$ (`FinitePauliStabilizer.lean:39-47`).  The implementation
then proves all claims advertised as density-matrix facts:

- the group average is a self-adjoint idempotent
  (`FinitePauliStabilizer.lean:120-174`);
- $\operatorname{Tr}(P_G)=2^n/|G|$ and
  $\operatorname{Tr}(\rho_G)=1$ (`:177-204`);
- $\rho_G=(\operatorname{Tr}P_G)^{-1}P_G$ (`:206-224`);
- the concrete density equals its normalized signed-Pauli sum (`:226-248`);
- the projector and density are positive semidefinite, and the finite
  functional is normalized and positive (`:250-333`).

The documentation on the signed-sum identification now also says that it is
only one finite-group instance of the generic expression layer, not a proof
about two nested local groups or their survivor condition
(`FinitePauliStabilizer.lean:232-249`).

The signs are faithful to the standard convention:
$Y=\left(\begin{smallmatrix}0&-i\\ i&0\end{smallmatrix}\right)$
(`FinitePauli.lean:32-37`), Boolean `true` denotes the scalar $-1$
(`FiniteDensity.lean:56-70`), and partial trace preserves that sign while
retaining precisely right-identity terms with the factor $2^m$
(`FiniteDensity.lean:95-112,213-258`).  Thus the trace normalization matches
the manuscript's calculation.  No separate matrix-rank theorem is claimed;
for the proved finite star projection, rank equals trace as the standard
finite-dimensional consequence.

## Scope and remaining explicit bridge

No Lean or TeX theorem now overclaims a global stabilizer construction or GNS
realization.  The finite representation transport is conditional on a unital
star-algebra representation and explicitly not an infinite-volume GNS result
(`FinitePauliStabilizer.lean:437-470`).

The remaining global bridge is stated, rather than hidden: the
`FiniteNestedPauli.lean` tensor-coordinate, inclusion, and survivor contract
must be derived from $\cG_{\cS,F}=\cG_{\cS}\cap\cA_F$ for arbitrary finite
lattice regions.  Construction of the countable lattice, quasi-local state,
GNS vector, and strong trace extension remain separately listed.  These are
deliberate out-of-scope obligations, not defects in the approved finite
algebraic layer.

## Verification performed

- `lake build` in `formalization_finite_fibers/` — passed.
- `lake env lean tests/AxiomAudit.lean` — passed.  The audit now covers the
  I003 finite projector, positivity, functional, representation-transport,
  and expression-compatibility theorems (`tests/AxiomAudit.lean:39-44`); each
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Searched the four I003 Lean modules for `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, and `implemented_by` — no matches.
- `pdflatex -interaction=nonstopmode -halt-on-error` for I003 `technical.tex`
  and `QUESTION.tex`, each with a temporary output directory — passed, with no
  undefined references or fatal TeX errors.

## Residual risk

This approval covers the stated finite group-density calculation and the
generic signed-Pauli partial-trace identity.  The later conditional
`FiniteNestedPauli.lean` bridge has its own fresh adversarial review; neither
review approves a global quasi-local or GNS conclusion.
