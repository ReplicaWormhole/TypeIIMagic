# Formalization progress

## Context policy (2026-08-05)

All future manuscript-facing formalization takes its context only from
`SOURCE-CONTRACT.md`, with exact locators in the manuscript `main.tex`. Earlier
gLU/refinement/layer-coherence artifacts remain available only as explicitly
labelled legacy infrastructure; they are not manuscript hypotheses. See
`AGENTS.md` and `CONTEXT-LEDGER.md`.

The manuscript-facing module sequence is now `Formalization.Manuscript`:
source boundary, finite model, algebraic limit, product state, conditional GNS
bridge, trace dichotomy, and only then the pending theorem contract. Existing
implementation files remain in place and are imported through facades.

- P17 — under a supplied finite adapted-coordinate/word realization, the
  finite pure/mixed product state is exactly the stabilizer indicator on every
  supplied source Pauli basis word.
- P18 — a supplied finite matrix-factor tensor decomposition transports the
  finite product trace to an algebraic tracial state with its elementary-tensor
  formula.
- P19 — a supplied C-star model plus compatible states packages the existing
  GNS unitary and algebraic commutant transport into one bridge interface.
- P23 — supplied coherent finite-stage star equivalences induce the infinite
  algebraic direct-limit regional equivalence `alpha`, with finite-stage and
  inverse formulas. No C-star or von Neumann extension is claimed.
- P24 — compatible target-stage algebraic states pull back along `alpha` to a
  unique algebraic direct-limit state with its exact finite-stage expectation
  formula and conditional stabilizer-indicator corollary.
- P25 — supplied C-star completions and an extension of `alpha` yield an
  isometric continuous C-star equivalence and continuous state pullback;
  existence of those completions remains an explicit assumption.

## Checked Lean results

- `TPT-001` / `TPT-002` — an algebraic tracial state pulls back along a
  complex `StarAlgEquiv`.
- TPT-003 — algebraic traciality is reflected as well as preserved by a
  complex star-algebra equivalence; hence a nontracial product state cannot
  become tracial after an algebraic coordinate identification.
- `FMT-001` — the normalized trace on a nonempty finite full matrix algebra is
  an algebraic tracial state.  Positivity is proved by the explicit
  trace-of-a-star-square sum-of-squares identity.
- `FSC-001` — a finite corner equipped with a star isomorphism to a full matrix
  algebra inherits that algebraic tracial state.
- `FTT-001` — the finite algebraic tensor product of two matrix factors is
  identified by the Kronecker star isomorphism, and its normalized trace
  factorizes on elementary tensors; tensoring with a matrix identity preserves
  the trace.
- `FAM-001` — if `R` has an algebraic tracial state, then its finite matrix
  amplification `Matrix n n R` has the normalized diagonal tracial state.
  Positivity is checked as a finite sum of coefficient-algebra star-squares.
  An explicit `StarAlgEquiv` transports this finite type-I product trace to a
  target algebra.
- `TMT-001` — the finite type-I product is now identified canonically, not
  supplied as an assumption: `Matrix n n ℂ ⊗[ℂ] R` is star-isomorphic to
  `Matrix n n R`.  Its trace factors on elementary tensors as the normalized
  matrix trace times the coefficient trace.
- `DTT-001` — the actual dyadic finite-stage system is constructed as
  `A₀ = ℂ`, `Aₙ₊₁ = Matrix (Fin 2) (Fin 2) Aₙ`, with diagonal identity-qubit
  embeddings.  Its normalized traces are compatible with every stage map,
  and their algebraic directed limit carries the induced algebraic tracial
  state.
- FPU-001 — for every nonempty finite matrix factor, its algebraic tensor
  product with the concrete dyadic algebraic limit carries the checked product
  tracial state.  The theorem includes the elementary-tensor formula
  tr_p(a) times qubitUHFTrace(u).
- FPU-002 — any supplied regional `StarAlgEquiv` into that finite-pure
  product model induces an algebraic tracial state on the regional algebra,
  with the checked formula on inverse images of elementary tensors.
- `AIT-001` — compatible unital cyclic finite-stage functionals glue to a
  unital cyclic linear functional on mathlib's algebraic directed direct
  limit.
- `AIT-002` — compatible stagewise star-algebra maps induce an involutive,
  additive, multiplication-reversing star on that algebraic direct limit.
  Compatible algebraic tracial states then glue to an ordinary algebraic
  tracial state there.
- `SPC-001` — an adapted Hamel basis identifies the label space with finitely
  supported X/Z coordinate labels and maps the singleton coordinate labels to
  the chosen basis vectors.
- ASC-001 — for a selected set of Z coordinates, Lean now identifies the
  corresponding coordinate subspace both as the span of those Z basis
  vectors and as the finite words with no X coordinate and no Z coordinate
  outside the selected set.  This is the exact linear selection criterion
  required before comparing the regional stabilizer state with the
  pure/mixed product state.
- FQS-001 — Lean now reads the recursive finite-qubit Pauli label as its
  finite X/Z coordinate list and proves that the pure/mixed product-state
  indicator is exactly the selected-Z condition: a pure coordinate has no X
  exponent, and a mixed coordinate is the identity label.  Under an arbitrary
  supplied adapted coordinate basis, that condition is literal membership in
  the selected-Z stabilizer submodule.  The coherent direct-limit state theorem
  has a corresponding selected-Z indicator form on source basis words.
- `PCC-001` — a phase-corrected additive map of Pauli labels respects word
  multiplication and star exactly when it satisfies explicit multiplier and
  involution equations.  This isolates the cocycle data that symplecticity
  alone does not supply.  The cross-algebra word-basis extension is now also
  checked: its two compatibility equations and a specified Pauli-word basis
  yield a genuine `StarAlgEquiv`.
- `SCC-001` — the quotient of two multiplier phases is an additive character,
  calibrating by an additive character preserves the multiplier equation, and
  every additive character on a vector subspace extends to the ambient vector
  space along a complementary subspace.  This is the exact algebraic
  stabilizer-sign calibration: the finite-field character is self-conjugate,
  and calibration preserves both Pauli-word compatibility equations.  The
  concrete finite-support quadratic phase is now independently formalized;
  relating it to the actual regional stabilizer convention remains separate.
- QPR-001 — the explicit ZMod 4 finite-support quadratic refinement has its
  polarization and diagonal identities fully checked.  Its discrepancy pairing
  is additive in both words, symmetric for a symmetric discrepancy, and has
  additive order two.  These facts instantiate the cross-algebra Pauli-word
  multiplication and involution certificates and, with a supplied word-basis
  linear equivalence, a `StarAlgEquiv`.
- QPT-001 — the concrete finite-support phase theorem now composes that
  `StarAlgEquiv` with the finite-pure times qubit-UHF trace transport: whenever
  the regional Pauli-word exponents, involution phases, and word-basis map are
  supplied, Lean constructs both the star-algebra equivalence and its induced
  algebraic tracial state with the elementary-tensor product formula.  The
  Pauli-word interface has been weakened from `Ring` to `Semiring`, the exact
  structure carried by the concrete algebraic UHF direct limit.
- PTO-001 — two isometries whose range projections sum to the identity rule
  out even an algebraic unital cyclic trace.  This is the checked obstruction
  behind the infinite-pure-sector case; the tracial-state theorem is therefore
  deliberately limited to a finite pure matrix factor.
- ALT-001 — compatible finite-stage `StarAlgEquiv`s and compatible target
  algebraic tracial states induce a source-side algebraic tracial state on the
  corresponding quasi-local direct limit.  The theorem evaluates it exactly
  on every finite-stage representative.  The concrete finite-pure UHF trace
  now has the matching finite-stage elementary-tensor formula.
- FQP-001 — every finite stage of the dyadic qubit tower now has an explicit
  ordered Pauli-word `StarSystem` and a complex Pauli-word basis.  The
  identity-qubit embeddings preserve its words, basis vectors, multiplication
  multipliers, and star multipliers under coherent label maps.  Thus the UHF
  target-side finite-stage word hypotheses are no longer abstract assumptions;
  assembling them into one global target word system remains open.
- PMS-001 — for every Boolean sequence specifying whether each newly adjoined
  qubit is pure or maximally mixed, the corresponding finite product
  functionals are algebraic states, are compatible with all dyadic embeddings,
  and induce an algebraic state on the UHF direct limit.  Their values on every
  finite Pauli word are proved recursively: pure coordinates permit only zero
  X exponent, while mixed coordinates permit only the identity word.  The
  all-mixed specialization is proved equal to the previously checked UHF
  tracial state.  Lean also proves that even the one-qubit pure specialization
  is not cyclic and hence not an algebraic tracial state.
- PTR-001 — this nontraciality is now proved at arbitrary finite and
  direct-limit coordinates: if any Boolean coordinate is pure, explicit
  matrix units witness a failure of cyclicity.  Consequently the algebraic
  UHF product state is tracial if and only if every coordinate is maximally
  mixed, in which case it is the checked UHF trace.
- CBL-001 — finite-stage star-algebra equivalences need not be assumed
  coherent on every algebra element: if the source connecting maps, target
  vectors, and coordinate maps agree on a specified source basis, Lean proves
  the full commuting square by linear-basis extensionality.
- CPS-001 — a phase-corrected finite coordinate system now has a concrete
  direct-limit state interface.  Coherent source basis transport, phases, and
  finite Pauli labels imply full-stage equivalence coherence and hence a
  star-algebra equivalence to the algebraic qubit-UHF direct limit; the induced
  source state evaluates a basis word as its phase times the pure/mixed Pauli
  selection indicator.  The all-mixed specialization pulls the UHF trace back
  to a source algebraic tracial state; more generally its pure/mixed pullback
  is tracial exactly when every coordinate is mixed.  Constructing the
  regional inputs remains open.
- ACS-001 — if supplied finite-stage regional data identify selected target
  Z-coordinates with the actual source stabilizer words, Lean derives the
  exact phase-calibrated stabilizer expectation formula on every source basis word.
  The stronger form states that hypothesis as literal membership in the
  selected-Z submodule of an adapted coordinate basis.  Thus the remaining
  geometric work is isolated to constructing and coherently transporting that
  coordinate data from a separately supplied finite-coordinate realization,
  rather than to a hidden infinite-algebra assumption. The manuscript does not
  presently supply that realization; see `SOURCE-CONTRACT.md`.
- ALS-001 — compatible finite-stage star-algebra equivalences transport
  compatible algebraic states (not only tracial states) to a quasi-local
  algebraic direct limit.  This is the exact state-level interface required by
  a coherent regional stabilizer-coordinate construction.
- WBE-001 — if Pauli words form a complex linear basis, checking a
  complex-linear map on every pair of basis words proves multiplicativity on
  all finite sums.  The corresponding conjugate-linear basis argument proves
  star preservation; a bijective unital map satisfying both checks is packaged
  as a star-algebra equivalence.
- ALC-001 — a compatible family of finite-stage star-algebra maps induces a
  star-algebra map from the algebraic directed limit.  Compatible finite-stage
  star-algebra equivalences induce a star-algebra equivalence of the two
  algebraic limits.  The C-star norm extension remains open.
- CSE-001 — once a source and target are supplied as complex C-star algebras,
  Lean proves that every complex `StarAlgEquiv` is isometric and therefore
  continuous with continuous inverse.  A continuous target functional pulls
  back continuously along it.  This does not construct C-star norms or
  completions for the algebraic direct-limit models.
- CCF-001 — the pinned Mathlib supports the finite dyadic stages as genuine
  C-star algebras and supports closure/minimality once an ambient C-star
  algebra is supplied.  It does not provide the C-star inductive-limit
  construction for the algebraic dyadic limit; this is recorded as an
  explicit missing API rather than hidden behind an axiom.
- NMC-001 — supplied finite C-star realizations of the coherent coordinate
  maps are isometric and continuous, and the commuting inclusion squares
  preserve the norm estimates.  The resulting dense-subalgebra estimate is
  exactly the analytic input needed before extending the algebraic map to a
  completion; no completion is constructed here.
- BMC-001 — for a star subalgebra of bounded operators on a Hilbert space,
  Lean now constructs the algebraic bicommutant as a concrete
  `VonNeumannAlgebra`, with monotonicity, minimality, membership, and
  idempotence lemmas.  The analytic strong/weak double-commutant theorem is
  still explicitly absent from the pinned Mathlib and remains separate.
- CCC-001 — from an explicitly supplied isometric star representation of a
  pre-C-star algebra into bounded operators, Lean constructs the closed
  operator-range C-star algebra, its isometric dense embedding, and the
  uniqueness equivalence between two such concrete completions.  The faithful
  operator representation of the project-specific algebraic limit is still a
  separate obligation.

## The exact theorem still to prove

The Overleaf short-range theorem asserts a regional von Neumann algebra
isomorphism to a type-I factor tensor a hyperfinite type-II1 factor.  It is
not yet formalized as a theorem because the supplied manuscript proof leaves
the following essential premises open:

1. a finite-support adapted symplectic coordinate map whose finite-stage
   source bases, phase correction, and target Pauli labels are coherent along
   an exhaustion;
2. identification of the actual regional Pauli multiplier and involution
   exponents with the finite-support coordinate discrepancy, followed by
   calibration to the actual stabilizer character;
3. the induced quasi-local C-star isomorphism;
4. factorization of the regional state into pure and normalized-tracial
   coordinate states; and
5. a normal/spatial extension to the respective bicommutants.

The current pinned mathlib version includes preliminary abstract and concrete
von Neumann-algebra definitions, but lacks a finished API for infinite von
Neumann tensor products, normal states/traces, hyperfiniteness, and factor
classification.  The project therefore does not introduce any axiom for the
target theorem.

## Last verification

```text
lake build
lake build Formalization.AlgebraicLimitStateTransport Formalization.QubitMatrixState Formalization.FinitePureMixedQubitState Formalization
lake build Formalization.TraceTransport Formalization
lake build Formalization.CoherentBasisEquiv Formalization.CoherentPhaseQubitState Formalization
lake build Formalization.PureCoordinateNotTracial Formalization
lake build Formalization.AdaptedStabilizerSubspace Formalization
lake build Formalization.FiniteQubitPauliSelection Formalization.CoherentPhaseQubitState Formalization
lake build Formalization.CStarEquivExtension Formalization
lake build AristotleCandidates.CStarInductiveLimitFeasibility AristotleCandidates.FiniteCoordinateMapNormControl
lake env lean /tmp/stabilizer_hyperfinite_axioms_run4.lean
pdflatex -interaction=nonstopmode -halt-on-error .../001-tensor-product-trace.tex
```

Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for the
checked tensor-amplification, concrete dyadic direct-limit trace,
finite-support quadratic-phase, induced-trace, finite-qubit Pauli-word,
pure/mixed product-state, basis-level coherence, phase-corrected direct-limit
equivalence/state transport, and properly-infinite trace-obstruction theorems.
No source theorem contains `sorry`, `admit`, or a user-declared axiom.  The
blueprint build output is kept under `/tmp`, not in this source project.
