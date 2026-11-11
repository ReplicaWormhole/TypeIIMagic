# Active plan: two-lane stabilizer-algebra formalization

## Decision — 2026-08-07

The project now has two parallel mathematical targets sharing finite
stabilizer and operator-algebra infrastructure, but neither is allowed to
silently supply the other one's hypotheses.

### Lane G — general lattices and central type-III exclusion

**Source basis:** `main.tex:332-342`, with the corner proof at
`main.tex:1026-1536`.

For a general consistent stabilizer system and region, construct the decreasing
local-code projection tower, its strong limit `q`, and the finite corner
`q M_Gamma q`. Prove that the vector functional `tau_q` is a faithful normal
tracial **state** on that corner, hence that `q` is finite; prove `q` is full;
and derive that every nonzero central projection `z` has `zq != 0` finite in
`z M_Gamma`. Conclude that no nonzero central summand is type III.

This lane does **not** require a direct-integral formalization or a global
trace/weight on `M_Gamma`. A global faithful normal semifinite weight is a
separate optional strengthening. The condition to formalize is the existence
of a nonzero finite **projection/corner** in each nonzero central summand, not
merely a finite-dimensional subalgebra.

### Lane H — explicit local-hyperbolic tensor-factor model

**Source basis:** `main.tex:1671-1679`, `main.tex:1898-2004`.

From a coherent local hyperbolic basis, construct the finite coordinate maps,
their coherent algebraic direct-limit star equivalence, concrete C-star
models, the state identity, and the product GNS tensor splitting. Then prove
the special regional algebra is spatially isomorphic to

`B(K_pure) barTensor R_mixed`.

After proving the two factors and their spatial tensor product, derive the
trivial-center/factor conclusion for this special case. This conclusion does
not follow merely from the word "hyperbolic"; it follows from the constructed
spatial factorization.

### Reconnection

Lane H gives an explicit factor theorem and, in the infinite-pure case, the
concrete faithful normal semifinite weight `Tr barTensor tau`. Lane G gives
the general no-central-type-III theorem. A final comparison theorem may show
that the Lane-H factor model satisfies the Lane-G finite-corner criterion, but
the two results remain logically independent.

## Aristotle package sequence

### Shared/central core

| Packet | Lean target | Purpose and acceptance gate |
|---|---|---|
| P47 | `CenterFiniteProjectionCore.lean` | Define center, central projections, finite projections, corners, central support, and fullness for the concrete von Neumann-algebra model. Prove only algebraic order/corner lemmas; no direct integral. |
| P48 | `GeneralLatticeProjectionTower.lean` | Formalize the general-lattice exhaustion, local code projections, monotonicity, and the strong-limit projection `q`. If the stabilizer definitions do not imply a required limit fact, expose it as an auxiliary hypothesis. |
| P49 | `FiniteCornerTrace.lean` | Derive finite-stage trace cyclicity and pass it to the compressed quasi-local C-star algebra. Keep finite codespace density data explicit. |
| P49A | `StrongOperatorClosedVonNeumann.lean` | Develop the strong-operator convergence/closure API needed for concrete operator algebras; prove commutants and hence concrete von Neumann algebras are strongly closed. This is a proved infrastructure theorem, not an interface. |
| P49B | `VonNeumannBicommutantTheorem.lean` | Prove the analytic double-commutant theorem for a unital complex star subalgebra of bounded operators: its bicommutant is its strong-operator closure. Develop the required finite amplification/cyclic-subspace machinery locally when Mathlib lacks it. |
| P49C | `KaplanskyDensity.lean` | Prove bounded/unit-ball Kaplansky density for the represented C-star algebra in its bicommutant and derive the compressed-corner approximation used by the manuscript. No supplied density interface is accepted. |
| P50 | `NormalFaithfulCornerTrace.lean` | Using P49 and P49C, prove traciality of `tau_q` on `q M_Gamma q` by bounded strong approximation, prove faithfulness, and establish the stronger concrete WOT-continuity certificate that P50U will translate into the standard ultraweak-normal interface. |
| P50U | `UltraweakNormality.lean` | Define the concrete ultraweak topology from absolutely summable matrix-coefficient series, prove the ultraweak-to-WOT identity is continuous, and upgrade P50's WOT-continuity certificate to literal ultraweak normality. This is mandatory infrastructure and may not alias ultraweak topology to WOT/SOT/norm. |
| P51 | `FullFiniteCornerCentralExclusion.lean` | Prove `q` finite, prove fullness, and derive `0 != z ->` a nonzero finite projection in `z M_Gamma`; define/use the project-local type-III obstruction. |

### Explicit local-hyperbolic lane

| Packet | Lean target | Purpose and acceptance gate |
|---|---|---|
| P52 | `CoherentLocalHyperbolicCoordinates.lean` | Build finite coordinate blocks and an exhaustion from local hyperbolic data. Audit whether finite support suffices; otherwise isolate the exact local-finiteness/coherence assumption. |
| P53 | `LocalHyperbolicAlgebraicAlpha.lean` | Construct the finite stage maps, phase calibration, and coherent algebraic `alpha`; instantiate the existing direct-limit theorems without supplied stage equivalences. |
| P54 | `UHFReferenceRepresentation.lean` | Construct a faithful compatible Hilbert/operator representation of the dyadic algebra from finite stages; do not assume an infinite tensor-product Hilbert space. |
| P55A | `LocalHyperbolicFiniteStageUHFBridge.lean` | Construct, rather than assume, the finite-stage star equivalence from each P53 coordinate Pauli algebra to the corresponding finite dyadic matrix algebra, with explicit generator/phase formulas and norm control. |
| P55B | `LocalHyperbolicSourceUHFBridge.lean` | Prove coherence of the P55A maps and identify the P53 source direct limit with the coordinate dyadic limit; prove the finite terminal-stage and infinite cofinal-UHF branches separately. |
| P55C | `LocalHyperbolicConcreteRepresentations.lean` | Transport the P54 faithful representation through P55B and P53 alpha, and construct the source and regional closed operator-range C-star algebras with faithful dense embeddings. |
| P55D | `RegionalConcreteCStarAlpha.lean` | Extend the P53 algebraic alpha uniquely between the P55C concrete C-star closures and prove the inverse and dense-range identities. |
| P56 | `RegionalProductStateIdentity.lean` | Retired partial result: it proves the finite-word/algebraic state equality and conditional continuous-extension uniqueness, but does not prove C-star boundedness or positivity. |
| P56R | `RegionalProductStateIdentity.lean` | Recovery after P55D: construct the pure/mixed product C-star state from finite-dimensional density-matrix estimates, prove positivity/unitality and transport it through `alpha`; no supplied norm bound. |
| P57A | `VacuumRestrictedInfiniteTensorProduct.lean` | Shared infrastructure: port and audit the proved finite-support vacuum-restricted infinite-tensor pre-Hilbert core from `bound_beating`; do not import external projects or package a completion as an axiom. |
| P57 | `ProductGNSTensorFactorization.lean` | After P54, P56R, and P57A, construct the pure/mixed product GNS Hilbert-space tensor splitting and the spatial represented-algebra identification. |
| P58 | `MixedUHFHyperfiniteFactor.lean` | Construct/prove the finite mixed matrix and infinite mixed hyperfinite-II1 alternatives under project-local factor and normal-trace definitions. |
| P59 | `LocalHyperbolicFactorTraceTheorem.lean` | Retired partial transport artifact: it compiles conditional centre/trace/weight transports but introduces unproved bridge and local-normality premises, so it is not evidence for the Lane-H theorem. |
| P59A | `ConcretePureMixedProductData.lean` | Construct the pure/mixed coordinate C-star subalgebras, their commuting dense product decomposition, and the concrete `ProductGNSData` instance directly from P55D/P56R. |
| P57B | `VacuumRestrictedITPCompletion.lean` | Starting from P57A's proved finite-support core, construct the null-space quotient/completion as an actual Hilbert space with dense algebraic embedding; no completed ITP interface may be assumed. |
| P57C | `PureGNSFactor.lean` | Identify the concrete pure component of P59A with the P57B vacuum product representation and prove its represented von Neumann closure is the full `B(K_pure)` factor. |
| P59B | `MixedGNSUHFBridge.lean` | Identify P59A's mixed GNS representation with P58's dyadic-UHF model and transport its factor/tracial structure; no fresh mixed-factor premise. |
| P59R | `RegionalFactorTransport.lean` | Combine P57, P57C, and P59B to identify the regional represented algebra with the concrete spatial product and prove trivial centre/factorhood. |
| P59T | `RegionalTraceWeight.lean` | Separately prove the finite-pure tracial-state and infinite-pure semifinite-weight results using a standard ultraweak-normal interface; never use P59's local vector-normal predicates as substitutes. |

### Optional strengthening/reconnection

| Packet | Lean target | Purpose |
|---|---|---|
| P60 | `FullCornerSemifiniteWeight.lean` | Retired partial attempt: it constructs a conditional extended-positive trace series and finite-compression certificate, but does not yet prove standard positive-cone semifiniteness. |
| P60R | `FullCornerSemifiniteWeight.lean` | Recovery: define the weight on the positive cone and prove standard semifiniteness using positive square roots and the finite comparison projections. |
| P61 | `HyperbolicImpliesCentralCriterion.lean` | Show the explicit Lane-H model supplies the finite-corner criterion used by Lane G. |

## Initial parallel wave

Submit only the four independent foundation packets first: P47, P48, P52,
and P54. Integrate and semantically audit them before submitting dependent
packets. Existing P42--P46 task drafts are preserved as historical drafts;
they are not evidence and must be re-scoped against this plan before reuse.

## Non-negotiable gates

1. No claim that `q M_Gamma q` has merely a semifinite weight when the
   construction actually targets a finite faithful normal tracial state.
2. No claim of a global trace/weight on `M_Gamma` from the finite-corner
   theorem alone.
3. No claim that a finite-dimensional subalgebra excludes type III; the proof
   must produce a nonzero finite projection in every nonzero central summand.
4. No claim that hyperbolic data imply a factor before the spatial tensor
   factorization and factorhood of both factors are proved.
5. Every manuscript-facing packet identifies an exact `main.tex` locator and
   every extra analytic hypothesis appears as a named field, never an axiom.
6. P49A--P49C are mandatory proved infrastructure. P50 may not replace the
   bicommutant theorem or Kaplansky density by a supplied structure field; an
   incomplete analytic package halts Lane G and triggers review.
7. P50's WOT-continuity theorem is a mathematically stronger certificate but
   is not itself the standard definition of normality. P50U must formalize the
   actual ultraweak topology and checked comparison before the project reports
   the corner state as ultraweak-normal in the formal interface. P51's
   finiteness/fullness proof is logically independent because it uses only
   traciality and faithfulness.
8. The original P55 exhausted its remote budget without producing its
   authorized Lean file. It is retired, not accepted. P55A--P55D replace it
   and expose the previously missing bridge between P53's twisted-Pauli direct
   limit and P54's dyadic UHF model. P56 may advance only after P55D is
   integrated and audited.
9. P56 is preserved as a partial artifact, not accepted evidence: its
   `ProductStateBound` is an explicit missing C-star norm estimate and it has
   no positivity theorem. P56R must derive the bound and positivity from the
   finite-dimensional density-matrix data and P55D's concrete C-star model;
   it may not use `ProductStateBound` in its final declarations or proofs.
10. P57A may reuse the algorithmic finite-support construction in
    `bound_beating/formalize_itp`, but only by an audited local port. It may
    not import that separate project, copy its optional completion/axiom
    wrappers, or claim a completed Hilbert tensor product before the quotient
    and completion API is actually proved.
11. P59 is a preserved partial transport artifact, not an accepted theorem.
    P59A must construct, rather than assume, the `ProductGNSData` used by P57;
    P59B must connect that datum to P58's `mixedVonNeumann`; and P57C must
    establish the pure type-I factor. P59R may use only those proved bridges.
    The finite/infinite trace conclusions are separated into P59T, where the
    normality predicate must be standard ultraweak normality and the infinite
    branch must carry an explicit infinitude hypothesis.

---

# Previous single-lane plan: retained background

## Objective

Formalize, from the manuscript's actual finite-support adapted-coordinate data,
a state-preserving C-star isomorphism from the quasi-local Pauli algebra to the
regional algebra.  Obtain the represented von Neumann algebra equivalence by
the canonical GNS unitary, then apply an independently established product
factor classification.

The source basis is exclusively `SOURCE-CONTRACT.md` and the cited manuscript
locators.  In particular, no gLU/refinement/layer-coherence premise is allowed
unless later added explicitly as a new auxiliary assumption.

## Current position

The project already has checked conditional interfaces for:

1. finite Pauli/stabilizer coordinates and pure/mixed states;
2. algebraic direct limits, their induced algebraic equivalence `alpha`, and
   compatible state transport;
3. supplied C-star completions and a supplied C-star extension of `alpha`;
4. GNS transport for supplied compatible C-star states; and
5. supplied normal/product-factor transport.

These are scaffolding.  They do not discharge the manuscript-specific finite
coordinate construction or the product-factor classification.

## Phase A — exact finite coordinate theorem

**Goal:** Replace abstract finite-stage star equivalences by maps constructed
from a finite restriction of the adapted symplectic basis.

1. Specify a finite region/exhaustion and the finite Pauli label spaces.
2. Define the coordinate map from the adapted `z_i,x_i` data.
3. Prove the Pauli multiplier and star equations, including the required phase
   correction.
4. Prove the map is a finite-stage complex star-algebra equivalence.
5. Prove its stabilizer membership criterion and the finite product-state
   expectation formula.

**Gate A:** no supplied finite-stage star equivalence remains in the finite
manuscript theorem; only explicitly stated finite adapted-coordinate data does.

## Phase B — coherence and quasi-local C-star isomorphism

**Goal:** Construct the actual C-star isomorphism `alpha`, rather than assume
an algebraic or completed extension.

1. Prove the Phase-A maps commute exactly with all finite-region inclusions.
2. Form the algebraic direct-limit star equivalence.
3. Specify the quasi-local C-star completions as inductive-limit completions.
4. Prove the algebraic map is isometric on the dense quasi-local subalgebras.
5. Extend it uniquely to a C-star star-algebra equivalence
   `alpha : P_quasilocal ≃⋆ₐ[ℂ] A_regional`.

**Gate B:** P23 and P25 are instantiated by proved data, not used as supplied
interfaces.

## Phase C — state identity and GNS transport

**Goal:** Prove the regional state pulled back by `alpha` is the pure/mixed
product state.

1. Check equality on finite Pauli-word bases using Phase A's stabilizer
criterion.
2. Prove compatibility under inclusions and hence equality on the quasi-local
C-star algebra by density/continuity.
3. Instantiate the existing C-star/GNS bridge to obtain the canonical GNS
unitary and its intertwining identity.
4. Use conjugation by that unitary to identify the represented von Neumann
algebras.

**Gate C:** do not use a separate quasi-equivalence/normal-folium argument.
It is unnecessary once the state-preserving C-star isomorphism is proved.

## Phase D — product representation classification

**Goal:** Independently prove or source the product-state representation
theorem.

1. Split coordinate indices into pure and mixed sectors.
2. Establish the infinite-product GNS factorization.
3. Identify the pure sector as `B(K_pure)`.
4. Identify the mixed sector as a finite matrix factor when finite, or the
hyperfinite `II_1` factor when infinite.
5. Establish the spatial tensor-product identification of the product
representation.

**Gate D:** every analytic theorem is either formalized against a supported
Mathlib API or recorded as an exact external theorem with source locator and
explicit hypothesis.

## Phase E — theorem and trace corollaries

1. Transport the Phase-D product classification through the Phase-C GNS
unitary to the regional von Neumann algebra.
2. State the finite-pure and infinite-pure cases separately.
3. Finite pure sector: derive the normalized tracial-state conclusion.
4. Infinite pure sector: state the faithful normal semifinite trace/weight
conclusion; do not call it a tracial state.
5. Audit every conclusion against `main.tex:1740-1752` and record any required
manuscript correction separately.

## Parallelization

Until Phase B is blocked on a single coherent-coordinate construction, run in
parallel:

- finite phase/cocycle verification;
- finite adapted-coordinate/stabilizer-state verification;
- finite inclusion/coherence lemmas;
- Mathlib/API feasibility audits for C-star inductive limits and GNS products;
- product mixed-sector classification/source work.

Do not parallelize mutually dependent attempts at the same global `alpha`.
Each new Aristotle packet must use `aristotle_tasks/TEMPLATE.md` and state its
source basis plus every auxiliary assumption.

## Exit criterion

Call the manuscript theorem formally established only when Gates A--D are
discharged and Phase E compiles without substituting supplied interfaces for
the central finite-coordinate, C-star-extension, state-identity, or
product-classification claims.
