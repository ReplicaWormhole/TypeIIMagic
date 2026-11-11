# Two-lane formalization decision

Date: 2026-08-07

The active Codex/Aristotle loop follows the two-lane plan in `PLAN.md`.

**Lane G** formalizes the manuscript's general-lattice corner argument:
the strong-limit code projection `q`, the faithful normal finite tracial state
on `q M_Gamma q`, finiteness and fullness of `q`, and the conclusion that each
nonzero central summand has a nonzero finite projection and hence is not type
III. This route does not use a direct integral and does not require a global
trace/weight on `M_Gamma`.

**Lane H** formalizes the explicit short-range/local-hyperbolic model:
coherent coordinate maps, an algebraic and C-star `alpha`, the product-state
identity, product GNS tensor factorization, and the resulting factor and
trace/weight classification.

The lanes meet only after their own gates are met. In particular, the explicit
tensor-factor result proves trivial center in the special local-hyperbolic
case, whereas the general corner result rules out type-III central summands
without asserting trivial center.

The first approved parallel Aristotle wave is P47, P48, P52, and P54. No
dependent packet should be submitted before its prerequisite results are
integrated and semantically audited.

Amendment, 2026-08-07: the analytic passage from the compressed quasi-local
C-star algebra to the von Neumann corner is mandatory project infrastructure.
After P48, the loop must prove strong closedness of concrete von Neumann
algebras (P49A), the analytic double-commutant theorem (P49B), and Kaplansky
unit-ball density with its compressed-corner corollary (P49C). P50 depends on
both the finite-stage/C-star trace P49 and the proved P49C result. These core
analytic theorems may require new local topology machinery, but may not be
replaced by axioms or supplied interfaces.

Amendment, 2026-08-08: P50's checked WOT continuity is retained as a stronger
concrete certificate, but the field name alone is not accepted as a
formalization of the standard ultraweak definition of normality. Package P50U
must define the ultraweak topology from absolutely summable series of matrix
coefficients, prove the topology comparison, and export an explicitly
ultraweak-normal P50 conclusion. This does not block P51's finite-projection
argument, which uses the corner state's traciality and faithfulness rather than
normality.

Amendment, 2026-08-08: the original P55 is retired after Aristotle returned
`OUT_OF_BUDGET` without creating `RegionalConcreteCStarAlpha.lean`. The failed
run is not evidence and no code from it is integrated. Lane H now uses four
separate gates: P55A constructs finite-stage Pauli-to-dyadic equivalences,
P55B proves coherence and the finite/infinite direct-limit identifications,
P55C constructs faithful source/regional operator representations and their
closed ranges, and P55D extends the algebraic alpha by density. This split is
mathematical: P53 and P54 did not yet contain an identification between their
two different algebraic direct limits. P56 depends on accepted P55D.

P60 may run independently of Lane H after P51 and P50U. It is optional Lane-G
strengthening and must use P50U's literal ultraweak-normal corner state. It may
assume an explicitly named countable comparison family for the full corner,
but it may not infer a global weight from fullness alone or conceal the weight,
normality, faithfulness, traciality, or semifiniteness laws in an axiom.

Amendment, 2026-08-08: P60 compiled and its conditional weight-series,
traciality, faithfulness, corner restriction, and finite-compression results
are preserved, but P60 is not accepted as the optional global-weight theorem.
The closeout's P51 provenance objection was stale: P51 is accepted in
`reviews/P51-full-finite-corner-central-exclusion-recovery.md`. The genuine
remaining gap is standard semifiniteness on the positive cone. P60R may revise
the P60 candidate in place, but must prove that for each nonzero positive
`x ∈ M` there is a nonzero positive `y ≤ x` of finite weight. It must construct
the required positive square-root/factorization argument from Mathlib or
local proved C-star theory; that factorization may not be a new hypothesis.

Amendment, 2026-08-10: P56 is retained as a partial, reviewed artifact. Its
finite-word and algebraic direct-limit identities are useful, but its concrete
extensions depend on `ProductStateBound` and no positivity theorem was proved.
P56R replaces it as the Lane-H state gate and must derive a genuine unital
positive C-star functional directly from the finite pure/mixed density-matrix
data and the P55D concrete alpha. The original P56 job is disabled rather than
rewritten, so the distinction remains machine-visible.

In parallel, P57A ports the *proved* finite-support vacuum-restricted infinite
tensor pre-Hilbert construction from the compatible Lean-4.28 `bound_beating`
workspace into this repository as shared infrastructure. This is a local port,
not a cross-project import. Its optional completion/axiom wrapper is explicitly
excluded: P57A can establish the algebraic kernel, finite-mode realization,
positivity, sesquilinearity, and pre-inner-product core, but the completed
Hilbert-space and spatial tensor claims remain P57 work and must be proved
against the local Mathlib API.

Amendment, 2026-08-10: P59 is retained only as an audited partial artifact.
It restated P57's generic transport but did not construct a `ProductGNSData`
from the P55D/P56R local-hyperbolic model, did not identify that datum's mixed
GNS representation with P58's `mixedVonNeumann`, and replaced the required
factor and trace inputs with fresh premise bundles. The recovery is therefore
split into proof gates: P59A constructs the concrete product datum; P57B
constructs the actual Hilbert completion of the P57A vacuum core; P57C proves
the pure type-I factor; P59B proves the mixed-UHF bridge; and P59R transports
the resulting factorization to the regional algebra. P59T treats traces and
weights only after P59R, using standard ultraweak normality and an explicit
infinite-pure hypothesis for the weight branch.
