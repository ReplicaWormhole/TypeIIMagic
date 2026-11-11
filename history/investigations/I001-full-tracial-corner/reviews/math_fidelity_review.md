---
status: passed
reviewer: gpd-check-proof
claim_ids:
  - "thm:full_tracial_corner_semifinite"
  - "lem:mvN_witness_in_corner"
  - "cor:finite_fiber_finite_projection"
proof_artifact_paths:
  - "work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/QUESTION.tex"
  - "work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/technical.tex"
  - "formalization_finite_fibers/FiniteFiber/Basic.lean"
  - "formalization_finite_fibers/FiniteFiber/TracialCorner.lean"
  - "formalization_finite_fibers/FiniteFiber/FiniteFibers.lean"
  - "writing/overleaf_prl_stabilizer_region_algebras/main.tex"
missing_parameter_symbols: []
missing_hypothesis_ids: []
coverage_gaps: []
scope_status: matched
quantifier_status: matched
counterexample_status: none_found
---

# Proof Redteam

## Proof Inventory

**Exact target.**  `QUESTION.tex:22--32` asks whether a full projection $q$ for
which $q\cM q$ has a faithful tracial state yields a nonzero finite projection
in every nonzero central summand $z\cM$.

**Exact theorem under review.**  `technical.tex:388--405` states: “Let
$\cM\subseteq\cB(\cH)$ be a concrete von Neumann algebra.  Let
$q\in\cM$ be a full projection, and assume
Assumption~\ref{ass:faithful_tracial_projection_functional}.  Then $\cM$ is
semifinite in the sense of Definition~\ref{def:semifinite_projection_form}.”
The corresponding checked declaration is
`FiniteFiber.full_tracial_corner_semifinite` in
`formalization_finite_fibers/FiniteFiber/FiniteFibers.lean:46--57`.

**Manuscript comparison.**  The source-of-truth functional has domain
$qM_\Gamma q$ (`writing/overleaf_prl_stabilizer_region_algebras/main.tex:1150--1158`),
is made tracial on that corner at `:1265--1315`, and is used only after the
support bridge $v=qvq$ at `:1426--1450`.  The final central-slice conclusion
is at `:1501--1539`.  The revised abstraction now has exactly the same corner
domain and bridge.

**Named parameters and hypotheses.**

- A complex Hilbert space $\cH$ and concrete von Neumann algebra $\cM$.
- A full projection $q\in\cM$.
- A linear functional whose restriction is tracial on the explicitly supported
  corner elements and detects zero projections below $q$.
- An arbitrary nonzero central projection $z$, and, for the specialization,
  an explicitly indexed nonzero central projection $z_i$.

**Conclusion clauses.**  The central theorem must provide a nonzero finite
$zq\leq z$ for every nonzero central $z$.  The finite-fiber theorem must expose
the canonical witness $z_iq$; it is not required to formalize a direct
integral, a factor assertion, or a bundled `not_typeIII` theorem.

## Coverage Ledger

### Named-Parameter Coverage

| Parameter | Status | Notes |
|---|---|---|
| $\cM\subseteq\cB(\cH)$ | covered | The Lean package uses `VonNeumannAlgebra H`; no competing algebra notion is introduced. |
| Projection and fullness of $q$ | covered | `IsFullProjection` includes membership/projection data and the exact nonzero-central-slice condition (`Basic.lean:48--51`). |
| Corner functional | covered | `FaithfulTracialCorner.tracial` quantifies only over `IsCornerElement M q a` and `... b` (`TracialCorner.lean:24--29`), matching the manuscript's domain. |
| Central projection $z$ | covered | The proof selects $z*q$, proves it finite, nonzero, and below $z$ (`FiniteFibers.lean:26--57`). |
| Finite-fiber label $z_i$ | covered | `finite_central_fiber_canonical_witness` exports the precise witness $z_i*q$ (`FiniteFibers.lean:59--69`). |

### Hypothesis Coverage

| Hypothesis | Status | Notes |
|---|---|---|
| Faithful tracial state on $q\cM q$ | covered by the abstract interface | For $a,b\in q\cM q$, the corner state gives traciality; for $r\leq q$, its faithfulness gives the required zero-detection.  The ambient carrier of `tau` is only a linear-extension wrapper; no trace law is asserted outside the corner. |
| Standard Murray--von Neumann witness convention | covered | The public equivalence remains $v^*v=e$, $vv^*=f$ (`Basic.lean:34--36`).  `isPartialIsometry_of_star_mul_eq_projection` derives, rather than assumes, $vv^*v=v$ (`Basic.lean:82--108`). |
| Witness belongs to the corner before trace use | covered | `mvN_witness_in_corner` proves $qv=v=vq$ and the adjoint identities (`TracialCorner.lean:36--85`); the finite proof invokes it before `T.tracial` (`:95--112`). |
| Fullness | covered | It is used only to establish $zq\ne0$, precisely as in the manuscript. |
| Normality and the stabilizer/GNS realization | correctly out of scope | Normality is unnecessary for the finite-projection argument.  The four GNS construction obligations remain explicitly deferred at `technical.tex:452--478`. |

### Quantifier / Domain Coverage

| Obligation | Status | Notes |
|---|---|---|
| For every nonzero central $z$ | covered | `IsSemifinite` has exactly this quantifier (`Basic.lean:53--57`). |
| Traciality for every pair in $q\cM q$ | covered | The two support equalities in `IsCornerElement` encode this domain; no ambient-$\cM$ trace is required. |
| Every equivalent subprojection $f\leq e\leq q$ | covered | The proof obtains a standard witness, derives its partial-isometry identity and corner support, then applies traciality to $v^*,v$. |
| Every supplied finite-fiber index $i$ | covered | The canonical-witness theorem is pointwise in $i$; partition and factor data are intentionally unnecessary for this implication. |

### Conclusion-Clause Coverage

| Conclusion | Status | Notes |
|---|---|---|
| Nonzero finite projection below each nonzero central $z$ | covered | The checked witness is $z*q$ (`FiniteFibers.lean:51--57`). |
| Canonical finite-fiber witness | covered | `finite_central_fiber_canonical_witness` states finiteness, nonzeroness, and $z_iq\leq z_i$ together (`FiniteFibers.lean:59--69`). |
| A finite projection in the central summand $z_i\cM$ | covered at the stated ambient strength | Ambient finiteness of $z_iq\leq z_i$ implies finiteness for witnesses restricted to the central summand.  The package deliberately has not bundled that summand as an algebra on $z_i\cH$. |
| Type-III exclusion for factor fibers | correctly deferred | `technical.tex:439--449` does not represent it as machine checked. |

## Adversarial Probe

**Probe type:** replay the previous infinite-dimensional type-I obstruction and
test the standard-witness boundary.

**Result:** Take $\cM=\cB(\ell^2(\mathbb N))$ and let $q$ be rank one.  The
corner is $\mathbb Cq$, $q$ is full, and the corner state is faithful and
tracial.  The previous failed interface demanded trace equality for the
unilateral shift $S$ and $S^*$, forcing $\tau(q)=0$.  The revised interface
does not admit that invalid test: $S$ and $S^*$ are not corner elements, so no
traciality is required for that pair.  On the actual corner the state supplies
all fields used by the proof, and the witness $q$ is finite.

For the witness bridge, $v^*v=e$ with $e$ a projection gives
$vv^*v=v$ by `Basic.lean:88--108`.  If $f\leq e\leq q$ and
$vv^*=f$, this yields $v=ve=fv$, hence $v=qvq$.  This reproduces the precise
load-bearing step in the manuscript rather than assuming a different
Murray--von Neumann convention.

## Verdict

APPROVED

Scope status: `matched`.  Quantifier status: `matched`.  Counterexample
status: `none_found`.

The prior mathematical-fidelity blockers are resolved: the theorem no longer
requires an impossible ambient trace, the standard witness convention is
preserved, the corner-support bridge is proved before trace use, and the public
finite-fiber API names the canonical witness.  The abstract Lean result is
mathematically aligned with the valid algebraic content of
`main.tex:1150--1539`.

The TeX blocker has been repaired: `technical.tex` now supplies the short title
through the optional argument of `\title`.  Independent temporary-output builds
of both `technical.tex` and `QUESTION.tex` completed with exit status zero; the
final logs contained no undefined-reference or overfull-box diagnostics.  A
visual inspection of the rebuilt five-page technical PDF found no clipping or
overlap, including the reformatted Lean API declarations.

Lean verification passed independently: the three narrow `lake env lean`
checks and `lake build -v` completed successfully, no placeholders were found,
and `#print axioms` for the five load-bearing public theorems reported only
`propext`, `Classical.choice`, and `Quot.sound`.

This approval covers the conditional abstract finite-projection theorem.  It
does not certify a Lean construction from a bundled corner state, the GNS
input, or the represented central-corner type-III statement.

## Required Follow-Up

1. None before treating the stated abstract finite-projection theorem as
   established.
2. To machine-check the state-level input itself, introduce a bundled tracial
   state on $q\cM q$ and an adapter into `FaithfulTracialCorner` (or type
   `tau` directly on the corner).  A linear extension outside $\cM$ is an API
   convenience, not a traciality requirement or a missing hypothesis of the
   abstract theorem.
3. Keep the stabilizer/GNS realization and represented-corner `not_typeIII`
   theorem marked as future work, as the current note already does.
