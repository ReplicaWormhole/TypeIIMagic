# P59 closeout review — local-hyperbolic factor and trace theorem

## Decision

**Status: compiled Lean infrastructure and conditional transport statements only;
the P59 mathematical gate is not met.  Lane H must halt and the queue must not
advance.**

The exact supervisor-supplied archive
`aristotle_responses/P59-local-hyperbolic-factor-trace-theorem-a12190c2-9efd5c22.tar.gz`
has SHA-256

```text
ac70c29eb711cd0709c2250d6e2845455da4d867dddcd95d825a4b884807dd59
```

It was extracted only into
`aristotle_responses/P59-local-hyperbolic-factor-trace-theorem-a12190c2-9efd5c22-quarantine/`.
No `lake build`, `lake update`, or dependency fetch was run in that quarantine
snapshot.  The only candidate integrated into the live project is the
packet-authorized
`AristotleCandidates/LocalHyperbolicFactorTraceTheorem.lean`; its live and
quarantine SHA-256 values agree exactly:

```text
14dea8cd3df2c61de09a3dd73949f307633e242c7d638921a969823fd9818baf
```

The integration preserves a reproducible audited artifact; it does **not**
accept that artifact as satisfying P59 or authorize an automatic successor.
The archive and quarantine snapshot remain raw response records.  No manuscript
file was modified.

## Source, packet, and predecessor audit

The packet declares source basis `main.tex:1671-1679, 1970-2004`.  That is a
valid exact locator for the local-hyperbolic hypothesis and the later
quasi-equivalence discussion, but the claimed GNS/tensor-factor and mixed-type
content is located in the source contract at `main.tex:1945-1967`.  The packet
does not cite that clause.  It also says to list auxiliary assumptions rather
than itself listing every assumption, exact Lean declaration, and conditional
status, contrary to the packet requirements in `AGENTS.md`.  This review does
not silently repair those packet omissions by treating the returned code as a
manuscript theorem.

P57 and P58 are the declared predecessors.  The P59 quarantine snapshot's
copies of both direct imports are byte-identical to the live copies:

```text
ProductGNSTensorFactorization.lean  6e4549050881ec265bb57f243095ae549de03ce6a8628ad4bf4724e2d3478b07
MixedUHFHyperfiniteFactor.lean      5dbf9ff8c35035c94b37804435793102cb0c59f88c7a39e2746c32274fc67d20
```

P58's live hash agrees with its accepted closeout.  P57's accepted closeout
records `...26557bb...`, while the live file and the P59 snapshot have
`...265bb57...`; this appears to be a transposition in the older review, but
cannot be reconstructed without using an earlier package archive, which this
closeout correctly did not do.  The P59 build therefore validates the current
live predecessor sources, while that older P57 hash-record discrepancy remains
an unresolved provenance warning.

P57 itself explicitly accepted only a generic `ProductGNSData` GNS split and
a bicommutant-defined spatial object; it did not identify its pure closure with
`B(K_pure)`, instantiate the data from P55D/P56R, or prove factor/type/trace
claims.  P58 instead concerns the specific P54 dyadic-UHF representation
`mixedVonNeumann`, conditionally on `MixedWeakClosurePremises`.  These two
accepted results have no integrated bridge between them.

## Exact declarations and assumptions in the candidate

The candidate imports P57 and P58, but it uses no P58 classification
declaration or `MixedWeakClosurePremises` field.  It introduces an arbitrary
`D : ProductGNSData` and calls `(Set.range D.totalRep)''`
`regionalAlgebra D` (lines 765-803).

The relevant declarations are:

- `unitaryConj_image_spatial` (lines 800-803), a restatement of P57's generic
  bicommutant transport;
- `spatialRegionalStarEquiv` (lines 1587-1639), with exact type
  `spatialSubalgebra D ≃⋆ₐ[ℂ] regionalSubalgebra D`.  Its source is P57's
  bicommutant of generic represented ranges, not a theorem identifying that
  object with `B(K_pure) barTensor R_mixed`;
- `regionalAlgebra_hasTrivialCenter` (lines 818-876), conditional on
  `SpatialFactorPremises D`, whose fields are `pure_nontrivial`,
  `pure_commutant`, and the newly supplied
  `mixed_factor : HasTrivialCenterSet (Set.range D.mixedRep)''`;
- `regionalAlgebra_isNormalizedTracialState` (lines 1188-1223), conditional
  on `FinitePureTracePremises D e Omega`, whose fields are `mixed_unit`,
  whole-spatial-algebra `tracial`, and `separating`; and
- `regionalAlgebra_isFaithfulNormalSemifiniteWeight` (lines 1487-1527),
  conditional on `InfinitePureWeightPremises D e Omega`, whose fields are
  `mixed_unit`, `separating`, `semifinite`, and whole-spatial-algebra
  `tracial`.

The finite state is normal only in the candidate's newly defined
`IsFiniteVectorNormal` sense (a finite sum of vector functionals, lines
920-938).  The infinite object is normal only in the candidate's newly defined
`IsFaithfulNormalSemifiniteWeightOn` sense, whose `normal` field says it is a
possibly infinite `vectorWeight` sum (lines 1343-1358).  Neither definition is
proved equivalent to standard ultraweak or sigma-weak normality.

The infinite-weight theorem also lacks an `[Infinite iota]` hypothesis.  That
hypothesis appears only in `regionalAlgebra_weight_one_eq_top` (lines
1531-1537).  Hence the candidate does not formalize a disjoint finite/infinite
pure-sector dichotomy, even though it correctly proves that its ENNReal-valued
functional is not a state when that separate infinitude hypothesis is supplied.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | Lean proves the candidate's generic Hilbert-tensor amplification lemmas, transport along P57's product-GNS unitary, the explicitly conditional centre transport, finite vector-functional calculations, and ENNReal vector-weight calculations.  The candidate does not introduce `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, `implemented_by`, or `native_decide`. |
| partial | The returned module gives a reusable conditional P57-level transport layer.  Its finite trace and infinite weight conclusions are conditional on named fields, and its `normal` predicates are project-local certificates rather than standard normality. |
| blocked | No theorem instantiates `ProductGNSData` with the concrete P55D/P56R regional model; no theorem identifies P57's mixed representation with P58's `mixedVonNeumann`; no theorem transports P58's three weak-closure premises to `D.mixedRep`; and no theorem identifies the pure closure with `B(K_pure)`.  Those bridges are essential before P58 can discharge the candidate's fresh `mixed_factor`, trace, or weight premises. |
| failed | The P59 gate stated in the packet and `PLAN.md` is not met: the candidate does not transport P57--P58 to the asserted regional `B(K_pure) barTensor R_mixed` model, prove its factor conclusion from those predecessors, or establish the stated finite/infinite trace-weight dichotomy at the standard normality scope. |

The first fatal gap is the replacement of the required P58 transport by the
new `SpatialFactorPremises.mixed_factor` field at lines 818-825.  A source
audit finds no use in P59 of `mixedVonNeumann`, `MixedWeakClosurePremises`,
`uhfVectorState`, or P58's classification theorem.  Importing P58 and citing
it in comments is not a connection to its theorem.

## Plan alignment

- **Package and lane:** `P59`, Lane `H` — declared correctly.
- **Predecessors:** P57 and P58 are present and live-built, but the candidate
  uses P57's generic transport only.  The required P57-to-P58/regional bridge
  is absent; P58 is not a mathematically used predecessor at this gate.
- **Permitted gate:** not discharged.  The actual type of
  `spatialRegionalStarEquiv` is an isomorphism of P57's two generic
  bicommutant-defined star subalgebras, not the requested regional
  `B(K_pure) barTensor R_mixed` theorem.  Factor, finite trace, and infinite
  weight statements require newly supplied premise bundles.
- **Forbidden downstream claims:** respected in the narrow sense.  The module
  makes no Lane-G/general-central-decomposition claim and does not call the
  infinite ENNReal-valued functional a tracial state; with `[Infinite iota]`
  it proves its value on `1` is `top`.  These scope protections do not cure the
  missing permitted-gate proof.

## Verification in the live project only

- `lake build AristotleCandidates.LocalHyperbolicFactorTraceTheorem` — passed
  (`8074/8074` jobs, 71 seconds).
- `lake build AristotleCandidates.ProductGNSTensorFactorization AristotleCandidates.MixedUHFHyperfiniteFactor AristotleCandidates.LocalHyperbolicFactorTraceTheorem Formalization` — passed (`8102` jobs).
- `lake build` — passed (`0` additional jobs).
- `lake env lean --stdin` with `#print axioms` for
  `spatialRegionalStarEquiv`, `regionalAlgebra_hasTrivialCenter`,
  `regionalAlgebra_isNormalizedTracialState`,
  `regionalAlgebra_isFaithfulNormalSemifiniteWeight`, and
  `regionalAlgebra_weight_one_eq_top` — each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Declaration and token scan of the P59 candidate and direct P57/P58 imports —
  no forbidden declaration/token found.
- Live/quarantine candidate SHA comparison, direct-import SHA comparisons, and
  `git diff --check` / new-file whitespace check — passed.

Compilation and axiom reports validate the stated Lean declarations; they do
not supply the missing regional-model, pure-factor, P57-to-P58, standard
normality, or weight-semifiniteness mathematics.

## Adversarial review

Artifact types reviewed: Lean code, mathematical formalization, source-backed
scope, and workflow closeout.

Findings, highest severity first:

1. **Critical:** P59 never connects P57's arbitrary product datum to P58's
   concrete mixed-UHF weak closure, so its factor theorem assumes instead of
   derives the key mixed-factor input.
2. **High:** the advertised spatial `B(K_pure) barTensor R_mixed` theorem has
   no matching Lean type; the actual source is only P57's generic bicommutant.
3. **High:** the words “normal tracial state” and “faithful normal semifinite
   weight” rely on new project-local predicates without a standard
   ultraweak/sigma-weak comparison theorem.
4. **Medium:** the alleged infinite-pure theorem is not indexed by an infinite
   basis; only its separate non-state corollary is.
5. **Medium:** P59's source packet omits the manuscript product/type locator
   and does not predeclare the exact auxiliary assumptions; P57's recorded
   candidate hash has an unreconciled transposition.

No unrelated pre-existing change was overwritten, reverted, reformatted, or
committed.  The sole new source artifact is the exact P59 candidate, retained
with this review for reproducibility; the exact archive/quarantine extraction
and the existing `.lake` cache are intentionally retained.  No dependency
update, fetch, commit, push, Aristotle submission, or manuscript edit was
performed.
