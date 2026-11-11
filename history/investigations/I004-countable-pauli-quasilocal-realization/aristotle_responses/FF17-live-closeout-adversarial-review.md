# FF17 live closeout — full-Pauli stabilizer density

**Decision: ACCEPTED at the packet's stated finite-volume scope.**

## Quarantine and integration

- Aristotle project: `a8623a7e-5752-4e4d-9667-d3c741247c1f`; completed task:
  `44158f6b-4673-4e26-9871-9fc7717c0353`.
- Raw archive retained at `FF17-full-pauli-stabilizer-density.tar.gz`, SHA-256
  `7e86f988e2118b9e43141f319f65b9ccf5ae0802be34147d670212acdfc84a63`.
- Complete dependency-free snapshot retained under `FF17-extracted/`; no Lake
  command was run there.
- Integrated only `FiniteFiber/FullPauliStabilizerDensity.lean`.  Its live and
  quarantined SHA-256 values agree:
  `688162cc2779855e163f45fd210e4ddd36339579136fd3039f19df82cfca0a09`.
- Rejected: the remote README attribution block, `ARISTOTLE_SUMMARY.md`,
  source-context/autonomy metadata, and the remote `manuscript/` copy.  No
  manuscript or root import file was modified.

## Proved

For `D : FullPauliRegionStabilizer Site`, the exact hypotheses are the fields
at `FiniteFiber/FullPauliStabilizerDensity.lean:303`: a subgroup of
`FullPauliWord Site`, a finite `region`, an explicit `Fintype` on the subgroup,
support containment for every group member, elementwise involutivity
`g * g = 1`, and exclusion of `FullPauliWord.negativeIdentity`.

- `FullPauliRegionStabilizer.stabilizerData` constructs
  `FinitePauliStabilizerData D.group D.region.card`; the representation
  injectivity and matrix `-1` exclusion are established internally, rather
  than inserted as fields.
- The packet's target identity is exactly
  `FullPauliRegionStabilizer.regionToQubitMatrix_regionDensity`
  (`FullPauliStabilizerDensity.lean:477`): after the explicit basis
  reindexing, the finite-region average
  `((2 : C)^D.region.card)^(-1) * sum_g fullPauliRegionMatrix D.region g`
  is `D.stabilizerData.stabilizerDensity`.
- The exact normal-form convention is preserved by
  `fullPauliRegionMatrix_eq_pauliSign_smul`: the central `ZMod 4` phase plus
  the checked Hermitian correction produces the signed Pauli term used by the
  finite-density layer.
- Derived finite-volume conclusions are checked: projector invariance,
  self-adjoint idempotence, trace formula, trace-one density,
  trace-normalized-projector identity, positive semidefiniteness, and nonzero
  projector (`:490`--`:539`).
- `ofGlobalStabilizer` retains the added premises explicitly:
  `hinv : forall g in S, g * g = 1` and `negativeIdentity notin S` (`:677`--`:688`).
  `ofGenerators` discharges these only from the existing explicit
  pairwise-commuting, order-two, consistent generator data; it does not infer
  them from short-range order.

## Partial

This accepts only the manuscript's finite-region density formula
`rho_F = 2^(-|F|) sum_{g in G_{S,F}} g` and its finite matrix consequences.
The module does not prove region-to-region partial-trace compatibility, a
quasilocal completion, a global state, GNS data, normality, or a finite-fiber/
type conclusion.  Those remain open and are not needed for FF17.

## Blocked

None within the stated FF17 target.

## Failed

None.  No target was silently weakened: the finite group, its support,
involutivity, and consistency are all visible assumptions of the proved
finite-volume theorem.

## Adversarial review

No confirmed defect found.  The main potential scope failure—treating a
finite syntactic local group as a completed quasilocal construction—is avoided:
the only global-group constructor remains conditional and the source explicitly
disclaims every global-state/GNS claim.  The matrix identity is transported by
an explicit basis algebra equivalence, not asserted by notation.

## Live verification

All commands below were run in `formalization_finite_fibers`, never in the
quarantine snapshot:

```text
lake build FiniteFiber.FullPauliStabilizerDensity                PASS
lake build FiniteFiber.FinitePauliStabilizer                     PASS
lake build FiniteFiber.FiniteRegionFullPauliMultiplication      PASS
lake build FiniteFiber.FullPauliSupportLocality                  PASS
lake build FiniteFiber                                           PASS
lake build                                                       PASS
lake env lean tests/AxiomAudit.lean                              PASS
```

A direct generated `#print axioms` audit covered all 41 public FF17 theorems.
Each reports only `propext`, `Classical.choice`, and `Quot.sound`.  A direct
scan found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
`implemented_by` token in the new module.
