# P59B closeout review — mixed GNS/UHF bridge

## Decision

**Status: failed; Lane H must halt.**

Aristotle task `bb6c00a3-3adb-4e9c-80b2-47f7787be42c` is terminal
`OUT_OF_BUDGET` in
`history/logs/20260810T232201Z-60d29fa6-tasks.log`.
Only its exact archive
`aristotle_responses/P59B-mixed-gns-uhf-bridge-60d29fa6-bb6c00a3.tar.gz`
(SHA-256 `46c3f7cec5689d9f6d592b5db16fa4bfa38cb8c09a588aa73b80b42de0fe645e`)
was extracted to the dedicated quarantine directory.  No build, Lake update,
or dependency fetch ran in that dependency-free snapshot.

The only packet-authorized candidate is
`AristotleCandidates/MixedGNSUHFBridge.lean` (quarantined SHA-256
`e9992333fbfea8cda71a0e6c2adbeec0e26e941b10bdbb2fdf1a95039e01414d`).
It was **not integrated**: it has eight `sorry` placeholders, and the two
load-bearing declarations checked below depend on `sorryAx`.  No raw response
record was copied into the working tree.  The quarantined P59A and P58
predecessors match the already integrated live modules byte-for-byte:

```text
ConcretePureMixedProductData.lean  8e646687234146d34a1e27c63eb8c65ddbe9cfc59a025135291e9e932a34b8b6
MixedUHFHyperfiniteFactor.lean     5dbf9ff8c35035c94b37804435793102cb0c59f88c7a39e2746c32274fc67d20
```

## Exact declarations and assumptions

The proposed route adds `MixedRegister`/`MixedEnumeration`, explicit mixed
coordinate indices, their visibility at exhaustion stages, and the local
proposition `Exhaustive`.  It constructs stage maps and a UHF homomorphism,
then attempts the P58-to-P59A GNS transport using P58's existing
`MixedWeakClosurePremises`.

The unproved chain is:

- `MixedEnumeration.inner_preMap` (line 1069) and `norm_preMap` (1073),
  asserting equality of the UHF trace and P59A mixed-marginal inner products;
- `norm_gnsCLM` (1091), `denseRange_gnsCLM` (1094), and
  `surjective_gnsCLM` (1097), needed to construct the claimed unitary;
- `gnsUnitary_intertwine` (1113) and `conj_uhfRep` (1119); and
- `mapVN_mixedVonNeumann` (1128), needed for the final conditional theorem
  `mixedRepVonNeumann_isHyperfiniteFiniteFactor`.

Thus the candidate neither proves the specified unitary/star-equivalence nor
transports P58's finite/infinite mixed weak-closure conclusion.  The stated
mathematical target is not met.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | Some finite-register Pauli-word calculations, stage maps, and algebraic UHF-to-mixed maps elaborate. |
| partial | The candidate makes the coordinate enumeration explicit and supplies preliminary maps, but the GNS inner-product identity, density, surjectivity, intertwining, and von Neumann transport remain unproved. |
| blocked | The P59B gate is blocked by the eight placeholders listed above; the final theorem necessarily inherits them. |
| failed | Acceptance fails: packet criterion forbids `sorry`, and no reviewed candidate can be integrated. |

## Plan alignment

- **Package and lane:** `P59B`, Lane `H` — correctly declared.
- **Predecessors:** only P59A and P58 are imported; both are locally
  integrated, audited, and byte-identical to the quarantined copies.
- **Permitted gate:** not discharged.  The missing GNS isometry/density and
  weak-closure-transport proofs are exactly the bridge required by P59B.
- **Forbidden downstream claims:** the source text does not assert a pure
  type-I factor, regional product transport, or trace/weight dichotomy.  It
  does not add a fresh mixed-factor or normality *field*; however, this scope
  compliance cannot compensate for the unresolved core proofs.

## Verification

- `lake env lean <quarantined MixedGNSUHFBridge.lean>` run from the live
  project — elaborates, but emits eight `declaration uses sorry` warnings at
  lines 1069, 1073, 1091, 1094, 1097, 1113, 1119, and 1128.  It is not an
  acceptance result.
- Source-plus-`#print axioms` checks in the live Lake environment — both
  `MixedEnumeration.inner_preMap` and
  `MixedEnumeration.mixedRepVonNeumann_isHyperfiniteFiniteFactor` report
  `sorryAx` (in addition to `propext`, `Classical.choice`, and `Quot.sound`).
- `lake build AristotleCandidates.ConcretePureMixedProductData AristotleCandidates.MixedUHFHyperfiniteFactor Formalization`
  — passed (`8102` jobs) in the live project.
- `lake build` — passed (`0` jobs) in the live project.  This does not build
  the rejected, unintegrated P59B candidate.
- Candidate declaration scan — eight `sorry` occurrences; no `admit`, user
  `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration.

## Adversarial review

**Acceptance-blocking finding:** the advertised unitary and the exact
weak-closure equality depend on unproved `sorry` declarations.  Therefore a
successful elaboration of the quarantined file is only a placeholder-tolerant
Lean check, not mathematical validation.  No manuscript theorem, factor
theorem, or trace/weight conclusion has been promoted.

## Cleanup and worktree state

Kept: the exact archive and its dedicated quarantine extraction as raw task
records, plus this halt review.  Not kept in the live source tree: the rejected
candidate module and any derived `.olean`.  All pre-existing dirty plan,
packet, candidate, and review work remains preserved.  No manuscript file was
changed; no commit, push, update, fetch, or archive build occurred.
