# P59B — mixed GNS/UHF bridge

## Context declaration

- **Source basis:** `main.tex:1945-1967`.

## Plan alignment

- **Package and lane:** `P59B`; Lane `H`.
- **Predecessors:** P59A and P58, integrated and locally audited.
- **Gate discharged:** identify the concrete mixed GNS component of P59A with
  P58's dyadic-UHF weak-closure model and transport its factor/tracial
  structure.
- **Forbidden downstream claims:** no pure type-I factor, no regional product
  transport, no trace/weight dichotomy, and no fresh mixed-factor premise.

## Mathematical target

Create only `AristotleCandidates/MixedGNSUHFBridge.lean`. Build a unitary or
star-equivalence from the actual mixed coordinate algebra/GNS representation
inside P59A to P58's UHF representation. Use it to transport P58's finite and
infinite mixed alternatives and named weak-closure conclusions to P59A's
mixed representation. Prove the exact statement needed later, not merely that
both models are UHF.

## Auxiliary assumptions

Use only P58's explicit `MixedWeakClosurePremises` where P58 itself uses them,
and make the coordinate-index identification explicit. Do not add a new mixed
factor, mixed trace, equivalence, or normality field.

## Files and imports

Create only `AristotleCandidates/MixedGNSUHFBridge.lean`; import P59A and P58.

## Acceptance criteria

`lake build AristotleCandidates.MixedGNSUHFBridge` succeeds, the bridge uses
actual P58 declarations, and no `sorry`, axiom, or supplied mixed-factor
premise is introduced.
