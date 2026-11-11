# P57C — pure GNS type-I factor

## Context declaration

- **Source basis:** `main.tex:1945-1963`.

## Plan alignment

- **Package and lane:** `P57C`; Lane `H`.
- **Predecessors:** P59A and P57B, integrated and locally audited.
- **Gate discharged:** identify the constructed pure coordinate GNS
  representation with the vacuum ITP and prove its represented closure is the
  full type-I operator factor.
- **Forbidden downstream claims:** no mixed-UHF identification, no regional
  factor transport, and no trace/weight conclusion.

## Mathematical target

Create only `AristotleCandidates/PureGNSFactor.lean`. Instantiate P59A's pure
coordinate state and P57B's completed vacuum ITP. Construct the canonical GNS
unitary, prove the finite-word action agrees with finite excitations, and prove
the bicommutant of the pure represented coordinate algebra is the full bounded
operator algebra on the completed pure space. Derive trivial centre from that
equality.

No `pure_factor`, `pure_commutant`, GNS-unitary, or `B(K)`-closure premise may
be introduced. If pinned Mathlib lacks an essential theorem, prove it locally
or report the exact gap without accepting the package.

## Auxiliary assumptions

Only the integrated P59A coordinate assumptions and P57B vacuum construction.
State finite/infinite coordinate branches explicitly.

## Files and imports

Create only `AristotleCandidates/PureGNSFactor.lean`; import P59A, P57B, and
the existing bicommutant infrastructure.

## Acceptance criteria

`lake build AristotleCandidates.PureGNSFactor` succeeds without `sorry`,
axiom, supplied pure-factor premise, mixed claim, or trace/weight conclusion.
