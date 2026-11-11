# Stabilizer Type Formalization

This folder contains a source-backed Lean formalization workspace for the
stabilizer-system and von Neumann algebra type-restriction project.

The workflow is deliberately two-track:

1. Write complete textbook-backed natural-language TeX blueprints.
2. Formalize only targets already present in those blueprints, optionally
   through Aristotle packets.

Blueprints are the informal source of truth.  They must exist before Lean work
and must contain the relevant definitions, assumptions, theorem statements, and
informal proofs or proof sketches.  Aristotle packets are extracted from
blueprints; they are not independent sources of mathematical content.

The first technical priority is not type classification.  It is to define the
objects correctly:

- stabilizer systems;
- canonical stabilizer states;
- infinite-system Hilbert spaces via GNS packages/construction;
- concrete represented region algebras as `VonNeumannAlgebra H`;
- type-restriction statements.

## Layout

```text
Formalization/             Lean source
blueprints/                prerequisite informal TeX notes for Lean targets
aristotle/packets/         one-target Aristotle requests
aristotle/responses/       raw Aristotle outputs
aristotle/logs/            command logs and blocked-target notes
agents/                    handoffs and agent notes
reviews/                   formalization reviews
MANIFEST.toml              target index and status ledger
PROGRESS.md                chronological work log
COMMUNICATION.md           Aristotle and agent communication protocol
```

## Current Strategy

The fastest honest path is:

1. Write/complete the blueprint note for algebraic stabilizer data over
   `ZMod 2`, then formalize it.
2. Write/complete the blueprint note for canonical coefficient states, then
   formalize it.
3. Write/complete the blueprint note for the GNS package/interface, then
   formalize it.
4. Write/complete the blueprint note for represented concrete region von
   Neumann algebras, then formalize them.
5. Write/complete the type-restriction blueprint only after the representation
   layer exists, then prove type restrictions.

The GNS layer is required for infinite systems because a concrete
`VonNeumannAlgebra H` needs the Hilbert space `H`.
