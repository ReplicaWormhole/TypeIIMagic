# Autonomous proof-development policy

The manuscript theorem is the objective; its displayed proof is evidence and a
starting point, not a restriction on the proof method. Aristotle may introduce
the smallest necessary project-local C-star, von Neumann, GNS, tensor-product,
or Pauli/stabilizer theory in the packet's owned Lean module when Mathlib lacks
it or the paper only gives it implicitly.

It may replace a difficult proof route with an easier valid route. It must not
introduce axioms, `sorry`, `admit`, `opaque`, `unsafe`, or `implemented_by`, and
it must not silently weaken the target. If an additional hypothesis is truly
needed, state it as an explicit Lean field or theorem premise, explain why it
is needed, and prove the strongest recognizable form of the manuscript theorem
available from that premise.

Every result must distinguish:

1. checked infrastructure developed in the packet;
2. a theorem recovered in the manuscript's intended form;
3. a conditional theorem with its exact extra assumptions; and
4. any genuine source or Mathlib obstruction still open.

The canonical paper context is `manuscript/main.tex`. Its proof sketches may
be audited, repaired, or replaced, but its user-level theorem target must not
be silently abandoned.

The active execution contract is `PLAN.md`, with its approved interpretation
in `work/TWO-LANE-FORMALIZATION-DECISION.md`. Every packet must obey its `Plan
alignment` section. A remote result may use only predecessors already integrated
and locally audited; it may neither assume a later package nor claim a later
gate. Lane G and Lane H remain logically independent until an explicit
reconnection package is reached.
