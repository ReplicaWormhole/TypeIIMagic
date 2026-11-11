# P52 — coherent local-hyperbolic coordinates

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1898-1939`.

## Plan alignment

- **Package and lane:** `P52`; Lane `H`.
- **Predecessors:** none.
- **Gate discharged:** construct finite coordinate blocks and their coherent
  exhaustion from explicitly stated local-hyperbolic data.
- **Forbidden downstream claims:** no global algebraic alpha, C-star extension,
  product-state identity, GNS tensor split, factorhood, or trace/weight theorem.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/CoherentLocalHyperbolicCoordinates.lean`.
Formalize the finite coordinate blocks associated with a locally supported
adapted hyperbolic family along a lattice exhaustion. Construct source and
target finite Pauli labels, inclusion coherence, and the data needed for later
phase calibration. Audit whether finite support alone yields locally finite
blocks; if not, make the exact local-finiteness/coherence condition a named
auxiliary field. Reuse checked coordinate and basis-coherence infrastructure.

## Auxiliary assumptions

Every local-finiteness, exhaustion, basis, support, and coherence premise not
literally obtained from the cited manuscript clause must be explicit. The
result is conditional when this list is nonempty.

## Files and imports

Create only `AristotleCandidates/CoherentLocalHyperbolicCoordinates.lean`.
Prefer `Formalization.SymplecticCoordinates`,
`Formalization.CoherentBasisEquiv`, and the existing finite-coordinate modules.
Do not import P53 or any later packet.

## Acceptance criteria

- `lake build AristotleCandidates.CoherentLocalHyperbolicCoordinates` succeeds.
- The response states whether finite support sufficed and names every extra
  local-finiteness or coherence field.
- No placeholders, axioms, or forbidden downstream conclusions occur.
