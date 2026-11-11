# P43 — construct coherent local hyperbolic coordinate data

## Mathematical target

Create only `AristotleCandidates/CoherentLocalHyperbolicCoordinates.lean`.
Read the canonical `manuscript/main.tex`, especially the local hyperbolic-basis
section, and all checked P17--P42 infrastructure.

Formalize the exact upgrade from a locally supported adapted hyperbolic basis
to the *coherent finite-stage data* required by the existing algebraic limit
theorems: finite coordinate blocks along a lattice exhaustion, source and
target Pauli-word bases, inclusion coherence, and phase calibration satisfying
the multiplier and involution equations.

Prove all purely algebraic consequences of a supplied locally finite coherent
coordinate structure.  Crucially, do not treat “every basis vector has finite
support” as automatically implying uniform local finiteness, finite-stage
exhaustion, or phase coherence.  If an implication requires an extra condition,
make it an explicit field and record the exact source gap.

## Boundary

No C-star completion, GNS spatial transport, factor classification, or final
regional theorem.  No placeholders or axioms.  Build the file and report
whether the manuscript hypothesis alone yielded the coherence data.
