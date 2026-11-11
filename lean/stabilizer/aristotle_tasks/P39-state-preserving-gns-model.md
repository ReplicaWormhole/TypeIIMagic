# P39 — state-preserving C-star alpha and GNS transport

## Context declaration

- **Source basis:** `main.tex:1921-1958`

## Mathematical target

Create only `AristotleCandidates/StatePreservingGNSModel.lean`. Package the
concrete completion of P38, a supplied regional completion, and a supplied
state-preserving extension of the finite-coordinate algebraic alpha. Prove the
continuous state pullback, equality from dense finite-stage formulas, and the
canonical GNS unitary/intertwining consequences using the existing GNS bridge.

## Boundary

Do not construct the manuscript's finite adapted-coordinate data or assert a
normal/spatial von Neumann equivalence. All completion, alpha, and state data
not built in this file must be explicit assumptions. No placeholders or axioms.

## Acceptance criteria

`lake build AristotleCandidates.StatePreservingGNSModel` succeeds and reports
the exact unfinished geometric input.
