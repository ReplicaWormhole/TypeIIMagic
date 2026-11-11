# P59 — local-hyperbolic factor and trace theorem

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1970-2004`.

## Plan alignment

- **Package and lane:** `P59`; Lane `H`.
- **Predecessors:** `P57`, `P58`, both integrated and locally audited before submission.
- **Gate discharged:** transport the spatial product model to the regional
  algebra, prove trivial center, and prove the finite/infinite pure trace dichotomy.
- **Forbidden downstream claims:** no general-lattice central decomposition, no
  assertion that Lane H proves Lane G, and no global tracial **state** in the
  infinite-pure case.

## Mathematical target

Create only `AristotleCandidates/LocalHyperbolicFactorTraceTheorem.lean`. Prove
the regional represented von Neumann algebra is spatially star-isomorphic to
`B(K_pure) barTensor R_mixed` using the integrated P57--P58 declarations. Prove
both factors and their spatial tensor product have trivial center, then transport
factorhood. In the finite-pure case construct the normalized tracial state. In
the infinite-pure case construct or explicitly assume and transport a faithful
normal semifinite trace/weight; never call it a state.

## Auxiliary assumptions

List every spatial tensor-product, factor-center, normal transport, canonical
operator trace, and semifinite-weight premise not constructed by predecessors.

## Files and imports

Create only `AristotleCandidates/LocalHyperbolicFactorTraceTheorem.lean`; import
P57 and P58.

## Acceptance criteria

`lake build AristotleCandidates.LocalHyperbolicFactorTraceTheorem` succeeds
without forbidden declarations. Report separately the spatial isomorphism,
factor conclusion, finite tracial state, and infinite semifinite weight.
