# P59R — regional factor transport

## Context declaration

- **Source basis:** `main.tex:1945-1967, 1970-2004`.

## Plan alignment

- **Package and lane:** `P59R`; Lane `H`.
- **Predecessors:** P57, P57C, and P59B, integrated and locally audited.
- **Gate discharged:** prove the regional represented algebra is the concrete
  spatial product of the proved pure and mixed factors, hence has trivial
  centre.
- **Forbidden downstream claims:** no finite-pure tracial state, no
  infinite-pure trace/weight, and no general central-decomposition conclusion.

## Mathematical target

Create only `AristotleCandidates/RegionalFactorTransport.lean`. Instantiate
P57's product-GNS unitary with P59A's concrete datum, substitute P57C's pure
full-operator factor and P59B's mixed factor, and prove the regional
bicommutant is star-isomorphic to the corresponding concrete spatial product.
Derive its trivial centre without a new pure-commutant or mixed-factor premise.

## Auxiliary assumptions

Only the named P58 weak-closure premises transported by P59B and the integrated
local-hyperbolic data. No trace, weight, or normality premise belongs here.

## Files and imports

Create only `AristotleCandidates/RegionalFactorTransport.lean`; import P57,
P57C, and P59B.

## Acceptance criteria

`lake build AristotleCandidates.RegionalFactorTransport` succeeds with no
`sorry`, axiom, or new factor premise. Report spatial identification and
trivial-centre theorem separately.
