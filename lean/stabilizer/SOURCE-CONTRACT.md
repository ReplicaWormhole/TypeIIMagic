# Manuscript source contract

## Authoritative source

- Manuscript: `sources/manuscript/main.tex`
- Title in source: *Infinite Magic and the Continuum* (`main.tex:117`)
- Formalization policy: `AGENTS.md`

This project does not treat its own Lean files, prior agent prompts, or the
surrounding repository as mathematical source authority.

## Source clauses in scope

| Source locator | What the manuscript says | Formalization status |
| --- | --- | --- |
| `main.tex:1671-1679` | Defines short-range order through a local symplectic basis, with `W_Gamma = span{z_i : i in P}` and finite support. | Requires a precise Lean model of the infinite Pauli/symplectic data. |
| `main.tex:1740-1752` | States the short-range regional-algebra theorem, with an asserted factorization `A_Gamma` into a pure-sector type-I factor and a core factor that is finite type I or hyperfinite `II_1`. | Target statement; not established by current Lean artifacts. |
| `main.tex:1915-1920` | Proposes an adapted symplectic basis and a star-isomorphism from an infinite Pauli algebra to `A_Gamma`. | External assumption/gap until the source construction is formalized. |
| `main.tex:1927-1931` | Writes a pure/mixed product density state. | Finite density-matrix fragments are formalized; the infinite model is not. |
| `main.tex:1945-1967` | Proposes the GNS/tensor-factor and type conclusions. | Conditional GNS transport is formalized; analytic product and type conclusions are not. |
| `main.tex:1970-2004` | Proposes quasi-equivalence and normal-folium transport. | Not formalized. |

The wording above is a locator-oriented paraphrase, not a replacement for the
manuscript.

## Permitted auxiliary assumptions

Any manuscript-facing Lean theorem that needs one of the following must expose
it in the theorem statement or task packet:

1. a completed C-star or von Neumann algebra model for the infinite Pauli
   system and its regional algebra;
2. the asserted star-isomorphism from that model to the regional algebra;
3. the product-state formula and hypotheses making the GNS representation a
   spatial tensor product;
4. the von Neumann closure, normality, and quasi-equivalence assumptions needed
   to transport the claimed factor type; and
5. any hyperfiniteness or trace theorem used for the core factor.

None of these assumptions is supplied merely by the phrase “short-range
order” in the current manuscript source.

## Trace correction

The manuscript-facing target must distinguish two cases:

- if the pure-sector Hilbert space is finite-dimensional, a normalized tracial
  state can be obtained from the finite matrix trace together with the core
  trace;
- if the pure-sector Hilbert space is infinite-dimensional, the appropriate
  conclusion is a faithful normal semifinite trace/weight on the `II_infinity`
  target, not a tracial state.

This is a correction to the intended theorem contract, not a claim that the
current manuscript already states or proves the corrected dichotomy.

## Legacy firewall

Earlier gLU/refinement/layer-coherence material is listed in
`CONTEXT-LEDGER.md`. It is retained, but it is neither a source clause nor an
implicit assumption of this formalization.
