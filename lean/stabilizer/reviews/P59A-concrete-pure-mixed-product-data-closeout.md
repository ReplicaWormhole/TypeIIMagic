# P59A closeout review — concrete pure/mixed product datum

## Decision

**Status: proved at the packet's stated conditional Lane-H scope; queue may advance.**

Aristotle task `f17ae380-7cbe-4e16-8ea3-94d98cb8ef47` is terminal `COMPLETE` in `history/logs/20260810T213056Z-a130d169-tasks.log`. Only its exact archive `aristotle_responses/P59A-concrete-pure-mixed-product-data-a130d169-f17ae380.tar.gz` (SHA-256 `54d09cdca8580fdc5a2d1d37f4db6f4d805e6f46e93acc4fa9db58e33d9ce75b`) was extracted into its named quarantine directory. No build, dependency update, or fetch was run there. The only integrated source is the packet-authorized `AristotleCandidates/ConcretePureMixedProductData.lean`. Its live and quarantine SHA-256 values agree:

```text
8e646687234146d34a1e27c63eb8c65ddbe9cfc59a025135291e9a932a34b8b6
```

The quarantined copies of `RegionalConcreteCStarAlpha.lean`, `RegionalProductStateIdentity.lean`, and `ProductGNSTensorFactorization.lean` are byte-identical to their live, locally audited counterparts. P57 is used only for its already integrated `ProductGNSData` structure.

## Exact declarations and assumptions

For `A : AlphaData L I` and `R : A.SourceConcreteRep`, P59A constructs:

- `pureCStar`, `mixedCStar`, `pureEmbedding`, and `mixedEmbedding` as the closed selected-coordinate and complementary-coordinate C-star subalgebras of `R.sourceCStar` and their inclusion star homomorphisms;
- `pureCStar_mixedCStar_commute` and `pureEmbedding_mixedEmbedding_commute`, derived by closing the verified cross-coordinate Pauli-word commutation relation;
- `productSpan` and `dense_productSpan`, using the exact split of every finite-stage word and the P55D dense source embedding;
- `totalStateCLM_mul`, which factors the recovered P56R source state on all pure/mixed elementary products; and
- the square-positivity conversion `positiveOfStarSq`, positive marginals, `SourceConcreteRep.concreteProductGNSData`, and the branch-uniform `AlphaData.concreteProductGNSData`, with identification lemmas for the total algebra and total state.

There is no new premise argument. The result inherits only the explicit coordinate-model data already carried by `AlphaData` and `SourceConcreteRep`: the accepted P52/P53/P55D coordinate and concrete-model data, including the named `symplectic` and `stage_surjective` fields. The total state is exactly P56R's `cstarProductStateRecovered`; `ProductStateBound` is not an argument of any P59A declaration. The C-star order used to build Mathlib `PositiveLinearMap`s is explicitly `CStarAlgebra.spectralOrder`.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | The selected/complementary concrete C-star subalgebras, commuting inclusions, norm-dense span of their elementary products, positive unital marginal functionals, product identity, contractivity, and concrete `ProductGNSData` are constructed from P55D/P56R data. |
| partial | The result is conditional infrastructure relative to the manuscript: it does not construct the underlying local-hyperbolic coordinate/model hypotheses from `main.tex:1925-1967`. |
| blocked | Completed ITP/GNS factor identification, pure and mixed factor classification, regional factor transport, and trace/weight conclusions remain separate downstream gates. |
| failed | None. |

Thus P59A's mathematical target is met at its stated scope. This is not a proof of a completed infinite tensor product, a factor theorem, or a trace/weight theorem.

## Plan alignment

- **Package and lane:** `P59A`, Lane `H`, as declared in both the packet and `PLAN.md`.
- **Predecessors:** P55D and P56R are integrated, live audited in their respective closeouts, and match the quarantined copies. The integrated P57 supplies only the generic target structure permitted by the packet; it is not used to obtain a factor or trace conclusion.
- **Permitted gate:** discharged exactly: P59A instantiates P57's generic product datum from the P55D/P56R concrete coordinate model rather than adding arbitrary `ProductGNSData`, density, product-state, positivity, or norm-bound fields.
- **Forbidden downstream claims:** respected. The candidate contains no completed ITP, pure/mixed factor classification, regional factor, normality, trace, or weight theorem.

## Verification

- `lake build AristotleCandidates.ConcretePureMixedProductData` — completed, but Lake has no registered target for this untracked candidate and produced no candidate `.olean`; it is not acceptance evidence by itself.
- `lake env lean AristotleCandidates/ConcretePureMixedProductData.lean` — passed in the live project; this is the narrow source-level Lean check.
- Direct live elaboration of P59A together with `#print axioms` for `pureCStar_mixedCStar_commute`, `dense_productSpan`, `totalStateCLM_mul`, `positiveOfStarSq`, both exported datum declarations, and the non-vacuity theorem — passed. Each reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Direct live Lean checks of the P55D, P56R, and P57 support modules — passed.
- `lake build` — passed (existing registered project targets up to date).
- Declaration-head scan of P59A — no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration. `git diff --check` passed.

## Adversarial review

No acceptance-blocking issue found. The load-bearing checks were that each finite source word is split into pure and mixed filters at the same stage, the two pairing orientations vanish before commutation is concluded, dense span follows from the actual P55D dense source embedding, and state factorization is extended from words only through closed linear submodules. The positivity conversion explicitly uses the pinned spectral C-star order; it does not replace positivity by an axiom. Compilation and axiom reports validate the Lean artifact, not the inherited coordinate hypotheses or later operator-algebraic claims.

## Cleanup and worktree state

Kept intentionally: the integrated P59A candidate, its exact archive, quarantine extraction, and this review. All pre-existing modified and untracked plan, packet, candidate, and review files were preserved. No manuscript file was changed; no commit, push, archive build, dependency update, or dependency fetch occurred.

