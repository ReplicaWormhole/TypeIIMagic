# P57 closeout review — product GNS tensor factorization

## Decision

**Status: proved at the packet's stated conditional Lane-H scope; queue may
advance.**

Relative to the complete manuscript theorem, this is intentionally **partial**:
the module does not prove the pure or mixed factor classifications, factorhood,
normal/spatial tensor-product theory beyond its concrete bicommutant definition,
or the final trace/weight conclusions.

The exact supervisor-supplied archive
`aristotle_responses/P57-product-gns-tensor-factorization-a7accfb8-36471af9.tar.gz`
has SHA-256
`27aa2166368ee5ded0dc2f5ea2573811bb4b6be623c54f53da69b71a14ecdeed`.  It was
extracted only into
`aristotle_responses/P57-product-gns-tensor-factorization-a7accfb8-36471af9-quarantine/`.
No build, dependency update, or dependency fetch was run in that quarantine
snapshot.  Only the packet-authorized candidate
`AristotleCandidates/ProductGNSTensorFactorization.lean` was integrated into
the live project.  Its live SHA-256 matches the quarantined candidate exactly:

```text
6e4549050881ec26557bbf243095ae549de03ce6a8628ad4bf4724e2d3478b07
```

The archive, quarantine extraction, and this review are retained as raw
response records.  No manuscript file was changed.

## Source and exact scope

The packet's manuscript source basis is `main.tex:1945-1985`.  Lines
`1945-1953` state the product-state GNS splitting target
`\mathcal H_{\widetilde\omega}=\mathcal K\otimes\mathcal K'`; lines
`1954-1967` contain the later factor/type classification, which is outside P57;
and lines `1968-1981` describe the separate identification with the regional
GNS representation and its quasi-equivalence problem.  The candidate therefore
formalizes the P57 GNS/spatial-identification gate only, not the later
classification or source-specific quasi-equivalence theorem.

## Exact assumptions and declarations

The central declaration is
`AristotleCandidates.ProductGNSTensor.ProductGNSData`.  Its explicit fields
are:

- C-star structures and order structures for `Pure`, `Mixed`, and `Total`;
- unital star-algebra embeddings `pureEmb : Pure →⋆ₐ[ℂ] Total` and
  `mixedEmb : Mixed →⋆ₐ[ℂ] Total`;
- positive linear functionals `pureState`, `mixedState`, and `totalState`;
- elementwise commutation of the two embeddings;
- the product identity
  `totalState (pureEmb a * mixedEmb b) = pureState a * mixedState b`;
- the contractivity premise `state_norm_le`; and
- norm-density of the complex linear span of elementary products,
  `span_dense`.

The GNS construction uses positive functionals, so normalized-state fields are
not needed for these declarations.  Reading the data specifically as states
requires the usual supplied normalization; no normalization is silently used
to prove a later trace or factor statement.  The algebraic tensor product and
its completion are constructed in the module.  No completed infinite tensor
product, spatial von Neumann tensor-product API, normal extension, or closure
premise is supplied as an axiom or interface.

The load-bearing declarations are:

- `prodElt`, `prodElt_mul`, `prodElt_star_mul`, and
  `preInner_prodElt`, giving the elementary product algebra and its GNS inner
  product factorization;
- `prodCLM`, `inner_prodCLM`, `TensorPre`, `TensorGNS`,
  `tensorLiftₗ`, `inner_tensorLiftₗ`, and `norm_tensorLiftₗ`, constructing the
  algebraic tensor map and its isometry;
- `tensorUnitaryCLM`, `denseRange_tensorUnitaryCLM`,
  `surjective_tensorUnitaryCLM`, and
  `productGNSUnitary`, constructing the canonical GNS unitary;
- `prodCLM_intertwine` and `tensorUnitaryCLM_tensorOpC`, proving the dense
  finite-word intertwining and its continuous extension;
- `unitaryConj_tensorOpC`, transporting elementary tensor operators to the
  total GNS representation;
- `commute_totalRep_of_commute_prodElt` and
  `centralizer_representedProductSet`, proving that elementary products and
  the full represented total algebra have the same commutant;
- `unitaryConj_image_bicommutant_elementaryTensorSet`, transporting the
  generated bicommutant through the GNS unitary;
- `pureFactorSet`, `mixedFactorSet`, `spatialTensorAlgebra`,
  `tensorOpC_split`, `tensorOpC_commute`, and
  `bicommutant_elementary_eq_spatial`; and
- `unitaryConj_image_spatialTensorAlgebra`, the final concrete equality with
  `(Set.range totalRep).centralizer.centralizer`.

`spatialTensorAlgebra` is explicitly defined as the bicommutant of the two
commuting represented factor families.  This is a project-local concrete set
definition, not an imported standard spatial von Neumann tensor-product
construction.  The candidate documents that pinned Mathlib still lacks the
standard tensor-product algebra, commutation, slice-map, and normal-product
extension API.  The included `trivialProductGNSData` witness only proves that
the data structure is non-vacuous; it is not a classification or regional
application theorem.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | The conditional product-data theorem constructs the GNS tensor-product unitary, proves the finite-word and continuous intertwining identities, and identifies the represented total bicommutant with the concrete bicommutant-defined spatial algebra. |
| partial | The result remains generic over `ProductGNSData`; it does not itself instantiate that bundle from the manuscript's regional algebra and P55D/P56R data. Standard spatial von Neumann tensor-product theory and all later factor/type/trace conclusions remain open. |
| blocked | Nothing blocks the packet's permitted strongest-local-form gate. The stronger standard spatial-von-Neumann API is unavailable in pinned Mathlib and is explicitly recorded rather than assumed. |
| failed | None. No compilation, placeholder, archive-integrity, or scope failure was found. |

The packet's mathematical target is therefore met at its stated conditional
scope.  It is not a proof of the complete manuscript claim
`\pi_{\widetilde\omega}(\mathcal P_I)''=\mathcal B(\mathcal K)\bar\otimes\mathcal R`:
the classification of the two factors and the source-specific regional
identification are downstream work.

## Changed proof route

The candidate takes a constructive route through the algebraic tensor product
`PureGNS ⊗[ℂ] MixedGNS`, then completes the norm-preserving tensor lift.  It
derives boundedness of elementary tensor operators from the proved
intertwining identity and the isometry, rather than assuming a general
operator-tensor norm inequality unavailable in the pinned API.  It defines the
strongest available concrete spatial object as a bicommutant of the two
commuting factor families.  These are alternative proof choices within the
packet's scope, not silent weakenings; every added premise is a named field of
`ProductGNSData` above.

## Plan alignment

- **Package and lane:** `P57`; Lane `H`, correct.
- **Integrated predecessors:** `P54`, `P56R`, and `P57A`, each locally
  integrated, compiled, and accepted in its closeout review.  The preserved
  partial `P56` artifact is not used as a predecessor.  The additional GNS and
  bicommutant imports are already-built local infrastructure.
- **Permitted gate:** construct the pure/mixed product GNS Hilbert-space split,
  prove the dense/continuous intertwining identity, and identify the generated
  represented algebra with the strongest concrete spatial tensor object
  supported by pinned Mathlib.  This gate is discharged conditionally on the
  explicitly declared `ProductGNSData` fields.
- **Forbidden downstream claims:** respected.  The candidate does not claim
  mixed-factor classification, factorhood of either factor, regional
  factorhood, `\mathcal B(\mathcal K)` identification, hyperfiniteness, or any
  trace/weight dichotomy.

## Verification

- `lake build AristotleCandidates.ProductGNSTensorFactorization` — passed
  (`8072/8072` jobs).
- `lake build AristotleCandidates.UHFReferenceRepresentation AristotleCandidates.RegionalProductStateIdentity AristotleCandidates.VacuumRestrictedInfiniteTensorProduct AristotleCandidates.GNSCommutantConjugation AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.VonNeumannBicommutantTheorem AristotleCandidates.ProductGNSTensorFactorization Formalization` — passed (`8100` jobs).
- `lake build` — passed (`0` jobs; live project already up to date).
- `#print axioms` for `productGNSUnitary`, `prodCLM_intertwine`,
  `unitaryConj_image_bicommutant_elementaryTensorSet`,
  `bicommutant_elementary_eq_spatial`, and
  `unitaryConj_image_spatialTensorAlgebra` — each reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- A declaration-level scan of the candidate and direct imports found no
  `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, `implemented_by`, or
  `native_decide` declarations.  Textual mentions in explanatory comments
  were not treated as declarations.
- `git diff --check` and live/quarantine SHA-256 comparison — passed.

## Adversarial review

Artifact types touched: Lean code, mathematical formalization, and workflow
closeout metadata.  No acceptance-blocking finding was found.  The review
checked that the candidate is the packet-authorized file, that its explicit
fields account for density and product-state assumptions, that completion and
spatial objects are constructed at the available scope, that no downstream
factor/trace claim is smuggled in, and that no unrelated dirty work was
overwritten.  Compilation and axiom checks validate the Lean declarations only;
they do not validate the manuscript's missing regional coordinate construction,
normal/quasi-equivalence argument, or factor classification.

## Cleanup and worktree state

The pre-existing modified plan, packet, decision, and queue files, together
with all earlier candidates and reviews, were preserved.  The new integrated
candidate, exact archive, quarantine extraction, and this closeout review are
kept intentionally.  The live `.lake/build` cache produced/used by the Lean
checks is also retained under the existing project build tree.  No commit,
push, dependency update, manuscript edit, or archive build was performed.
