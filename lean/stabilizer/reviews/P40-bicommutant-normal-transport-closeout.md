# P40 closeout review — bicommutant and normal transport boundary

## Decision

**Status: proved at the packet's stated conditional scope.**

The reviewed and integrated module is
`AristotleCandidates/BicommutantNormalTransport.lean`. It was downloaded as
`aristotle_responses/P40-bicommutant-normal-transport.tar.gz` and extracted,
without building or fetching dependencies, at
`aristotle_responses/P40-extracted/aristotle-stabilizer_hyperfinite-hpzu5w6c_aristotle/`.
The live module is byte-identical to that quarantined candidate. No remote
file other than this packet-authorized module was integrated; the archive and
extraction remain the raw response record.

## Source and scope

This is a manuscript-facing conditional interface with source basis
`main.tex:1970-2004`. Those lines propose to identify generated von Neumann
algebras, use normal-functionals/folia to establish quasi-equivalence, and
explicitly leave the necessary recovery and norm comparison as a question.
They do not supply a Mathlib double-commutant theorem, a characterization of
normal functionals, or the requisite project-specific completion data.

P40 starts only from P39's supplied `StatePreservingData`: it therefore
retains P39's C-star completions, state-preserving extension, and GNS unitary
as external data. It does not construct the manuscript's spatial tensor
product, factor type, hyperfiniteness, trace, or weight.

## Exact declarations and assumptions

The checked algebraic route is:

- `image_centralizer_centralizer_of_mulEquiv`,
  `image_vonNeumannGenerated`, and `image_commutant` transport set-theoretic
  centralizers and the P36 algebraic bicommutant under a star-algebra
  equivalence of bounded operators.
- For `M : StatePreservingData`, `sourceVN M` and `targetVN M` are the P36
  algebraic generated bicommutants of the two GNS representation ranges.
  `gnsConj_image_sourceVN` and `gnsConj_image_commutant` prove their exact
  conjugation formulas.
- `bicommutantStarEquiv` restricts the GNS-unitary conjugation to the two
  bicommutants, and `bicommutantStarEquiv_sourceRepVN` proves that it sends
  `pi_omega(a)` to `pi_tilde_omega(alphaCStar(a))`. Consequently
  `algebraicallyQuasiEquivalent` proves the explicitly defined algebraic
  intertwining condition.

The checked functional route is:

- `IsVectorSeriesFunctional N phi` is a definition of the series shape in
  `main.tex:1984-1993`: vectors `xi`, `eta` with summable norm series and
  `phi T = sum_n <xi_n, T eta_n>`.
- `isVectorSeriesFunctional_pullback` and
  `isVectorSeriesFunctional_pushforward` prove transport in both directions
  along the unitary-implemented bicommutant equivalence.
- `folium_source_eq_pullback_folium_target` proves equality after restriction
  to the C-star algebras for this explicitly defined vector-series class.

The following are definitions used only as hypotheses, not axioms and not
manuscript-derived facts:

- `DoubleCommutantStatement H`: the algebraic bicommutant has the asserted
  weak-operator-topology closure characterization;
- `NormalFunctionalCharacterization N IsNormal`: a supplied normality
  predicate is exactly `IsVectorSeriesFunctional`.

Accordingly,
`bicommutantStarEquiv_normal_of_characterization` is conditional on the two
normal-functional characterization premises, while
`bicommutant_eq_wotClosure_of_interface` is conditional on the two
double-commutant premises. `bicommutant_normal_transport_package` deliberately
packages only the unconditional algebraic and vector-series results.

## Scope classification

| Classification | Result |
| --- | --- |
| proved | Algebraic bicommutant/commutant conjugation, induced star equivalence implementing the GNS representation transport, algebraic quasi-equivalence, and bidirectional vector-series transport with the resulting restricted-class folium equality. |
| partial | Normality and WOT-closure conclusions are derived only conditionally from the two explicit interfaces. |
| blocked | Pinned Mathlib does not provide the required analytic double-commutant or normal-functional/predual infrastructure; the manuscript-specific completion, extension, and GNS input remains in P39's supplied datum. |
| failed | None. |

The packet's mathematical target is met at its stated scope. In particular,
the module does not silently upgrade the algebraic bicommutant to an analytic
closure and does not call its vector-series class the actual normal folium
without the explicit characterization premise.

## Adversarial review

No acceptance-blocking defect was found. The review checked that:

- the source locator is accurate and the manuscript itself records an
  unresolved recovery/norm question;
- P36's `vonNeumannGenerated` is used only as a set-centralizer bicommutant,
  never as an unproved WOT/SOT closure;
- the normality theorem exposes both characterization hypotheses and the WOT
  theorem exposes both double-commutant hypotheses;
- the alleged folium equality is precisely limited to the locally defined
  vector-series class; and
- no spatial tensor product, classification, trace, or type claim is added.

No `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or
`native_decide` declaration occurs in the integrated candidate. The principal
theorems audited with `#print axioms` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Verification

- `lake build AristotleCandidates.BicommutantNormalTransport` — passed in the
  already-built live project.
- `lake build AristotleCandidates.BicommutantVonNeumannCore AristotleCandidates.StatePreservingGNSModel AristotleCandidates.BicommutantNormalTransport Formalization` — passed.
- `lake build` — passed (`8090 jobs`).
- `lake env lean /dev/stdin` with `#print axioms` for
  `image_vonNeumannGenerated`, `gnsConj_image_sourceVN`,
  `bicommutantStarEquiv_sourceRepVN`,
  `folium_source_eq_pullback_folium_target`,
  `bicommutantStarEquiv_normal_of_characterization`,
  `bicommutant_normal_transport_package`, and
  `sanity_algebraicallyQuasiEquivalent` — passed; each reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Candidate byte comparison, forbidden-declaration scan, and `git diff --check`
  — passed.

## Cleanup and worktree state

Kept intentionally:

- `AristotleCandidates/BicommutantNormalTransport.lean`, the sole reviewed P40
  integration;
- the P40 quarantine archive and extracted snapshot under
  `aristotle_responses/`; and
- this closeout review.

All pre-existing modified and untracked work was preserved. No manuscript
file was modified, and no commit, push, dependency update, archive build, or
dependency fetch was performed in the quarantine snapshot.
