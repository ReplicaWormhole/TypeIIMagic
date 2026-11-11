# FF16 live closeout adversarial review

## Decision

**Accepted at the packet's stated finite-infrastructure scope.** Aristotle task `a1684489-8deb-4f62-8f5a-a592570dd778` was downloaded only into the I004 response quarantine. The live `FiniteFiber/FullPauliSupportLocality.lean` is byte-identical to the reviewed candidate (SHA-256 `33c06ce8a574c76846b66765ffc311c113365e22ef0112bc30a10bd526d1368d`). No build, dependency update, or dependency fetch was run in the downloaded snapshot.

## Reviewed declarations and assumptions

**Proved.**

- `FullPauliWord.SupportedIn a F := a.label.support ⊆ F` is the explicit finite support predicate. `FullPauliWord.HasFiniteRegionRealization a F` means that there is `A : finiteRegionQubitAlgebra F` whose `finiteRegionEmbed` equals `fullPauliRegionMatrix F' a` for every finite enlargement `F ⊆ F'`.
- `finiteRegionEmbed_fullPauliRegionMatrix (F) (F') (hFF') (a) (ha)` proves identity padding under the exact premise `ha : a.SupportedIn F`.
- `supportedIn_of_finiteRegionEmbed_eq (F) (F') (hFF') (a) (hsupp) (A) (hA)` proves the converse under `hsupp : a.SupportedIn F'` and `hA : fullPauliRegionMatrix F' a = finiteRegionEmbed F F' hFF' A`. The ambient premise is necessary: support wholly outside inspected `F'` is invisible there.
- `supportedIn_iff_hasFiniteRegionRealization (F) (a)` is the requested equivalence. Its reverse direction applies the preceding theorem to `F ∪ a.label.support`, so it does not silently discard outside support.
- `eq_fullPauliRegionMatrix_of_realization (F) (a) (A) (hA)` proves uniqueness by evaluating the all-enlargements premise at `F` itself.

Supporting compiled lemmas: `labelXBit_of_fst_eq_zero`, `labelXBit_of_fst_ne_zero`, `normalFormOneSiteMatrix_labelXBit_ne_zero`, `normalFormOneSiteMatrix_zero_zero_of_fst_eq_zero`, `normalFormOneSiteMatrix_one_one_of_pure_z`, `fullPauliRegionMatrix_apply`, `zmod4PhaseFactor_ne_zero`, `restrictLabel_eq_pad_of_supportedIn`, and `finiteRegionEmbed_self`.

**Partial.** This is an equivalence between explicit word support and the stated finite-region realization predicate only. It does not prove global-algebra membership, multi-region coherence beyond supplied identity padding, a directed colimit, norm closure, state, GNS representation, normality, von Neumann-algebra result, or finite-fiber conclusion.

**Blocked.** None at FF16 scope.

**Failed.** None. The remote snapshot's `FiniteFiber.lean` import change, README edit, metadata, handoff, manuscript copy, and all other noncandidate files were rejected. Only the candidate module and raw quarantine records were retained.

## Adversarial findings

No confirmed defect in the accepted scope.

- The apparent one-region counterexample is excluded by `HasFiniteRegionRealization`, which quantifies over every finite enlargement; the proof explicitly uses `F ∪ a.label.support`.
- The converse retains its necessary support-in-`F'` premise and does not identify syntactic support with an unspecified local/global algebra.
- The proof's nonzero phase and one-site matrix arguments are over `ℂ`; its cancellation step is justified by the established nonzero matrix entry.
- The candidate has no declaration headed by `axiom`, `opaque`, `unsafe`, or `implemented_by`, and contains no `sorry`, `admit`, or `native_decide`.

## Live checks

- `lake build FiniteFiber.FullPauliSupportLocality` — passed.
- `lake build FiniteFiber.FiniteRegionFullPauliMultiplication` — passed.
- `lake build FiniteFiber` — passed.
- `lake build` — passed.
- `lake env lean --stdin` with `#print axioms` for every FF16 public theorem — passed; each footprint is a subset of `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean tests/AxiomAudit.lean` — passed.
- Placeholder declaration scan and `git diff --check` — passed.

## Residual risk and cleanup

Lean compilation and axiom inspection validate the formal declarations and their stated assumptions; they do not establish later quasilocal/GNS/type bridges. The raw archive is `FF16-full-pauli-support-locality.tar.gz`, SHA-256 `447389053d147319b70c0c519f027c25bfc78c085dcfca68c23e4b793345b727`, and the extracted remote project remains quarantined at `FF16-extracted/`. Pre-existing dirty and untracked project work was preserved. No manuscript edit, commit, push, or destructive cleanup occurred.
