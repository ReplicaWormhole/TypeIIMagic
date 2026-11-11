# FF18 live closeout adversarial review

## Decision

**Accepted at the packet's stated finite directed-system scope.** Aristotle
project `5fa4450b-d7be-40a2-be81-93d0605fab47`, completed task
`70f0b085-8ab2-4fd0-bd0e-f930b3bdae52`, was downloaded only to the I004
response quarantine. The raw archive is
`FF18-full-pauli-directed-local-system.tar.gz` with SHA-256
`61ffdc4cc89f189142d513ea80e3424e83d2061eb679acae10453b96ab35cf6b`;
the complete dependency-free snapshot remains under `FF18-extracted/`.
No Lake command, dependency update, or dependency fetch was run in that
snapshot.

Only `FiniteFiber/FullPauliDirectedLocalSystem.lean` was integrated. It is
byte-identical to the quarantined candidate. The remote README change and all
other snapshot files, including metadata, handoff, manuscript copy, and
summary, were rejected. No root import, manuscript, or existing source file
was modified.

## Reviewed declarations and assumptions

**Proved.**

- `finiteRegionQubitAlgebraDirectedSystem` is a `DirectedSystem` indexed
  by `Finset Site` with its inclusion order, whose maps are
  `localInclusion hFF' = finiteRegionEmbed F F' hFF'`. Its coherence is
  exactly the already-checked self and compositional embedding coherence.
- `finiteRegionPartialTrace F F' hFF'` is the explicitly defined linear
  partial trace over `F' \\ F`, under the exact premise
  `hFF' : F ⊆ F'`. Theorems
  `finiteRegionPartialTrace_trans` and
  `finiteRegionPartialTrace_comp` prove its elementwise and linear-map
  composition laws for explicit `F ⊆ F' ⊆ F''`.
- `localInclusion_fullPauliRegionMatrix` requires
  `a.SupportedIn F`; `finiteRegionPartialTrace_fullPauliRegionMatrix_dichotomy`
  additionally requires `a.SupportedIn F'` and gives either the rescaled
  supported term or zero. Thus no unsupported word is silently treated as
  local.
- `FullPauliStabilizerSystem` has precisely the explicit fields
  `group : Subgroup (FullPauliWord Site)`,
  `involutive : ∀ g ∈ group, g * g = 1`, and
  `consistent : negativeIdentity ∉ group`.
  Under only these fields, `finiteRegionPartialTrace_regionDensity` proves
  the finite density restriction formula.
- `localState_localInclusion` proves exactly
  `ω_{F'}(A ⊗ 1) = ω_F(A)` for each explicit `F ⊆ F'` and
  finite matrix `A`; `localState_comp_localInclusion`,
  `localState_localInclusion_trans`, and
  `finiteRegionPartialTrace_regionDensity_trans` give the stated
  functional, state, and density composition forms.

**Partial.** The module packages finite/direct-limit data only. It does not
form a colimit algebra, define quotient multiplication or star, prove
positivity or norm control on a colimit, take a norm completion, construct a
global state, or construct GNS, von Neumann, normality, type, or finite-fiber
data.

**Blocked.** None within FF18's stated scope.

**Failed.** None. The packet target is not weakened: the finite-stage
restriction identity and its composition law are present with their explicit
finite-region and stabilizer-consistency premises.

## Adversarial findings

No confirmed defect in the accepted scope.

- The phase and support route is retained from the checked full-Pauli
  finite-region modules. The partial-trace zero branch explicitly obtains a
  nonzero discarded-site label; it does not infer locality merely from a
  matrix equality on one region.
- The normalization is checked rather than assumed: the proof of density
  compatibility accounts for both the discarded factor
  `2 ^ |F' \\ F|` and the finite-region density normalization.
- The word “state” occurs only for the explicitly finite matrix functional.
  The source explicitly rules out quasilocal completion, global state, and
  GNS claims.
- The candidate contains no `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `implemented_by`, or `native_decide` declaration.

## Live verification

All commands were run in the live `formalization_finite_fibers` project:

```text
lake env lean FiniteFiber/FullPauliDirectedLocalSystem.lean       PASS
lake build FiniteFiber.FullPauliDirectedLocalSystem                PASS
lake build FiniteFiber                                             PASS
lake build                                                         PASS
lake build FiniteFiber.FullPauliStabilizerDensity                  PASS
lake build FiniteFiber.FiniteRegionEmbeddingCoherence             PASS
lake env lean tests/AxiomAudit.lean                                PASS
lake env lean tests/FullPauliMultiplicationAxiomAudit.lean        PASS
```

A direct `#print axioms` audit covered all 36 public theorem declarations
in the new module. Every footprint is exactly a subset of `propext`,
`Classical.choice`, and `Quot.sound`. A placeholder/prohibited-declaration
scan and `git diff --no-index --check` passed.

## Residual risk and cleanup

Lean compilation and the axiom audit validate the stated finite-dimensional
declarations, not the later quasilocal completion/state/GNS bridge. Existing
dirty and untracked repository material was preserved. The new Lean module,
raw archive, quarantined extraction, and this review are intentional retained
artifacts. No commit, push, manuscript edit, or destructive cleanup occurred.
