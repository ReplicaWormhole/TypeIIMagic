# FF19 live closeout adversarial review

## Decision

**Accepted at the packet's stated conditional quasilocal-state/GNS-interface
scope.** Aristotle project `269479d4-b0f7-45a7-9500-a3220a0a9798`, completed
task `c024cdf3-1bf8-439f-85f3-825e012a8af4`, was downloaded only to the I004
response quarantine. The raw archive is
`FF19-quasilocal-state-gns-interface.tar.gz` with SHA-256
`0a80611f014e598364362681c6782ced50bdce5ea2aa2c99412a3539fe308fef`; the
complete dependency-free snapshot remains under `FF19-extracted/`. No Lake
command, dependency update, or dependency fetch was run in that snapshot.

Only `FiniteFiber/QuasilocalStateGNSInterface.lean` was integrated. It is
byte-identical to the quarantined candidate (SHA-256
`227b8bb9cdd7e4c3961306fbac931079e722a5e273d8496fa52584cfc5893f55`). Remote
metadata, README changes, handoff changes, manuscript copies, and the remote
summary were rejected. No manuscript, root import, existing source module, or
user-owned dirty file was modified.

## Reviewed declarations and exact assumptions

**Proved.** The new conditional inputs are exactly these two structures.

1. `QuasilocalEmbedding Site A`, for `[CStarAlgebra A]`, has fields
   `embed : ∀ F, finiteRegionQubitAlgebra F →⋆ₐ[ℂ] A`,
   `embed_injective`, `embed_localInclusion`, and `dense_localAlgebra`.
   Thus it explicitly supplies the C-star completion/local embedding,
   faithfulness, FF18 inclusion coherence, and density of the finite local
   images.
2. `QuasilocalStabilizerState S Q`, for the preceding `Q` and the existing
   `S : FullPauliStabilizerSystem Site`, has fields
   `state : A →ₚ[ℂ] ℂ` and
   `state_embed : ∀ F x, state (Q.embed F x) = S.localState F x`.
   The state/GNS results additionally use the explicit ambient instances
   `[PartialOrder A] [StarOrderedRing A]`; no normality or factor premise is
   introduced.

The primary exact declarations checked are:

```text
QuasilocalEmbedding.norm_embed
  (F) (x) : ‖Q.embed F x‖ = ‖x‖
QuasilocalEmbedding.exists_localSet_common_region
  {Γ} {x y} : x ∈ Q.localSet Γ → y ∈ Q.localSet Γ →
    ∃ G, ↑G ⊆ Γ ∧ ∃ a b, Q.embed G a = x ∧ Q.embed G b = y
QuasilocalEmbedding.dense_localStarAlgebra_univ :
  Dense (Q.localStarAlgebra Set.univ : Set A)
QuasilocalStabilizerState.state_eq (W W') :
  (W.state : A → ℂ) = (W'.state : A → ℂ)
QuasilocalStabilizerState.state_embed_apply (F) (x) :
  W.state (Q.embed F x) = ((S.regionDensity F) * x).trace
QuasilocalStabilizerState.inner_gnsVector_gnsRepresentation_embed (F) (x) :
  ⟪W.gnsVector, W.gnsRepresentation (Q.embed F x) W.gnsVector⟫_ℂ =
    S.localState F x
QuasilocalStabilizerState.localRepresentation_localInclusion (F F') (hFF') (x) :
  W.localRepresentation F' (localInclusion hFF' x) =
    W.localRepresentation F x
QuasilocalStabilizerState.gnsRepresentation_fullPauliRegionMatrix_gnsVector
  (F) (g) :
  W.localRepresentation F (fullPauliRegionMatrix F (g : FullPauliWord Site))
    W.gnsVector = W.gnsVector
```

The file also proves `state_one`, `continuous_state`, local-word evaluation
independence, finite local-state positivity, and empty-site witnesses for both
interfaces. The continuity/isometry and normalization facts are derived from
the displayed inputs, not added as hidden premises.

**Partial.** This is an interface, not an infinite-lattice construction. It
does not construct a norm completion or a global state from finite data; both
remain the two supplied bundles above. It also proves no product/tensor GNS
factorization, normality, von Neumann closure, type classification, or
finite-fiber conclusion.

**Blocked.** None within FF19's conditional scope.

**Failed.** None. An initial automatic axiom-audit name extractor omitted
nested namespaces; it was rerun with the fully qualified declarations below
and does not reflect an artifact defect.

## Adversarial findings

No confirmed finding at the accepted scope.

- The direct-limit wording is confined to directed finite local images and a
  local star subalgebra. The module does not manufacture a quotient algebra or
  identify that subalgebra with a completed C-star algebra.
- The extension uniqueness result uses continuity of positive linear maps and
  the explicit density input. It does not reverse a density implication or
  assume a continuity bound for an unconstructed extension.
- Local stabilizer invariance is obtained only after the explicit finite
  stabilizer membership, support, and involutivity data supplied by FF18; it
  is not promoted to a global factor or type statement.
- The candidate contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
  `implemented_by`, or `native_decide` declaration.

## Live verification

All commands were run in the live `formalization_finite_fibers` project:

```text
lake env lean FiniteFiber/QuasilocalStateGNSInterface.lean  PASS
lake build FiniteFiber.QuasilocalStateGNSInterface           PASS
lake build FiniteFiber.FullPauliDirectedLocalSystem          PASS
lake build FiniteFiber                                       PASS
lake build                                                    PASS
lake env lean tests/AxiomAudit.lean                           PASS
```

A direct `#print axioms` audit covered all 37 public theorem declarations in
the candidate, including both nested namespaces. Every footprint is exactly
a subset of `propext`, `Classical.choice`, and `Quot.sound`. The source
placeholder/prohibited-declaration scan and `git diff --no-index --check`
also passed.

## Residual risk and cleanup

Lean compilation and the axiom audit validate the stated conditional
interface, not the missing construction of the infinite quasilocal completion
or its global state. The raw archive and full extracted snapshot are retained
as intentional quarantine records. Existing dirty and untracked repository
material was preserved; no commit, push, destructive cleanup, dependency
change, or manuscript edit occurred.
