# FF14: coherence of finite-region matrix embeddings

Work in the existing Lean project `formalization_finite_fibers`.

Create a new file `FiniteFiber/FiniteRegionEmbeddingCoherence.lean` importing
`FiniteFiber.FiniteRegionQubitAlgebra`.  Do not modify existing files and do
not attempt the infinite-system theorem.

For finite regions `F F' F'' : Finset Site` and inclusions
`hFF' : F ⊆ F'`, `hF'F'' : F' ⊆ F''`, prove the directed-system coherence
identity

`finiteRegionEmbed F' F'' hF'F''
    (finiteRegionEmbed F F' hFF' A) =
  finiteRegionEmbed F F'' (hF'F''.trans hFF') A`.

The result must hold for every matrix `A`; handle proof-irrelevance of subset
proofs explicitly if needed.  Use the actual coordinate split and Kronecker
definitions already present in the project, not an abstract axiom asserting
coherence.  If the existing coordinate definitions make this statement
unprovable without an additional explicit equivalence lemma, provide that
lemma and prove the strongest exact coherence result available, documenting
the obstruction rather than weakening the theorem silently.

Use no `sorry`, `admit`, new axioms, `unsafe`, or opaque escape hatches.  Return
the complete candidate file and the exact Lean build command/result.
