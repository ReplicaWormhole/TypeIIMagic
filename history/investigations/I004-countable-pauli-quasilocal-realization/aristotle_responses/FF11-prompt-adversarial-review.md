# Review: FF11 phase-free finite-region Pauli matrices prompt

## Verdict

**APPROVED.**

## Findings

1. **Cleared — faithful finite-region object.**  The manuscript defines a
   local Pauli operator on a finite region as a tensor product of the four
   Hermitian one-site labels and identifies a smaller local algebra in a
   larger one by tensoring with the identity
   (`writing/overleaf_prl_stabilizer_region_algebras/main.tex:812-885`).  The
   candidate's matrix-entry product over `↥F` is exactly that object on the
   already checked basis `finiteRegionBasis F`; it does not introduce an
   arbitrary ordering of sites.

2. **Cleared — correct locality theorem.**  The target
   `finiteRegionEmbed F F' hFF' P_F(a) = P_F'(pad_I a)` is the literal
   finite-region version of the manuscript's `A |-> A tensor id` inclusion.
   It is correctly phrased through `finiteRegionEmbed` and its canonical
   `finiteRegionSplitEquiv`, rather than asserting an ill-typed unreindexed
   tensor equality on the `F'` basis.  The all-identity and self-adjoint
   statements are standard finite-dimensional facts needed for a local
   Hermitian Pauli-string interface.

3. **Cleared — phase convention is not smuggled past the boundary.**  The
   current `FullPauliWord` normal form is `i^phase X^x Z^z`, while its
   canonical projective `(1,1)` label is the Hermitian matrix `Y`.  Since the
   present matrices obey `X Z = -i Y`, an uncorrected phase-zero normal-form
   word would not map to the requested label matrix.  The explicit exclusion
   of every `FullPauliWord` map, group-homomorphism, and multiplication claim
   is therefore necessary and mathematically correct.  A later full
   representation must include the `ZMod 4` phase/Y-count correction; a
   Boolean sign would be insufficient.

4. **Cleared — Lean API and task size.**  The direct subtype product avoids
   noncanonical `Fin n` enumerations and their additional coherence theorem.
   The pinned project already exposes the required support APIs:
   `finiteRegionEmbed_apply`, `finiteRegionSplitEquiv`, `Finset.prod_sdiff`,
   `Finset.prod_subtype`, `Matrix.reindex_apply`, `Matrix.kronecker_apply`,
   `Matrix.one_apply`, `PauliLabel.matrix_I_eq_one`, and
   `PauliLabel.matrix_isSelfAdjoint`.  The split-factorization and
   all-identity arguments are nontrivial but bounded; they are properly
   confined to private helpers, leaving five focused public declarations.

5. **Cleared — scope and ownership.**  Candidate-only ownership, the
   no-placeholder prohibition, and the exclusions of syntactic
   support/locality, three-region coherence, colimits, closure, states, GNS,
   and the finite-projection theorem prevent the packet from promoting a
   finite-dimensional local computation into a completed global theorem.

## Residual risk

The result, if returned, must still be quarantined, rebuilt against the live
package, added to the public axiom audit, and adversarially reviewed before
integration.  Even a successful FF11 would only realize phase-free Hermitian
finite-region strings; the full phased Pauli/stabilizer representation and
all quasilocal/GNS/corner obligations remain open.
