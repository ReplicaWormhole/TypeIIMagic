# Review: FF10 finite-region qubit local-algebra prompt

## Verdict

Approved after revision.

## Mathematical-fidelity review

The requested construction is the literal finite-region realization of the
manuscript inclusion $\cA_F\hookrightarrow\cA_{F'}$ for $F\subseteq F'$:
the qubit basis on $F'$ splits canonically into the retained basis on $F$ and
the basis on $F'\setminus F$, and the existing reindexed Kronecker inclusion
implements $A\mapsto A\otimes\id$.  No finiteness assumption on the ambient
site type is needed beyond decidable equality.  The discarded basis is
nonempty even when $F'=F$, because the constant-zero bit function exists.

The prompt correctly excludes Pauli/stabilizer realization, inclusion
coherence for three regions, any colimit or norm closure, state/GNS data, and
the finite-fiber theorem.

## Lean/API review

The original norm clause was not well typed for arbitrary finite-region
matrices: the existing operator-norm $C^*$ instance is scoped to the
ordered-qubit matrix type.  FF10 now requires `open scoped ComplexOrder
Kronecker` and a candidate-local noncomputable
`CStarMatrix.instCStarAlgebra` instance for each finite-region matrix type.
With that repair, the finite set coordinate equivalence, `coordinateEmbedRight`,
its explicit formula and injectivity theorem, and
`NonUnitalStarAlgHom.norm_map` are available with the required finite-type
instances.  The prompt fixes the basis alias as `↥F → Fin 2` and requires
explicit `Finset.mem_sdiff` subtype proofs.

## Residual risk

This is candidate-only work.  If a result is later accepted, it must be
quarantined, locally rebuilt, added to the axiom audit, and adversarially
reviewed before integration.  No remote metadata or unrelated files may be
accepted.
