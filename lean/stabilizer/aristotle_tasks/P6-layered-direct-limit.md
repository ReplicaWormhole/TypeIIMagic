# P6 — coherent finite-layer direct-limit equivalence

> **Legacy infrastructure packet.** This packet is not manuscript-derived:
> gLU/refinement/layer-coherence language here must not be treated as a
> hypothesis or claim of `main.tex`. See `../CONTEXT-LEDGER.md`.

Work only on a new module named AristotleCandidates/LayeredDirectLimit.lean.

Import Formalization.CoherentBasisEquiv and
Formalization.AlgebraicLimitStarHom.  Define a transparent interface for a
pair of finite-stage directed systems together with:

- finite-stage star-algebra equivalences;
- source and target finite Pauli-word bases;
- refinement embeddings for both systems;
- label maps and phase-corrected word images; and
- finite-stage basis equations proving that every square commutes on Pauli
  words.

Use starAlgEquiv_commutes_of_basis or
starAlgEquiv_commutes_of_source_basis to derive whole-stage compatibility.
Then use algebraicLimitStarAlgEquiv to construct the induced star-algebra
equivalence of the two algebraic directed limits.  Prove its formula on every
finite-stage representative.

The interface must clearly state that finite-stage maps and their coherence are
supplied input.  It must not claim that a bare gLU condition, finite support,
or an adapted symplectic basis alone produces them.  It must not construct a
C-star completion, normal representation, GNS equivalence, or factor
classification.

Do not use sorry, admit, or axiom; do not modify existing project files.  Build
the owned module with:

    lake build AristotleCandidates.LayeredDirectLimit
