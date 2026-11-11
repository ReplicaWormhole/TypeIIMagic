# P1 — regional finite-stage witness wrapper

Work only on a new module named AristotleCandidates/RegionalWitness.lean.

The project already proves
StabilizerHyperfinite.exists_stabilizerState_of_coherentPhaseQubitStages and
StabilizerHyperfinite.exists_stabilizerState_of_adaptedCoordinateStages in
Formalization/CoherentPhaseQubitState.lean.

Create a transparent Lean structure that packages exactly the finite-stage
inputs of the adapted-coordinate theorem:

- the pure-coordinate Boolean pattern;
- source finite-stage bases and source-label embeddings;
- target finite-qubit Pauli labels and coherent phases;
- finite-stage star-algebra equivalences;
- all three coherence clauses;
- the actual selected-Z/adapted-coordinate membership equivalence with
  regional stabilizer words.

Then prove a wrapper theorem whose conclusion is the phase-calibrated
stabilizer expectation formula on the algebraic directed limit:

    omega ([sourceBasis n v]) =
      if isStabilizer n v then phase n v else 0.

The proof must invoke the existing checked theorem; it must not replace any
clause by an axiom, sorry, admit, an unproved typeclass instance, or a weaker
assumption.  The structure must make clear that it is input data, not a
construction from a bare adapted Hamel basis.  Do not edit existing project
files or Formalization.lean; compile the owned module directly with:

    lake build AristotleCandidates.RegionalWitness
