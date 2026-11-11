# Adversarial integration review: FF07 mixed Pauli relations

## Findings

1. Severity: cleared
   Location: `FF07-extracted/project_aristotle/AristotleCandidates/CountableMixedPauliRelations.lean:30-75`
   Finding: The two composite AE-action lemmas have the correct pullback
   orientation.  `Z_i.comp X_j` carries the unshifted factor
   `χ_i(x)`, while `X_j.comp Z_i` carries `χ_i(bit_j + x)`.  Consequently the
   same-site theorem applies `phaseCharacter_bit_add` and obtains precisely
   the displayed minus sign, and the distinct-site theorem applies
   `phaseCharacter_other_bit_add i j hij` with the correct hypothesis.
   Required correction: None.

2. Severity: cleared
   Location: candidate lines 21-28, 41-64
   Finding: The candidate correctly pulls the phase AE formula back through
   counting-measure-preserving translation.  For the same-site negative
   right-hand side it also uses `Lp.coeFn_neg` and `Pi.neg_apply`, so it never
   treats a negated `Lp` representative as definitionally pointwise.  This
   resolves the principal AE/Lp-negation risk.
   Required correction: None.

3. Severity: cleared with integration instruction
   Location: candidate lines 21-28, 48-50; live source lines 98-105
   Finding: `ae_comp_add_left_candidate` is an exact private duplicate of the
   live source-local helper `ae_comp_add_left`.  A read-only virtual integration
   replacing the candidate name by the existing helper compiled with all four
   public FF05--FF07 theorems and standard axioms.
   Required correction: During manual promotion, do not copy the duplicate
   helper; replace its sole use with the existing source-local
   `ae_comp_add_left`.

4. Severity: cleared
   Location: candidate lines 54-75 and I004 `HANDOFF.md:49-108`
   Finding: The two public theorems are exactly the same-site and distinct-site
   mixed bounded-operator relations.  They do not claim a matrix realization,
   finite/tail factorization, local algebra, quasilocal closure, state, GNS
   construction, or the finite-fiber theorem.
   Required correction: None.

5. Severity: non-blocking workflow violation outside the candidate
   Location: `FF07-extracted/project_aristotle/README.md:1-8`
   Finding: The extracted remote snapshot contains unauthorized Aristotle
   README attribution text outside the candidate-only ownership boundary.
   Required correction: Integrate the candidate theorem declarations after the
   helper reconciliation in finding 3; reject the README insertion and every
   other non-candidate archive change.

## Verdict

APPROVED

The candidate compiles directly against the live package, and the
source-helper-reconciled virtual integration compiles as well.  It has no
prohibited declarations; both public theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
