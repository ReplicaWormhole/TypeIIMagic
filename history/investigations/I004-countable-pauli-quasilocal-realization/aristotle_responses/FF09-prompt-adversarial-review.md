# Review: FF09 initial/tail additive-equivalence prompt

Verdict: APPROVED

## Findings

1. Severity: cleared after revision
   Location: `aristotle_tasks/FF09-initial-tail-additive-equivalence.md:31-49,70-83`
   The prompt now fixes the subgroup carriers exactly:

   ```lean
   {x | ∀ i, n ≤ i → x i = 0}
   ```

   for the initial subgroup and

   ```lean
   {x | ∀ i, i < n → x i = 0}
   ```

   for the tail subgroup.  It also requires genuine zero/add/neg closure and
   declares the additive equivalence `noncomputable`.  The latter is necessary:
   a direct executable `def` reaches Lean's IR failure because the relevant
   `Finsupp` additive instance has no executable code.

2. Severity: cleared
   Location: task lines 37-55 and 75-86
   The direction is mathematically correct.  The forward map sends
   `x` to the pair of the FF08 filters, each bundled with its required
   coordinate-vanishing proof; its inverse sends `(u, v)` to `u.1 + v.1`.
   `configurationInitial_add_configurationTail` supplies the left inverse.
   The right inverse follows coordinatewise from the two carrier hypotheses,
   `Finsupp.filter_apply_pos`, `Finsupp.filter_apply_neg`, and Finsupp/subtype
   extensionality.  A local MWE of both exact subgroup definitions and this
   `noncomputable AddEquiv` compiled against the live FF08 source.

3. Severity: cleared
   Location: task lines 51-55 and 84-87
   The three declarations faithfully state only an additive decomposition of
   `ℕ →₀ ZMod 2`.  They do not identify the initial component with a finite
   coordinate type and do not claim a Hilbert factorization or unitary, matrix
   image, local/quasi-local algebra, state, GNS datum, or finite-fiber result.

4. Severity: cleared
   Location: task lines 57-66 and 89-99
   The candidate ownership and no-placeholder restrictions are adequate for
   the remote candidate stage.  The prompt confines the result to one candidate
   file and explicitly forbids analytic/operator escalation and unrelated
   changes.

## Residual risks

- The candidate's right-inverse proof will naturally need `Prod.ext`,
  `Subtype.ext`, and `Finsupp.ext` in addition to the named pointwise filter
  lemmas; these are ordinary private proof details, not additional public
  claims.
- On integration, add all three public declarations to `tests/AxiomAudit.lean`
  and run focused `#print axioms`; standalone candidate compilation is not
  package closeout.
