# Review: FF08 initial/tail finite-support configuration split prompt

Verdict: APPROVED

## Findings

1. Severity: cleared
   Location: `aristotle_tasks/FF08-initial-tail-configuration-split.md:24-59`
   The proposed maps are genuinely additive endomorphisms of
   `CountablePauliConfiguration = ℕ →₀ ZMod 2`; they make no claim about a
   Hilbert-space tensor product, a finite-dimensional image, a local algebra,
   a state, or the finite-fiber theorem.  This is the correct strictly
   algebraic precursor to, but not a substitute for, the finite/tail
   factorization required by `technical.tex:124-140`.

2. Severity: cleared
   Location: task lines 37-53
   The five requested conclusions are the right small package.  The predicate
   `i < n` has complement `n ≤ i` by `Nat.not_lt`, so
   `configurationInitial_add_configurationTail` is exhaustive.  The two
   coordinate-zero statements establish the disjointness coordinatewise: at
   every index the initial component vanishes on the tail side and the tail
   component vanishes on the initial side.  The one-bit statements correctly
   identify the two corresponding one-site restrictions.  No tensor or
   finite-matrix conclusion is implicit in any of these types.

3. Severity: cleared after revision
   Location: task lines 69-70 and 80-88
   The prompt now requires `namespace FiniteFiber ... end FiniteFiber`, which
   fixes the public integration names and resolves the existing abbreviation
   and `configurationBit` at the intended namespace.  It also now names the
   reliable mathlib facts and the exact complement normalization:

   - `Finsupp.filter_pos_add_filter_neg` with
     `simpa only [configurationInitial, configurationTail, Nat.not_lt]`;
   - `Finsupp.filter_apply_neg`, using `Nat.not_lt.mpr h` and
     `Nat.not_le.mpr h` for the two zero claims; and
   - `Finsupp.filter_single_of_pos` for the one-bit claims.

   These APIs are genuine in the pinned mathlib.  A local stdin dry run of the
   two definitions and all five target theorem shapes compiled.  `Finsupp.filter_apply_pos`
   also exists, but is not needed for the requested results and need not be
   added to the prompt.

4. Severity: cleared
   Location: task lines 61-73 and 89-102
   Ownership is confined to the candidate file, the direct no-placeholder
   rule covers the relevant unsound declaration forms, and the task expressly
   forbids extra analytic/operator claims and unrelated edits.  The standalone
   compile check is appropriate for the candidate stage.

## Residual risks

- On integration, the five public theorems must still be added to the package
  axiom audit and checked with `#print axioms`; standalone compilation is not
  the eventual package closeout.
- This split remains only a decomposition inside `ℕ →₀ ZMod 2`.  It does not
  construct the required finite-coordinate type, an $L^2$ unitary, the
  $M_{2^n}(\mathbb C)\otimes 1$ local image, a quasi-local algebra or state,
  or any GNS/corner/finiteness conclusion.
