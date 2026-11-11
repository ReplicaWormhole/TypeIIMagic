# FF07 — mixed countable shift-phase relations

## Status

Accepted and integrated on August 5, 2026.

- Project: `c280ca7f-3f19-40e9-9bd3-fd3a4e718cc5`
- Final remote status: `IDLE` (completed)

Only `AristotleCandidates/CountableMixedPauliRelations.lean` was integrated
into the live package.  The full remote snapshot was quarantined at
`../aristotle_responses/FF07-extracted/`; its unrelated README attribution
insertion was rejected.  The independent prompt audit is approved; see
`../aristotle_responses/FF07-prompt-adversarial-review.md`.  The final
integration review is approved at
`../aristotle_responses/FF07-integration-adversarial-review.md`.

## Source locator

- `formalization_finite_fibers/FiniteFiber/CountablePauliRepresentation.lean`
- Lean toolchain: `leanprover/lean4:v4.28.0`

## Mathematical statements

Prove exactly the same-site anticommutation and distinct-site commutation
relations for the bounded generators:

```lean
theorem countablePauliZ_comp_countablePauliX_same (i : ℕ) :
    (countablePauliZ i).comp (countablePauliX i) =
      -((countablePauliX i).comp (countablePauliZ i)) := by
  -- completed proof

theorem countablePauliZ_comp_countablePauliX_other
    (i j : ℕ) (hij : i ≠ j) :
    (countablePauliZ i).comp (countablePauliX j) =
      (countablePauliX j).comp (countablePauliZ i) := by
  -- completed proof
```

The sign and composition order are intentional.  With the existing pullback
convention, `X_i f (x) = f (configurationBit i + x)`, so the same-site
identity `phaseCharacter_bit_add` gives the displayed minus sign.  The
distinct-site relation uses `phaseCharacter_other_bit_add`.

This is only the pair of mixed bounded-operator relations.  It is not a
matrix realization, finite/tail factorization, local algebra, quasilocal
closure, state, GNS construction, or finite-fiber theorem.

## Allowed ownership

Create and modify **only**:

```text
AristotleCandidates/CountableMixedPauliRelations.lean
```

Do not modify `FiniteFiber/`, `tests/`, the package manifest, any README, or
any manuscript/work record.  Do not add attribution text or unrelated files.

## Available local facts and proof constraints

- Import `FiniteFiber.CountablePauliRepresentation`.
- Reuse `configurationShift_apply_ae`, `configurationPhase_apply_ae`,
  `phaseCharacter_bit_add`, and `phaseCharacter_other_bit_add`.
- The source module's translation pullback helper is private.  In the isolated
  candidate, you may reproduce an appropriately private AE pullback helper
  using `measurePreserving_add_left`; when promoted, any duplicate helper will
  be reconciled with the existing source-local helper.
- All equality of `Lp` representatives must be established almost everywhere.
  Do not assert invalid pointwise equality of representatives.
- Do not weaken the displayed theorems or introduce extra hypotheses.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `implemented_by`.

## Verification and response

Run:

```bash
lake env lean AristotleCandidates/CountableMixedPauliRelations.lean
```

Return a compiling candidate containing exactly the private helpers (if any)
and the two public theorems needed for these results.  If blocked, return a
precise minimal API/proof-obligation report without a placeholder.
