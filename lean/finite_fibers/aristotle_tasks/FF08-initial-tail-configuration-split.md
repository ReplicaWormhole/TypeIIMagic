# FF08 — initial/tail finite-support configuration split

## Status

Accepted and integrated on August 5, 2026.

- Project: `5a41c5b2-24ef-4f49-9d6f-03e203a80ff3`
- Final remote status: `IDLE` (completed)
- Prompt audit: `../aristotle_responses/FF08-prompt-adversarial-review.md`
- Integration audit: `../aristotle_responses/FF08-integration-adversarial-review.md`

Only `AristotleCandidates/InitialTailConfigurationSplit.lean` was integrated
into the live package.  The full remote snapshot is quarantined at
`../aristotle_responses/FF08-extracted/`; its README attribution insertion,
stale HANDOFF deletion, and metadata were rejected.  The declarations were
locally rebuilt and added to the public axiom audit before integration.

## Source locator

- `formalization_finite_fibers/FiniteFiber/CountablePauliRepresentation.lean`
- Lean toolchain: `leanprover/lean4:v4.28.0`
- Relevant mathlib API:
  `Finsupp.filter`, `Finsupp.filterAddHom`, and
  `Finsupp.filter_pos_add_filter_neg` in `Mathlib/Data/Finsupp/Basic.lean`.

## Mathematical statement

For the configuration group

```lean
CountablePauliConfiguration = ℕ →₀ ZMod 2,
```

define the initial and tail restrictions at a cut `n` by filtering coordinates
with `i < n` and `n ≤ i`, respectively.  The required candidate must define
the following additive maps and prove the listed algebraic facts:

```lean
def configurationInitial (n : ℕ) :
    CountablePauliConfiguration →+ CountablePauliConfiguration :=
  Finsupp.filterAddHom fun i => i < n

def configurationTail (n : ℕ) :
    CountablePauliConfiguration →+ CountablePauliConfiguration :=
  Finsupp.filterAddHom fun i => n ≤ i

theorem configurationInitial_add_configurationTail
    (n : ℕ) (x : CountablePauliConfiguration) :
    configurationInitial n x + configurationTail n x = x

theorem configurationInitial_apply_of_le
    (n : ℕ) (x : CountablePauliConfiguration) (i : ℕ) (h : n ≤ i) :
    configurationInitial n x i = 0

theorem configurationTail_apply_of_lt
    (n : ℕ) (x : CountablePauliConfiguration) (i : ℕ) (h : i < n) :
    configurationTail n x i = 0

theorem configurationInitial_bit_of_lt (n i : ℕ) (h : i < n) :
    configurationInitial n (configurationBit i) = configurationBit i

theorem configurationTail_bit_of_le (n i : ℕ) (h : n ≤ i) :
    configurationTail n (configurationBit i) = configurationBit i
```

This is only the additive decomposition of finitely supported binary
configurations.  It is deliberately **not** a Hilbert-space tensor-product
factorization, a finite-dimensional matrix realization, a local algebra, a
quasi-local closure, a state/GNS construction, or a finite-fiber theorem.

## Allowed ownership

Create and modify **only**:

```text
AristotleCandidates/InitialTailConfigurationSplit.lean
```

Place every declaration in `namespace FiniteFiber ... end FiniteFiber` so the
candidate has the stated integration names and types.

Do not modify `FiniteFiber/`, `tests/`, the package manifest, any README, or
any manuscript/work record.  Do not add attribution text or unrelated files.

## Available local facts and proof constraints

- Import `FiniteFiber.CountablePauliRepresentation`.
- Use the existing abbreviation `CountablePauliConfiguration` and existing
  one-site generator `configurationBit`.
- `Finsupp.filter_pos_add_filter_neg` is the intended decomposition lemma;
  reconcile its complement predicate `¬ i < n` with `n ≤ i` explicitly.
- The intended decomposition proof is
  `simpa only [configurationInitial, configurationTail, Nat.not_lt] using
  Finsupp.filter_pos_add_filter_neg x (fun i => i < n)`.
- For the coordinate-zero claims, reduce to `Finsupp.filter` and use
  `Finsupp.filter_apply_neg`, with `Nat.not_lt.mpr h` for the initial part and
  `Nat.not_le.mpr h` for the tail part.  For the one-bit claims, use
  `Finsupp.filter_single_of_pos` with the respective predicate.
- Keep the requested maps additive homomorphisms.  Do not introduce an
  unsupported equivalence, measure-theoretic assertion, or bounded operator.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `implemented_by`.

## Verification and response

Run:

```bash
lake env lean AristotleCandidates/InitialTailConfigurationSplit.lean
```

Return a compiling candidate containing exactly the definitions and public
theorems above, plus private helpers only when indispensable.  If blocked,
return a precise minimal API/proof-obligation report without a placeholder.
