# FF09 — additive initial/tail configuration equivalence

## Status

Submitted to Aristotle on August 5, 2026; result not yet retrieved or
integrated.

- Project: `f78a4014-b751-45d0-af0a-b1e8a9e32c11`
- Latest observed remote status: `RUNNING`
- Prompt audit: `../aristotle_responses/FF09-prompt-adversarial-review.md`

The remote result is candidate-only.  It must be downloaded into quarantine,
locally rebuilt, added to the public axiom audit, and passed through a fresh
post-result adversarial review before any declaration is integrated.

## Source locator

- `formalization_finite_fibers/FiniteFiber/CountablePauliRepresentation.lean`
- Lean toolchain: `leanprover/lean4:v4.28.0`
- Existing FF08 declarations: `configurationInitial`, `configurationTail`,
  `configurationInitial_add_configurationTail`,
  `configurationInitial_apply_of_le`, and
  `configurationTail_apply_of_lt`.

## Mathematical statement

For a cut `n : ℕ`, let `K_<n` be the additive subgroup of

```lean
CountablePauliConfiguration = ℕ →₀ ZMod 2
```

whose configurations vanish at every `i` with `n ≤ i`, and let `K_≥n` be the
additive subgroup whose configurations vanish at every `i < n`.

Define the following public declarations inside `namespace FiniteFiber`:

```lean
def initialConfigurationSubgroup (n : ℕ) :
    AddSubgroup CountablePauliConfiguration

def tailConfigurationSubgroup (n : ℕ) :
    AddSubgroup CountablePauliConfiguration

noncomputable def configurationInitialTailAddEquiv (n : ℕ) :
    CountablePauliConfiguration ≃+
      initialConfigurationSubgroup n × tailConfigurationSubgroup n
```

The first definition must use
`carrier := {x | ∀ i, n ≤ i → x i = 0}`, and the second must use
`carrier := {x | ∀ i, i < n → x i = 0}`.

The equivalence must send `x` to the pair of its checked FF08 initial and tail
filters, and its inverse must send `(u, v)` to `u.1 + v.1`.  Prove the two
inverse laws and additive compatibility.  Private helper lemmas are allowed
when necessary.

This is an additive-group decomposition of finitely supported configurations.
It does **not** identify the initial subgroup with a finite coordinate space,
does **not** construct a Hilbert-space tensor product or unitary, and does
**not** assert a matrix algebra, local/quasi-local algebra, state, GNS
construction, or finite-fiber result.

## Allowed ownership

Create and modify **only**:

```text
AristotleCandidates/InitialTailAddEquiv.lean
```

Do not modify `FiniteFiber/`, `tests/`, the package manifest, any README, or
any manuscript/work record.  Do not add attribution text or unrelated files.

## Available facts and proof constraints

- Import `FiniteFiber.CountablePauliRepresentation`.
- Use exactly the displayed carriers: the initial subgroup vanishes on
  `n ≤ i`, and the tail subgroup vanishes on `i < n`.  The subgroup closure
  proofs must establish zero, addition, and negation closure, not rely on an
  axiom or unproved typeclass assumption.
- For the left inverse, reuse
  `configurationInitial_add_configurationTail`.
- For the right inverse, reason coordinatewise: on `i < n`, the tail component
  vanishes; on `n ≤ i`, the initial component vanishes.  Use Finsupp extensionality
  and the pointwise `Finsupp.filter_apply_pos`/`Finsupp.filter_apply_neg`
  lemmas with their predicates explicit where helpful.
- Mark the additive equivalence `noncomputable`: a direct structure
  construction otherwise reaches a Lean IR failure because the relevant
  `Finsupp` additive instance lacks executable code.
- Keep all claims at the additive configuration level.  Do not introduce
  measure theory, `Lp`, `ContinuousLinearMap`, a tensor product, or a finite
  cardinality conclusion.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `implemented_by`.

## Verification and response

Run:

```bash
lake env lean AristotleCandidates/InitialTailAddEquiv.lean
```

Return a compiling candidate containing exactly the public declarations above,
plus indispensable private helpers.  If blocked, return a precise minimal
API/proof-obligation report without a placeholder.
