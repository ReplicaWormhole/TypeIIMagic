# P51 recovery review — full finite corner and central type-III exclusion

## Decision

**Status: accepted after correcting the packet's manuscript source range; Lane G may advance.**

The first closeout correctly quarantined the candidate because the packet cited
only `main.tex:1456-1536`, omitting the finite-corner argument it used.  The
authoritative manuscript contains the complete relevant chain at
`main.tex:1418-1539`: the finite-projection corollary and proof at lines
1422-1445, its abstract lemma at 1447-1450, fullness at 1473-1499, and the
central-summand theorem and proof at 1501-1539.  The packet and integrated
candidate now cite that full range.  The rejected closeout remains preserved in
`reviews/P51-full-finite-corner-central-exclusion-closeout.md`.

The exact task-specific archive was
`aristotle_responses/P51-full-finite-corner-central-exclusion-10f2fe5c-f7631f0b.tar.gz`.
Its candidate was extracted only in the task-specific quarantine directory and
had SHA-256
`99294408c47f35f5716520b2a423fc399f6957bab6c632a184e5aa5daa75264c`.
Only `AristotleCandidates/FullFiniteCornerCentralExclusion.lean` was integrated.
After correcting documentation locators, its live SHA-256 is
`448540c487d612be26c66a70e05927d765dd8f4c90d1e8420c29b70cad981317`;
no proof term or declaration type was changed.

## Exact checked conclusions

- `isFiniteProjection_of_faithfulNormalTracialCorner` proves that the P50
  faithful tracial corner functional makes `q` a finite projection of `M`.
- `isFull_of_dense_cyclic_vectors` proves fullness from complement commutation,
  `q Omega = Omega`, and density of the vectors `b a Omega`.
- `central_summand_nonzero_finite_projection` produces the explicit projection
  `z * q`, proves it nonzero and finite in `M`, places it in `z M`, and proves
  its finiteness relative to that summand.
- `not_isTypeIIILike_centralSummand` derives the project-local type-III
  obstruction.
- `full_finite_corner_central_exclusion` exports the conditional Lane-G result
  from the P50 finite-system, represented-algebra, commutation, and density
  premises.

The proof of finiteness uses P50's traciality and faithfulness fields, not its
field currently named `normal`.  Therefore the separately tracked need to
formalize the standard ultraweak definition of normality does not invalidate
P51's finite-projection or central-summand conclusions.

## Scope and remaining assumptions

The result is conditional on the same explicit inputs as P50: the compatible
finite codespace system and decreasing tower, the norm-closed represented
regional algebra with the stated finite-stage density data, complement
commutation, and the dense-vector premise.  It constructs no global trace or
weight.  `IsTypeIIILike` is a project-local set-relative obstruction predicate;
the module does not formalize direct integrals, trivial center, Lane-H tensor
factorization, or the complete external classification theory of type III
von Neumann algebras.

## Verification

- `lake build AristotleCandidates.FullFiniteCornerCentralExclusion` — passed.
- Axiom audit of the four declarations named above — each reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan — no executable `sorry`, `admit`, user `axiom`,
  `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration.
- Source audit against the authoritative manuscript — the corrected range
  `main.tex:1418-1539` covers every manuscript-facing claim used by P51.
- `git diff --check` — passed.

## Adversarial review

No acceptance-blocking defect remains.  The proof produces a nonzero finite
projection, rather than merely a finite-dimensional subalgebra, in every
nonzero central summand.  Its conditional hypotheses and its project-local
type-III obstruction remain explicit.  The ultraweak-normality bridge is a
separate mandatory infrastructure package and is not silently claimed here.

AUTOPILOT_ACCEPTED: yes

AUTOPILOT_DECISION: advance
