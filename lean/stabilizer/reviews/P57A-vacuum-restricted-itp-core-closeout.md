# P57A closeout review — vacuum-restricted infinite-tensor pre-Hilbert core

## Decision

**Status: proved at the stated shared-infrastructure scope; queue may advance.**

Aristotle task `563e769a-0e9b-4395-9895-e03c81c26851` was downloaded as
`aristotle_responses/P57A-vacuum-restricted-itp-core-205100d0-563e769a.tar.gz`
and extracted, without a build, dependency update, or fetch, only under
`aristotle_responses/P57A-vacuum-restricted-itp-core-205100d0-563e769a-quarantine/`.
Only the packet-authorized module
`AristotleCandidates/VacuumRestrictedInfiniteTensorProduct.lean` was
integrated into the live project.  The raw archive and quarantine extraction
remain intact response records.  No manuscript file was changed.

The quarantined response incorrectly said that the nominated local source
`<original-home>/Projects/current/bound_beating/formalize_itp/Formalization/InfiniteTensorProductHilbert.lean`
was absent.  It is present.  Local comparison confirms that the integrated
module independently re-expresses the source's proved finite-support core,
but with a finite-Gram-coordinate proof route rather than importing the other
project.  I corrected that provenance comment in the live integrated module;
this changes documentation only.  The candidate and quarantine SHA-256 values
therefore differ:

- live: `c4936227e370cd0d04c32f4d62807003ed688afba9ca661a330c696a5c75feca`;
- quarantined response: `ee8862347e606cc8ac629e3baa8909354ad288da9a4f5502c8639fa595633c52`.

## Source, assumptions, and exact declarations

This is **infrastructure only**, not a manuscript-facing assertion.  The
candidate imports only `Mathlib`; it does not import the `bound_beating`
project or any other package result.

All generic results use only the packet-authorized assumptions
`[DecidableEq ι]`, `[∀ i, NormedAddCommGroup (E i)]`, and
`[∀ i, InnerProductSpace ℂ (E i)]`.  The normalization premise

```lean
hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1
```

is used exactly where padding a product outside active support, positivity,
finite-mode kernel realization, finite-mode evaluation, and the exported
pre-inner-product core require it.  No completion, density, positivity, or
external analytical premise was added.

The load-bearing live declarations are:

- `exists_gram_coords` (lines 64--77), finite coordinates for every finite
  Gram matrix;
- `exists_finiteMode_realization` (88--104) and
  `sum_prod_inner_nonneg` (109--122), realizing the product kernel as a
  norm square in a finite coordinate tensor model;
- `VacuumTensor` (128--134), `kern` (153--154), and
  `kern_eq_prod_of_subset` (158--164), defining the finite-support
  elementary tensors and support-independent kernel;
- `itpInner` (183--184), `conj_itpInner_symm` (220--231),
  `itpInner_add_left` (234--247), and `itpInner_smul_left` (250--262),
  the algebraic sesquilinear extension;
- `itpInner_nonneg` (266--285), positivity for an arbitrary finite linear
  combination, and `re_itpInner_nonneg` (288--291);
- `itpCore` (295--301), the exported
  `PreInnerProductSpace.Core ℂ (ITPSpan Ω)`;
- `vacuumVector` and `itpInner_vacuumVector` (309--322), whose
  norm-square is one; and
- `exists_finiteMode_realization_kern` (329--341) and
  `itpInner_eq_finiteMode` (344--352), the finite-mode statements for the
  actual vacuum-restricted kernel and algebraic span.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The finite-support elementary tensors, their finite-product kernel, the free finite span, sesquilinearity, finite-mode realization, positivity on arbitrary finite sums, the pre-inner-product core, and the algebraic vacuum norm-square-one theorem are all explicit proved declarations. |
| partial | Quotienting the null space, completion, and an infinite tensor-product Hilbert-space instance are deliberately absent. |
| blocked | None at P57A scope.  The local Mathlib snapshot lacks a ready-made inner-product API for a general `PiTensorProduct`; the candidate avoids that gap by proving the finite Gram-coordinate realization in `EuclideanSpace`, which suffices for the stated kernel positivity theorem. |
| failed | None. |

The packet's mathematical target is met at the stated scope.  The changed
route is the finite-Gram-coordinate proof of positivity, instead of importing
or copying an optional completion wrapper from the source workspace.  It adds
no premises and neither weakens the algebraic target nor supplies a
completion.

## Plan alignment

- **Package and lane:** P57A, Lane `shared` — correct.
- **Predecessors:** none — correct.  The module is self-contained and imports
  only Mathlib; it uses no package result that was merely remotely finished.
- **Permitted gate:** discharged: it supplies a proved finite-support
  vacuum-restricted algebraic ITP kernel and pre-inner-product core, so P57
  need not recreate that algebraic layer.
- **Forbidden downstream claims:** respected.  The module has no quotient or
  completion, no completed infinite tensor-product Hilbert space, no
  pure/mixed GNS tensor splitting, no spatial von Neumann tensor product, no
  factor classification, and no manuscript state identity.

## Verification

- `lake build AristotleCandidates.VacuumRestrictedInfiniteTensorProduct` —
  passed in the already-built live project (8026 jobs).
- `lake build AristotleCandidates.VacuumRestrictedInfiniteTensorProduct Formalization`
  — passed in the live project.
- `lake build` — passed in the live project.
- `#print axioms` for `exists_gram_coords`,
  `exists_finiteMode_realization`, `sum_prod_inner_nonneg`,
  `kern_eq_prod_of_subset`, `itpInner_nonneg`, `itpCore`,
  `itpInner_vacuumVector`, and `exists_finiteMode_realization_kern` —
  each reports only `propext`, `Classical.choice`, and `Quot.sound`.
- A forbidden-declaration scan found no `sorry`, `admit`, user
  `axiom`, `opaque`, `unsafe`, `implemented_by`, or
  `native_decide`; the only textual matches are explanatory prose.
- Direct-import audit: exactly `import Mathlib`; no external-project import.
  `git diff --check` for the integrated module passed.

## Adversarial review

No acceptance-blocking finding.  The review checked that the normalization
premise is used to justify only padding outside the finite active set, that
positivity reduces the complete finite Finsupp support to an actual finite
coordinate norm square, and that the `PreInnerProductSpace.Core` receives
the real-part nonnegativity required by its interface.  It also checked the
empty-active-set vacuum calculation separately, so its norm-square-one
statement is not being promoted to a general product-padding theorem without
`hΩ`.  Builds and axiom reports validate the formal declarations, but do
not create the intentionally omitted quotient, completion, GNS, or spatial
operator-algebra results.

## Cleanup and worktree state

Kept intentionally: the integrated P57A candidate, this closeout review, the
exact raw archive, and its quarantine extraction.  The repository already had
the listed modified plan/task files and untracked earlier candidates/reviews;
they were not overwritten or otherwise changed.  No commit, push, archive
build, dependency update, dependency fetch, or manuscript modification was
performed.
