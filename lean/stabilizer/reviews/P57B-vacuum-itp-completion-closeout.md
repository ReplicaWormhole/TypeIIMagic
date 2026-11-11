# P57B closeout review — vacuum-restricted ITP completion

## Decision

**Status: proved at the stated shared-infrastructure scope; queue may
advance.**

The exact supervisor-supplied archive
`aristotle_responses/P57B-vacuum-itp-completion-a929306b-83a7dea8.tar.gz`
has SHA-256
`c4351cce619e2e7855dc75bbc95621bdc9aa36dbaeda7cafb1fc75728ba0d2fa`.
It was extracted only into
`aristotle_responses/P57B-vacuum-itp-completion-a929306b-83a7dea8-quarantine/`.
No build, dependency update, or dependency fetch was run in that quarantine
snapshot. Only the packet-authorized candidate
`AristotleCandidates/VacuumRestrictedITPCompletion.lean` was integrated into
the live project. Its live SHA-256 is identical to the quarantined candidate:

```text
c347e629ea1364f28348bac33fe1e5b72c9b8945bc7a5bdd04a0d734e32e6018
```

The live P57A predecessor matches its quarantined copy. No manuscript file was
changed.

## Exact scope, assumptions, and declarations

This is **infrastructure only**, with no manuscript assertion. All generic
declarations have exactly the P57A parameters: `[DecidableEq ι]`,
`[∀ i, NormedAddCommGroup (E i)]`, `[∀ i, InnerProductSpace ℂ (E i)]`, and
the unit-reference premise
`hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1`. No GNS, definiteness, quotient, completion,
density, operator-algebra, or trace premise is added.

The load-bearing declarations are:

- `ITPPre`, `ITPPre.instCore`, `ITPPre.instSeminormedAddCommGroup`, and
  `ITPPre.instInnerProductSpace` (lines 80--99), transporting P57A's proved
  `itpCore hΩ` to a seminormed pre-inner-product space;
- `ITPPre.norm_eq_zero_iff` (108--110), which identifies zero seminorm with
  the P57A null form;
- `ITPQuot`, `mem_nullSubmodule_iff_inner`, and `mk_eq_zero_iff_inner`
  (118, 132--140), using `SeparationQuotient` to identify exactly zero-norm
  vectors;
- `ITPHilbert` and `itpHilbert_completeSpace` (148--164), the uniform-space
  completion of that genuine normed quotient;
- `itpEmbed`, `itpEmbed_inner`, `norm_itpEmbed`, `itpEmbed_eq_iff`, and
  `itpEmbed_eq_zero_iff` (172--201), the linear map preserving the P57A form
  and identifying precisely the null vectors;
- `denseRange_itpEmbed` and `norm_itpEmbed_vacuumVector` (204--223), the
  dense algebraic image and unit vacuum; and
- `itpEmbed_nullExample_eq_zero` (313--316), a concrete nonzero algebraic
  vector that the quotient maps to zero.

The implementation relies on proved P57A positivity plus pinned-Mathlib's
`InnerProductSpace.Core.toSeminormedAddCommGroup`,
`InnerProductSpace.ofCore`, `SeparationQuotient`, and
`UniformSpace.Completion` instances/maps. Thus the null space is quotiented
before completion; the output is not merely a seminormed space relabelled as a
Hilbert space.

## Acceptance classification

| Classification | Result |
| --- | --- |
| proved | The candidate constructs the actual null-space quotient and its completion, supplies a complete normed complex inner-product structure, proves the algebraic map preserves the core form and isometric seminorm, proves dense range, and proves the vacuum has norm one. |
| partial | Nothing at P57B scope. This package deliberately does not identify the completed space with a pure GNS representation or prove any operator-algebraic classification. |
| blocked | None. The required pinned-Mathlib quotient, completion, inner-product, and density APIs were available and used constructively. |
| failed | None. |

The packet's mathematical target is met at its stated scope. The example in
`itpEmbed_nullExample_eq_zero` independently checks the essential semantic
point: the construction genuinely collapses a nonzero null vector. There is no
alternative route or added premise beyond the packet's allowed P57A data.

## Plan alignment

- **Package and lane:** P57B; Lane `shared` — correct.
- **Integrated predecessors:** P57A only — correct. Its prior closeout records
  a locally integrated and audited finite-support core; no remotely finished
  but unintegrated package is used.
- **Permitted gate:** discharged. The candidate builds the quotient/completion
  Hilbert space with dense algebraic vacuum-tensor image, rather than assuming
  a completed ITP interface.
- **Forbidden downstream claims:** respected. The candidate makes no pure-GNS
  identification, `B(K)` closure or factor claim, mixed-factor claim, spatial
  von Neumann product claim, or trace/weight statement.

## Verification

- `lake build AristotleCandidates.VacuumRestrictedITPCompletion` — passed
  (`8027/8027` jobs) in the live project.
- `lake build AristotleCandidates.VacuumRestrictedInfiniteTensorProduct AristotleCandidates.VacuumRestrictedITPCompletion Formalization` — passed
  (`8088` jobs) in the live project.
- `lake build` — passed (already up to date) in the live project.
- `lake env lean /tmp/p57b_axioms.lean` printing axioms for
  `sqrt_re_eq_zero_iff`, `ITPPre.norm_eq_zero_iff`,
  `mk_eq_zero_iff_inner`, `itpEmbed_inner`, `itpEmbed_eq_iff`,
  `denseRange_itpEmbed`, `norm_itpEmbed_vacuumVector`, and
  `itpEmbed_nullExample_eq_zero` — each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Declaration scan found no `sorry`, `admit`, user `axiom`, `opaque`,
  `unsafe`, `implemented_by`, or `native_decide`; the one scan match is a
  documentation sentence. `git diff --check` passed.
- Live/quarantine candidate SHA-256 comparison — passed exactly.

## Adversarial review

Artifact types: Lean code, mathematical formalization, and workflow closeout.
No acceptance-blocking finding. The review checked the quotient occurs before
completion, the null-vector equivalence is stated and proved through the
P57A form, dense range uses both quotient surjectivity and completion density,
the vacuum normalization still depends on the explicit `hΩ`, and the concrete
null-vector example prevents a vacuous reading of the quotient. Compilation
and axiom reports validate the formal declarations; they do not establish
the deliberately excluded GNS, factor, spatial-tensor, or trace/weight claims.

## Cleanup and worktree state

Kept intentionally: the integrated P57B candidate, exact raw archive,
quarantine extraction, and this closeout review. The modified plan, task,
decision, and other candidate/review files listed before this closeout were
pre-existing user work and were preserved. No commit, push, archive build,
dependency update, dependency fetch, or manuscript modification was performed.
