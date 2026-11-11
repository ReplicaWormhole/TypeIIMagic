# P50 closeout rerun — normal faithful corner trace

## Decision

**Status: blocked; queue must halt.**

This rerun reviewed Aristotle task `292ec9c3-b24f-40ea-958e-835d0bae4379`
after its terminal `COMPLETE` status.  Its raw archive is already preserved as
`aristotle_responses/P50-normal-faithful-corner-trace.tar.gz` (SHA-256
`fd0d1163a25c0bce9299ee47729242662841def85d792242da1714dfd2839a31`) and
its dependency-free quarantine extraction as
`aristotle_responses/P50-quarantine/aristotle-stabilizer_two_lane_p50-n98s99xk_aristotle/`.
The archive was not built, updated, or used for dependency fetching.  The only
packet-authorized candidate is its
`AristotleCandidates/NormalFaithfulCornerTrace.lean` (SHA-256
`9b07496376b9a264645b9b1d8643e3710b0b9f3f85cc11a40109a1ffaaa713a9`).  It
remains unintegrated.

The mandatory predecessor P49 is not locally accepted or integrated.  The
authoritative P49 closeout records `partial; queue must halt` because its
source locator omitted the finite-stage claims it used.  The untracked live
`AristotleCandidates/FiniteCornerTrace.lean` is therefore not an integrated
predecessor merely because it compiles.  P49C is integrated and locally
audited, but it cannot substitute for P49.

Independently, the candidate fails P50's stated acceptance criterion: its
`CornerData` has the load-bearing field
`cstar_tracial : CornerTracialOn q Ω (A : Set (H →L[ℂ] H))`.  The exported
`FaithfulCornerData.isFaithfulNormalTracialState` is consequently conditional
on supplied C-star cyclicity rather than deriving it by instantiating
`CompatibleFiniteCodespaceSystem.finite_corner_trace`, as the packet requires.
Its import of `FiniteCornerTrace` supplies the predicate name but does not
discharge this premise.  Thus the candidate silently weakens the requested
route even though its abstract conditional bridge type-checks.

The current packet's source basis, `main.tex:1265-1416`, does cover the normal
trace argument and faithfulness proof.  However, the candidate's own header
and main-theorem documentation still cite `main.tex:1336-1455`, which excludes
the traciality passage at lines 1265-1314.  That stale attribution is a second
source-authority defect in the candidate, though not the first acceptance
blocker.

## Exact declarations and assumptions

The candidate declares `CornerData`, `FaithfulCornerData`, and
`IsFaithfulNormalTracialStateOnCorner`.  Its relevant results are:

- `CornerData.cornerTracialOn_vonNeumann`, conditional extension of supplied
  C-star cyclicity through P49C bounded compressed approximation;
- `CornerData.tau_tendsto_of_wotTendsto` and `tau_continuous_wot`, vector
  functional continuity; and
- `FaithfulCornerData.faithful` and
  `FaithfulCornerData.isFaithfulNormalTracialState`, conditional dense-set
  faithfulness and the packaged corner-state conclusion.

Besides complete complex Hilbert-space data, it assumes a norm-closed unital
represented star subalgebra, a self-adjoint idempotent `q` in its bicommutant,
a unit vector fixed by `q`, the supplied `cstar_tracial` premise, a commuting
complementary operator set, and density of the span of `a (b Ω)`.  It does not
add a global trace or weight, and P49C's Kaplansky theorem is used rather than
supplied.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | The quarantined candidate type-checks under the already-built live Lean environment; `FiniteCornerTrace` and `KaplanskyDensity` also build live.  The candidate source has no executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration. |
| partial | Under its explicit `cstar_tracial`, complement-commutation, and density assumptions, it gives an abstract normal/tracial/faithful vector-functional bridge. |
| blocked | P49 is not an accepted integrated predecessor, and the candidate replaces its required theorem with a supplied field. |
| failed | The packet's mathematical target is not met at its stated scope: the exported P50 theorem does not instantiate P49's `finite_corner_trace` and thus does not prove C-star cyclicity from the required finite-codespace system and density input. |

## Plan alignment

- **Package and lane:** P50, Lane G — correct.
- **Predecessors:** P49 and P49C are declared.  P49C is integrated; P49 is
  rejected/unintegrated.  The declared dependency condition is not satisfied.
- **Permitted gate:** the candidate otherwise addresses only corner
  traciality, vector-functional normality, and conditional faithfulness.
- **Forbidden claims:** no fullness, central-summand conclusion, global
  trace/weight, or type-III exclusion was found.  It does not discharge any
  later gate.

## Verification and cleanup

Run from the live project only:

```text
lake env lean aristotle_responses/P50-quarantine/.../NormalFaithfulCornerTrace.lean
lake build AristotleCandidates.FiniteCornerTrace AristotleCandidates.KaplanskyDensity
```

Both commands succeeded.  No build, update, or dependency fetch was run in
the quarantine snapshot.  No candidate was integrated, no manuscript file was
modified, and no commit, push, or new Aristotle submission occurred.  The
pre-existing dirty packet, candidate, and review files remain preserved.

## Adversarial review

Artifact types: math, source-backed, workflow.  The first fatal mathematical
gap is the supplied `cstar_tracial` premise in place of the mandated P49
instantiation; it is independent of compilation.  The review also found the
candidate's stale source locator.  No scope expansion or forbidden downstream
claim was found.  Residual risk: this closeout does not certify the candidate's
conditional operator-algebra argument as a manuscript theorem, because its
load-bearing P49 hypothesis is not established at the packet scope.
