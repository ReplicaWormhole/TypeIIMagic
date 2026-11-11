# P50 recovery review — normal faithful corner trace

## Decision

**Status: accepted after task-specific artifact recovery and a checked normality correction; queue may advance.**

The automated rerun closeout reviewed the package-level archive from the first
rejected P50 task rather than the result of retry task
`292ec9c3-b24f-40ea-958e-835d0bae4379`. The rejected closeouts remain preserved
in `reviews/P50-normal-faithful-corner-trace-closeout.md` and
`reviews/P50-normal-faithful-corner-trace-closeout-rerun.md`.

The actual retry project `d5eadb4d-3341-4f40-9129-85989734737e` was downloaded
separately to the ignored raw archive
`aristotle_responses/P50-normal-faithful-corner-trace-rerun-d5eadb4d.tar.gz`
(SHA-256 `72d1539f561204a4eaa28602c5759306ef2e973a3f1e2053c5fc3c69dde77e64`)
and extracted without building or fetching dependencies into the task-specific
quarantine directory `aristotle_responses/P50-rerun-d5eadb4d-quarantine/`.
Its candidate `NormalFaithfulCornerTrace.lean` had SHA-256
`cd61f079c7978bfb3bf5061e7b088522c7dc4620870cb9829df1dc44210e8a8d`.

Unlike the stale first result, the actual retry defines the exported theorem
`normal_faithful_corner_trace`, whose assumptions include P49's
`CompatibleFiniteCodespaceSystem`, decreasing projection tower, and norm-density
input. It invokes `D.finite_corner_trace` directly and does not expose a supplied
`CornerTracialOn`, bicommutant theorem, or Kaplansky-density interface.

## Normality correction

The retry candidate originally stored only strong-operator continuity in the
field named `normal`. SOT continuity by itself is not the correct formal
encoding of ultraweak normality. Before integration, the module was corrected
to prove `cornerTau_continuous_wot`: the compressed vector functional is
continuous for the weak operator topology. The `normal` field of
`IsFaithfulNormalTracialCorner` now stores this WOT-continuity theorem. This is
strong enough for the manuscript's normality claim because the functional is
an ambient vector functional and every WOT-continuous linear functional is
ultraweakly continuous.

The final integrated candidate has SHA-256
`2e9f93915721cf61978bd718ff972c3d0c26c8662efdc03fe7b91b65a627def2`.
The packet and candidate source basis is corrected to the exact manuscript
range `main.tex:1265-1417`, covering both the normal-trace and faithfulness
proofs through the closing `\end{proof}`.

## Exact declarations and assumptions

The integrated module proves:

- `cornerTau_continuous_wot`, plus strong-net and strong-partial-sum continuity;
- `cornerTracialOn_bicommutant` and
  `cornerTracialOn_vonNeumannGenerated`, using P49C's bounded compressed nets;
- `cornerTau_faithful`, using traciality, the commuting complementary algebra,
  and the dense span of vectors `b a Omega`;
- `IsFaithfulNormalTracialCorner`, packaging projection membership,
  normalization, positivity, traciality, WOT normality, and corner faithfulness;
- `normal_faithful_corner_trace`, deriving C-star traciality from
  `D.finite_corner_trace` and returning the packaged faithful normal finite
  tracial state on the corner; and
- `sanity_isFaithfulNormalTracialCorner`, showing the exported hypotheses are
  jointly satisfiable.

The remaining explicit premises are the P49 finite codespace system, its
decreasing projection tower, a norm-closed represented star algebra containing
the finite stages and contained in their norm closure, a commuting
complementary operator set, and density of the corresponding GNS vectors. No
global trace or weight, fullness, projection finiteness, central-summand, or
type-III conclusion is assumed or asserted.

## Verification

- `lake build AristotleCandidates.NormalFaithfulCornerTrace` — passed.
- `lake env lean /tmp/P50AxiomAudit.lean` — passed; the exported theorem,
  WOT-continuity theorem, faithfulness theorem, and corner traciality theorem
  depend only on `propext`, `Classical.choice`, and `Quot.sound`; the temporary
  audit file was removed.
- `lake build` — passed for the full live project.
- Placeholder/forbidden-declaration scan — no executable `sorry`, `admit`, user
  `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration.
- Source and theorem scan confirms the `main.tex:1265-1417` locator,
  `D.finite_corner_trace` invocation, and WOT-valued `normal` field.
- `git diff --check` — passed.

## Plan alignment

- **Package and lane:** P50, Lane G — correct.
- **Predecessors:** P49 and P49C are accepted and compiled. The exported theorem
  uses both rather than replacing either with a structure field.
- **Gate:** faithful normal finite tracial state on the von Neumann corner —
  discharged conditionally on the exact finite-system, represented-algebra,
  complement-commutation, and dense-vector premises listed above.
- **Forbidden downstream claims:** respected. P51 still owns finiteness of `q`,
  fullness, central finite projections, and type-III exclusion.

## Adversarial review

No acceptance-blocking finding remains. The review explicitly checked the
topology direction in the normality claim, the load-bearing P49 theorem call,
the P49C bounded-net use, the dense-set faithfulness route, and the separation
from P51. Compilation does not discharge the remaining manuscript-specific
premises; the theorem is conditional on them exactly as stated.

AUTOPILOT_ACCEPTED: yes

AUTOPILOT_DECISION: advance
