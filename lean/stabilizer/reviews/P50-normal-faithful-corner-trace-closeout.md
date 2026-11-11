# P50 closeout review — normal faithful corner trace

## Decision

**Status: blocked; queue must halt.**

The completed Aristotle response was downloaded to the ignored raw-response
record `aristotle_responses/P50-normal-faithful-corner-trace.tar.gz` (SHA-256
`fd0d1163a25c0bce9299ee47729242662841def85d792242da1714dfd2839a31`) and
extracted, without a build, update, or dependency fetch, to
`aristotle_responses/P50-quarantine/aristotle-stabilizer_two_lane_p50-n98s99xk_aristotle/`.
Its sole packet-authorized candidate module is
`AristotleCandidates/NormalFaithfulCornerTrace.lean` (SHA-256
`9b07496376b9a264645b9b1d8643e3710b0b9f3f85cc11a40109a1ffaaa713a9`).  It is
not integrated into the live worktree.

P50's declared predecessor P49 is not an integrated, accepted predecessor:
the existing P49 closeout explicitly records **partial; queue must halt** and
states that `FiniteCornerTrace.lean` was not accepted because its source
locator omitted the finite-stage clauses it claimed to formalize.  The live
copy is untracked, and its SHA-256 (`12cc9185a24773f85855bfc05ee779e997bf40f05abb2823e3352932ffff7111`)
matches the response snapshot.  Matching bytes and a successful compilation do
not turn that rejected predecessor into an integrated dependency.  P49C is
integrated and its snapshot matches the live file
(`e57deb88999d442a8882f37fd4b956e7d36df5849b460dea9f5aa1c5bd1ddde4`).

Independently, the P50 candidate does not obtain C-star-level traciality from
P49.  It places
`cstar_tracial : CornerTracialOn q Ω (A : Set (H ->L[ℂ] H))` in the new
`CornerData` structure, then uses that supplied field in
`CornerData.cornerTracialOn_vonNeumann`.  The only operational P49 import is
the definition of `CornerTracialOn`; no P49 theorem discharges this premise.
This is a new load-bearing premise in place of the required P49 result, so the
candidate does not meet the packet's stated target even as a conditional P50
extension.

There is also a source-authority mismatch.  The packet's only source basis is
`main.tex:1336-1455`, whereas the candidate explicitly attributes the
traciality/normal-state passage to `main.tex:1290-1312` (the source calculation
actually appears at lines 1281-1314).  The proposed faithful-corner argument
is within the declared range at `main.tex:1355-1416`; the antecedent
traciality claim is not.  The P49 predecessor was intended to supply that
outside-range result, but it is neither accepted nor used as a theorem.

## Exact declarations and assumptions reviewed

The candidate defines `CornerData`, `FaithfulCornerData`, and the project-local
predicate `IsFaithfulNormalTracialStateOnCorner`.  Its main declarations are:

- `CornerData.cornerTracialOn_vonNeumann`, deriving cyclicity on the
  bicommutant corner from bounded Kaplansky compressed product nets and the
  supplied `cstar_tracial` field;
- `CornerData.tau_tendsto_of_wotTendsto` and
  `CornerData.tau_continuous_wot`, identifying the compressed functional with
  a vector functional and proving WOT-net continuity;
- `FaithfulCornerData.faithful`, using a supplied complementary set `B`,
  `B_commutes`, and density of the span of `a (b Ω)`;
- `FaithfulCornerData.isFaithfulNormalTracialState`, packaging positivity,
  reality on squares, normalization at `q`, traciality, WOT continuity, and
  faithfulness.

Its explicit assumptions are: a complete complex inner-product space; a
norm-closed unital represented star subalgebra `A`; a self-adjoint idempotent
`q` in `A''` fixing a unit vector `Ω`; the new C-star traciality premise
`cstar_tracial`; a complementary operator set `B` commuting with `A`; and the
density premise for vectors `a (b Ω)`.  Kaplansky density itself is invoked as
the proved P49C theorem, not supplied as a field.  No global trace or weight
is supplied.

## Acceptance review

| Classification | Result |
| --- | --- |
| proved | In the live Lean environment, the quarantined candidate type-checks.  Its three sampled load-bearing declarations report only `propext`, `Classical.choice`, and `Quot.sound`.  It contains no executable `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `implemented_by`, or `native_decide` declaration. |
| partial | Conditional on its new `cstar_tracial` field and the listed complement/density data, the file supplies a coherent abstract bridge from bounded Kaplansky product approximation to a vector-functional tracial state and a dense-set faithfulness proof.  This is not P50 at the packet's scope because the P49 output is assumed rather than imported as a proved result. |
| blocked | The mandatory P49 predecessor remains unaccepted/unintegrated, and the candidate replaces it with a new premise.  The source declaration also omits the manuscript lines the candidate explicitly invokes for traciality and normality. |
| failed | The packet's acceptance criteria fail: P50 was required to use the locally integrated P49 and P49C results to prove the stated corner trace, not to add the C-star trace as an independent interface field.  Therefore the candidate is not integrated and the queue does not advance. |

The packet's mathematical target is **not met at its stated scope**.  Successful
Lean checks establish only the candidate's explicitly conditional abstract
theorem; they do not validate a manuscript-derived faithful normal tracial
state on the intended corner.

## Plan alignment

- **Package and lane:** P50, Lane G — correctly named.
- **Predecessors:** P49 and P49C are declared.  P49C is integrated and locally
  audited.  P49 is not accepted/integrated, so the declared predecessor set is
  not satisfied; the packet is not permitted to proceed.
- **Permitted gate:** the candidate addresses only the P50 gate—corner
  traciality, vector-functional normality, and faithfulness under explicit
  representation/complement/density data.  Its abstract route does not itself
  prove the required P49 input.
- **Forbidden downstream claims:** respected by the candidate.  It makes no
  fullness, central-summand, finite-projection, global trace/weight, or final
  type-III-exclusion claim.

## Verification

- `lake env lean <P50 quarantine>/AristotleCandidates/NormalFaithfulCornerTrace.lean`
  — passed, run from the already-built live project; no Lean operation was run
  in the dependency-free quarantine snapshot.
- `lake build AristotleCandidates.FiniteCornerTrace
  AristotleCandidates.KaplanskyDensity
  AristotleCandidates.VonNeumannBicommutantTheorem
  AristotleCandidates.StrongOperatorClosedVonNeumann Formalization` — passed
  (one non-blocking style suggestion in `KaplanskyDensity.lean:463`).
- `lake build` — passed in the live project.
- `#print axioms` for `CornerData.cornerTracialOn_vonNeumann`,
  `FaithfulCornerData.faithful`, and
  `FaithfulCornerData.isFaithfulNormalTracialState` — each lists only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder/forbidden-declaration scan of the candidate and direct
  predecessors — no executable forbidden declaration; the only match is
  P49C's negative-scope documentation.
- `git diff --check` — passed.

## Adversarial review

**Acceptance-blocking findings:**

1. The file's central hypothesis `cstar_tracial` is supplied, not discharged
   by P49.  This silently changes P50 from an extension of the required P49
   proof to a theorem conditional on the missing P49 conclusion.
2. P49 is a rejected/unintegrated predecessor, despite the packet's contrary
   predecessor declaration.  A local untracked copy and a passing build cannot
   repair this plan-alignment defect.
3. The candidate makes manuscript-facing traciality/normality attributions to
   `main.tex:1290-1312`, outside the packet's declared `main.tex:1336-1455`
   basis.

No additional Lean-term defect, forbidden downstream theorem, or archive
handling violation was found.  The raw archive and quarantine extraction are
kept intentionally as ignored response records.  All pre-existing dirty and
untracked work, including the unaccepted P49 copy and its reviews, was
preserved unchanged.  No manuscript file, commit, push, remote submission,
dependency update, archive build, or dependency fetch occurred.
