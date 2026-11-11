# Automated Aristotle closeout

You are performing one bounded closeout for the prepared formalization queue.
Do not choose a new mathematical task and do not submit another Aristotle job;
the local supervisor submits the next prepared packet after your accepted
closeout.

Project lane: `H`
Project root: `lean/stabilizer`
Prepared packet: `lean/stabilizer/aristotle_tasks/P57C-pure-gns-type-one-factor.md`
Aristotle project: `79a50549-7ae1-4e6e-840d-f0bb13d4d72b`
Aristotle task: `07e097eb-c3c0-418b-878b-ab4a45460a2b`
Terminal status: `OUT_OF_BUDGET`
Task-status log: `history/logs/20260811T085809Z-79a50549-tasks.log`
Exact response archive: `lean/stabilizer/aristotle_responses/P57C-pure-gns-type-one-factor-79a50549-07e097eb.tar.gz`
Exact quarantine directory: `lean/stabilizer/aristotle_responses/P57C-pure-gns-type-one-factor-79a50549-07e097eb-quarantine`

Aristotle task output:

```text
ID                                   CREATED              NAME                           STATUS         
---------------------------------------------------------------------------------------------------------
07e097eb-c3c0-418b-878b-ab4a45460a2b 3 hours ago          # Autonomous proof-developm... OUT_OF_BUDGET
```

Required actions:

1. Read the target project's local `AGENTS.md`, `PLAN.md`,
   `work/TWO-LANE-FORMALIZATION-DECISION.md`, packet instructions, and current
   handoff/status files. Check `git status --short` and preserve all unrelated
   dirty work. Verify that the packet names the correct lane, uses only locally
   integrated predecessors, discharges only its permitted gate, and makes none
   of its forbidden downstream claims.
2. The supervisor has already downloaded this exact task to
   `lean/stabilizer/aristotle_responses/P57C-pure-gns-type-one-factor-79a50549-07e097eb.tar.gz`. Do not use, overwrite, or infer results from any
   package-level archive belonging to an earlier task. Extract only this archive
   into `lean/stabilizer/aristotle_responses/P57C-pure-gns-type-one-factor-79a50549-07e097eb-quarantine`, never over the working tree. Integrate only the
   reviewed candidate module and raw response records allowed by the packet.
   Never run `lake build`, `lake update`, or a dependency fetch inside the
   downloaded archive: it is intentionally a dependency-free quarantine
   snapshot. After inspection, run every Lean check in the already-built live
   project only.
3. Run the packet's narrow Lean build, then the relevant broader build and
   axiom/placeholder checks. A compiling result is not by itself mathematical
   validation.
4. Write a closeout review in the project's existing review/handoff area. It
   must distinguish `proved`, `partial`, `blocked`, and `failed`, record the
   exact theorem declarations and assumptions, and state whether the packet's
   mathematical target is actually met. Include a `Plan alignment` subsection
   auditing the declared lane, predecessors, gate, and forbidden claims.
5. An alternative proof route and project-local supporting theory are allowed
   when they recover the manuscript theorem or a clearly labelled conditional
   form. Record the exact new declarations, changed route, and every added
   premise. Do not silently weaken a target.
6. Do not add an axiom/sorry/admit/opaque/unsafe declaration, overwrite
   unrelated dirty files, commit, push, or modify the manuscript.
7. If the result is blocked or partial, record the precise obstruction and do
   not pretend that the queue advanced. The supervisor will halt this lane.

At the end, print exactly one machine-readable decision line:

`AUTOPILOT_DECISION: advance`

only if the packet was integrated and verified at its stated scope. Otherwise
print:

`AUTOPILOT_DECISION: halt`

The final message must also contain `AUTOPILOT_ACCEPTED: yes` only after the
closeout review and checks are complete.
