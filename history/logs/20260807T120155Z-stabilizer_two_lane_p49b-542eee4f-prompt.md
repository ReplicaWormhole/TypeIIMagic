# Automated Aristotle closeout

You are performing one bounded closeout for the prepared formalization queue.
Do not choose a new mathematical task and do not submit another Aristotle job;
the local supervisor submits the next prepared packet after your accepted
closeout.

Project lane: `shared`
Project root: `lean/stabilizer`
Prepared packet: `lean/stabilizer/aristotle_tasks/P49B-von-neumann-bicommutant-theorem.md`
Aristotle project: `eff7c737-ecb5-4359-b480-6c22e5d2b6c7`
Aristotle task: `542eee4f-550b-43ef-858a-78f8d0f8c4ef`
Terminal status: `COMPLETE`
Task-status log: `history/logs/20260807T120155Z-eff7c737-tasks.log`

Aristotle task output:

```text
ID                                   CREATED              NAME                           STATUS         
---------------------------------------------------------------------------------------------------------
542eee4f-550b-43ef-858a-78f8d0f8c4ef 46 mins ago          # Autonomous proof-developm... COMPLETE
```

Required actions:

1. Read the target project's local `AGENTS.md`, `PLAN.md`,
   `work/TWO-LANE-FORMALIZATION-DECISION.md`, packet instructions, and current
   handoff/status files. Check `git status --short` and preserve all unrelated
   dirty work. Verify that the packet names the correct lane, uses only locally
   integrated predecessors, discharges only its permitted gate, and makes none
   of its forbidden downstream claims.
2. Download the completed Aristotle project into the lane's designated
   response/quarantine area, never over the working tree. Inspect the returned
   archive and integrate only the reviewed candidate module and raw response
   records allowed by the packet. Never run `lake build`, `lake update`, or a
   dependency fetch inside the downloaded archive: it is intentionally a
   dependency-free quarantine snapshot. After inspection, run every Lean check
   in the already-built live project only.
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
