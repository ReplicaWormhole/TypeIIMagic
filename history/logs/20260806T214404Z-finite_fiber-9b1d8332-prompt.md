# Automated Aristotle closeout

You are performing one bounded closeout for the prepared formalization queue.
Do not choose a new mathematical task and do not submit another Aristotle job;
the local supervisor submits the next prepared packet after your accepted
closeout.

Project lane: `finite_fiber`
Project root: `lean/finite_fibers`
Prepared packet: `lean/finite_fibers/aristotle_tasks/FF20-stabilizer-support-corner-instantiation.md`
Aristotle project: `b0b53374-0964-4fa5-a74d-4b624e2de8c0`
Aristotle task: `9b1d8332-6eaa-43ca-a8fd-573b508c6597`
Terminal status: `COMPLETE`
Task-status log: `history/logs/20260806T214404Z-b0b53374-tasks.log`

Aristotle task output:

```text
ID                                   CREATED              NAME                           STATUS         
---------------------------------------------------------------------------------------------------------
9b1d8332-6eaa-43ca-a8fd-573b508c6597 20 mins ago          # Autonomous proof-developm... COMPLETE
```

Required actions:

1. Read the target project's local `AGENTS.md`, packet instructions, and
   current handoff/status files. Check `git status --short` and preserve all
   unrelated dirty work.
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
   mathematical target is actually met.
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
