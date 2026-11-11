# FF23 — finite-range stabilizers have no type-III central summand

Read `manuscript/main.tex` and integrate only the checked results from
FF20--FF22.  Create only `FiniteFiber/FiniteRangeNoTypeIII.lean`.

State and prove the final general theorem in its robust central-summand form:
for the GNS von Neumann algebra of the supplied consistent finite-range
stabilizer system, every nonzero central projection `z` has `z M` containing a
nonzero finite projection.  Derive it by applying the already checked
support-corner theorem to the concrete corner obtained in FF21--FF22.

Do not use direct-integral language unless the requisite separability and
central-decomposition API is actually available.  Instead, add a clearly
labelled prose corollary that this central-summand statement excludes type-III
factors in a standard central decomposition under the usual decomposition
hypotheses.  If FF21--FF22 leave premises conditional, preserve those exact
premises in the final theorem; do not call the unconditional finite-range
theorem proved.

No `sorry`, `admit`, axioms, `opaque`, `unsafe`, or `native_decide`.  Return
the candidate file and exact Lean build result, distinguishing an unconditional
recovered theorem from a conditional theorem contract.
