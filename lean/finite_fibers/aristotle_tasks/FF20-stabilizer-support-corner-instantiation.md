# FF20 — instantiate the support-corner theorem from an actual stabilizer model

Read the full manuscript source and work only in `formalization_finite_fibers`.

Create only `FiniteFiber/ActualStabilizerSupportCorner.lean`. Combine the
actual finite full-Pauli local system of FF18 and the C-star/GNS interface of
FF19 with the already checked `StabilizerFiniteFiber` theorem. State a
conditional theorem whose hypotheses are exactly the remaining global facts:
the completed state/GNS representation, decreasing finite stabilizer supports,
their strong limit, dense orbit/fullness, and corner traciality. Its conclusion
must be the existing every-nonzero-central-summand finite-projection statement.

Do not claim those global hypotheses follow from the current manuscript's
short-range definition unless they have actually been constructed. Do not state
a direct-integral/type-III classification theorem. No axioms/placeholders.

Acceptance: `lake build FiniteFiber.ActualStabilizerSupportCorner` succeeds,
and the result is labelled conditional unless every listed global input is
proved in the submitted snapshot.
