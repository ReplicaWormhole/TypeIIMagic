# FF19 — quasilocal state and GNS interface for the actual local system

Read `manuscript/main.tex`, including the state and local/global GNS discussion.
Work only in `formalization_finite_fibers`.

Create only `FiniteFiber/QuasilocalStateGNSInterface.lean`. Starting from the
FF18 directed finite local system, formulate the smallest explicit interface
needed to use a concrete C-star completion and a continuous extension of the
compatible stabilizer functionals. Prove all algebraic direct-limit and
finite-stage evaluation facts available locally, and connect an explicitly
supplied C-star state to Mathlib GNS using the existing generic GNS bridge.

The C-star completion, continuity bound, and global state extension must remain
explicit inputs unless constructed from checked data. Do not assert a product
GNS factorization, normality, or a type classification. No axioms/placeholders.

Acceptance: `lake build FiniteFiber.QuasilocalStateGNSInterface` succeeds and
the conditional C-star/GNS inputs are enumerated exactly.
